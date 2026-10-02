-- Prove2me | Definitions.Def_HunterPDE_Elliptic_EllipticOperator
-- name    : HunterPDE_Elliptic_EllipticOperator
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T23:41:47.917989+00:00
-- url     : https://prove2.me/theorems/4bcfddfb-8d5b-4786-966f-d64beef1709d
-- title:
--   Divergence-form operators (4.16)–(4.18), bilinear forms (4.20)–(4.21), weak solutions (Def. 4.19) and the resolvent (4.26)–(4.27)
-- statement:
--   Let $\Omega \subseteq \mathbb{R}^n$ be open. A second-order operator in divergence form is
--   $$Lu = -\sum_{i,j=1}^n \partial_i(a_{ij}\partial_j u) + \sum_{i=1}^n \partial_i(b_i u) + cu \qquad (4.16)$$
--   with coefficients satisfying $a_{ij}, b_i, c \in L^\infty(\Omega)$ and $a_{ij} = a_{ji}$ (4.17). It is **uniformly elliptic** (Definition 4.16) if there is $\theta > 0$ with $\sum_{i,j} a_{ij}(x)\xi_i\xi_j \ge \theta|\xi|^2$ for almost every $x \in \Omega$ and every $\xi \in \mathbb{R}^n$ (4.18).
--
--   The bilinear form of $L$ on $H^1_0(\Omega)$ is
--   $$a(u,v) = \int_\Omega \Big(\sum_{i,j} a_{ij}\,\partial_i u\,\partial_j v - \sum_i b_i\,u\,\partial_i v + c\,uv\Big)dx, \qquad (4.20)$$
--   and that of the formal adjoint $L^*u = -\sum_{i,j}\partial_i(a_{ij}\partial_j u) - \sum_i b_i\partial_i u + cu$ (4.22) is $a^*(u,v) = a(v,u) = \int_\Omega \big(\sum a_{ij}\partial_i u\,\partial_j v - \sum b_i(\partial_i u)v + cuv\big)dx$.
--
--   For $\mu \in \mathbb{R}$ and a right-hand side $f$ acting on $H^1_0(\Omega)$, $u$ is a **weak solution** of $Lu + \mu u = f$, $u = 0$ on $\partial\Omega$ (Definition 4.19) if $u \in H^1_0(\Omega)$ and $a(u,\phi) + \mu(u,\phi)_{L^2} = \langle f, \phi\rangle$ for all $\phi \in H^1_0(\Omega)$. A function $f \in L^2(\Omega)$ acts by $\langle f,\phi\rangle = \int_\Omega f\phi\,dx$. The **resolvent** $K = (L+\mu I)^{-1}|_{L^2(\Omega)}$ is defined by $Kf = u$ iff $a(u,v) + \mu(u,v)_{L^2} = (f,v)_{L^2}$ for all $v \in H^1_0(\Omega)$ (4.26), and $K^*$ likewise with $a^*$ (4.27).
--
--   **Formalization Note.** Coordinates are 0-based. `Coeffs n` bundles $a_{ij}, b_i, c$; `Admissible` is (4.17) with $L^\infty$ taken on $\Omega$ and symmetry almost everywhere; `UniformlyEllipticWith Ω θ` includes $\theta > 0$. `IsWeakSolution B μ F u` takes the bilinear form `B` (`form P` for $L$, `formAdj P` for $L^*$) and the action `F` of the right-hand side, so $L^*v + \mu v = 0$ uses `formAdj P` and `F = 0`. `solutionSpace B μ` is the subspace of weak solutions of the homogeneous problem. `resolvent Ω P μ f` is the unique weak solution when one exists (for $\mu \ge \gamma$, Theorem 4.22) and $0$ otherwise. **Sign correction:** the page's display (4.21) prints $+\sum_i b_i(\partial_i u)v$, which contradicts both $a^*(u,v) = a(v,u)$ (stated on p. 102) and (4.22); `formAdj` uses the sign those fix.
-- source:
--   Hunter, Notes on Partial Differential Equations (revised 6/18/2014), pp. 101–106, Eqs. (4.16)–(4.18), (4.20)–(4.22), (4.26)–(4.27), Definitions 4.16, 4.19

import Mathlib
import Definitions.Def_HunterPDE_Elliptic_H10

namespace HunterPDE.Elliptic

open MeasureTheory

/-- The coefficient functions of a second-order operator in divergence form (Hunter (4.16)),
`L u = -∑ᵢⱼ ∂ᵢ(aᵢⱼ ∂ⱼu) + ∑ᵢ ∂ᵢ(bᵢ u) + c u`, on `ℝⁿ`; indices are 0-based (`Fin n`). -/
structure Coeffs (n : ℕ) where
  /-- The principal coefficients `aᵢⱼ`. -/
  a : Fin n → Fin n → EuclideanSpace ℝ (Fin n) → ℝ
  /-- The first-order coefficients `bᵢ`. -/
  b : Fin n → EuclideanSpace ℝ (Fin n) → ℝ
  /-- The zeroth-order coefficient `c`. -/
  c : EuclideanSpace ℝ (Fin n) → ℝ

/-- The standing assumption (4.17): `aᵢⱼ, bᵢ, c ∈ L^∞(Ω)` and `aᵢⱼ = aⱼᵢ` (as elements of
`L^∞(Ω)`, i.e. almost everywhere in `Ω`). -/
def Coeffs.Admissible {n : ℕ} (P : Coeffs n) (Ω : Set (EuclideanSpace ℝ (Fin n))) : Prop :=
  (∀ i j, MemLp (P.a i j) ⊤ (volume.restrict Ω)) ∧ (∀ i, MemLp (P.b i) ⊤ (volume.restrict Ω)) ∧
    MemLp P.c ⊤ (volume.restrict Ω) ∧ ∀ i j, P.a i j =ᵐ[volume.restrict Ω] P.a j i

/-- Uniform ellipticity with constant `θ` (Definition 4.16, (4.18)): `θ > 0` and
`∑ᵢⱼ aᵢⱼ(x) ξᵢ ξⱼ ≥ θ |ξ|²` for almost every `x ∈ Ω` and every `ξ ∈ ℝⁿ`. -/
def Coeffs.UniformlyEllipticWith {n : ℕ} (P : Coeffs n) (Ω : Set (EuclideanSpace ℝ (Fin n)))
    (θ : ℝ) : Prop :=
  0 < θ ∧ ∀ᵐ x ∂(volume.restrict Ω), ∀ ξ : Fin n → ℝ,
    θ * ∑ i, ξ i ^ 2 ≤ ∑ i, ∑ j, P.a i j x * ξ i * ξ j

/-- `L` is uniformly elliptic on `Ω` (Definition 4.16): (4.18) holds for some constant `θ > 0`. -/
def Coeffs.UniformlyElliptic {n : ℕ} (P : Coeffs n) (Ω : Set (EuclideanSpace ℝ (Fin n))) :
    Prop :=
  ∃ θ : ℝ, P.UniformlyEllipticWith Ω θ

/-- The bilinear form (4.20) of `L` on `H¹₀(Ω)`:
`a(u, v) = ∫_Ω (∑ᵢⱼ aᵢⱼ ∂ᵢu ∂ⱼv − ∑ᵢ bᵢ u ∂ᵢv + c u v) dx`. -/
noncomputable def form {n : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin n))} (P : Coeffs n)
    (u v : H10 n Ω) : ℝ :=
  ∫ x in Ω, ((∑ i, ∑ j, P.a i j x * pd u i x * pd v j x) - (∑ i, P.b i x * val u x * pd v i x)
    + P.c x * val u x * val v x)

/-- The bilinear form of the formal adjoint `L* u = -∑ᵢⱼ ∂ᵢ(aᵢⱼ ∂ⱼu) − ∑ᵢ bᵢ ∂ᵢu + c u` of (4.22):
`a*(u, v) = ∫_Ω (∑ᵢⱼ aᵢⱼ ∂ᵢu ∂ⱼv − ∑ᵢ bᵢ (∂ᵢu) v + c u v) dx`, so that `a*(u, v) = a(v, u)`
(p. 102, using `aᵢⱼ = aⱼᵢ`). The page's display (4.21) prints `+ ∑ᵢ bᵢ (∂ᵢu) v`, which contradicts
both `a*(u, v) = a(v, u)` and (4.22); the sign here is the one those two fix. -/
noncomputable def formAdj {n : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin n))} (P : Coeffs n)
    (u v : H10 n Ω) : ℝ :=
  ∫ x in Ω, ((∑ i, ∑ j, P.a i j x * pd u i x * pd v j x) - (∑ i, P.b i x * pd u i x * val v x)
    + P.c x * val u x * val v x)

/-- Weak solution (Definition 4.19) of `M u + μ u = F`, `u = 0` on `∂Ω`, for the operator `M`
whose bilinear form on `H¹₀(Ω)` is `B` (`B = form P` for `L`, `B = formAdj P` for `L*`):
`u ∈ H¹₀(Ω)` and `B(u, φ) + μ (u, φ)_{L²} = ⟨F, φ⟩` for all `φ ∈ H¹₀(Ω)`. The right-hand side
is given by its action `F : H¹₀(Ω) → ℝ`: for `f ∈ H⁻¹(Ω)` it is `⇑f`, for `f ∈ L²(Ω)` it is
`φ ↦ ∫_Ω f φ dx` (the identification of Definition 4.1). -/
def IsWeakSolution {n : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin n))} (B : H10 n Ω → H10 n Ω → ℝ)
    (μ : ℝ) (F : H10 n Ω → ℝ) (u : H10 n Ω) : Prop :=
  ∀ φ : H10 n Ω, B u φ + μ * l2inner u φ = F φ

/-- The action `φ ↦ (f, φ)_{L²} = ∫_Ω f φ dx` on `H¹₀(Ω)` of `f ∈ L²(Ω)` (Definition 4.1). -/
noncomputable def l2pairing {n : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin n))}
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (φ : H10 n Ω) : ℝ :=
  ∫ x in Ω, f x * val φ x

/-- The solution space in `H¹₀(Ω)` of the homogeneous problem `M u + μ u = 0` (bilinear form `B`),
as a subspace of `H¹₀(Ω)`: the span of the set of weak solutions (which is already a linear
subspace, so the span adds nothing). -/
noncomputable def solutionSpace {n : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin n))}
    (B : H10 n Ω → H10 n Ω → ℝ) (μ : ℝ) : Submodule ℝ (H10 n Ω) :=
  Submodule.span ℝ {u | IsWeakSolution B μ (fun _ => 0) u}

open Classical in
/-- The resolvent `K = (L + μI)⁻¹|_{L²(Ω)}` of (4.26): `K f = u` iff `u ∈ H¹₀(Ω)` and
`a_μ(u, v) = a(u, v) + μ (u, v)_{L²} = (f, v)_{L²}` for all `v ∈ H¹₀(Ω)`, regarded in `L²(Ω)`.
Where no such `u` exists (not the case for `μ ≥ γ`, Theorem 4.22) the value is `0`. -/
noncomputable def resolvent {n : ℕ} (Ω : Set (EuclideanSpace ℝ (Fin n))) (P : Coeffs n) (μ : ℝ)
    (f : Lp ℝ 2 (volume.restrict Ω)) : Lp ℝ 2 (volume.restrict Ω) :=
  if h : ∃ u : H10 n Ω, IsWeakSolution (form P) μ (l2pairing (f : EuclideanSpace ℝ (Fin n) → ℝ)) u
  then toL2 h.choose else 0

open Classical in
/-- The operator `K* = (L* + μI)⁻¹|_{L²(Ω)}` of (4.27): `K* f = u` iff `u ∈ H¹₀(Ω)` and
`a*_μ(u, v) = a*(u, v) + μ (u, v)_{L²} = (f, v)_{L²}` for all `v ∈ H¹₀(Ω)`. -/
noncomputable def resolventAdj {n : ℕ} (Ω : Set (EuclideanSpace ℝ (Fin n))) (P : Coeffs n)
    (μ : ℝ) (f : Lp ℝ 2 (volume.restrict Ω)) : Lp ℝ 2 (volume.restrict Ω) :=
  if h : ∃ u : H10 n Ω,
      IsWeakSolution (formAdj P) μ (l2pairing (f : EuclideanSpace ℝ (Fin n) → ℝ)) u
  then toL2 h.choose else 0

end HunterPDE.Elliptic


