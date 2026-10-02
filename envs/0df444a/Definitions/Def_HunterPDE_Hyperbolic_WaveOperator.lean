-- Prove2me | Definitions.Def_HunterPDE_Hyperbolic_WaveOperator
-- name    : HunterPDE_Hyperbolic_WaveOperator
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T00:30:51.396195+00:00
-- url     : https://prove2.me/theorems/9b46964b-e2d2-41f0-bdce-cb602ec2933d
-- title:
--   Assumption 7.1, the bilinear form (7.6) and weak solutions of the hyperbolic IBVP (Definition 7.2)
-- statement:
--   Let $\Omega \subset \mathbb{R}^n$ be open and $T > 0$. The operator is $Lu = -\sum_{i,j=1}^n \partial_i\big(a^{ij}(x,t)\partial_j u\big) + c(x,t)u$ (7.4), with bilinear form on $H^1_0(\Omega)$
--   $$a(u,v;t) = \sum_{i,j=1}^n \int_\Omega a^{ij}(x,t)\,\partial_i u\,\partial_j v\,dx + \int_\Omega c(x,t)\,u v\,dx \qquad (7.6),$$
--   and $a_t(u,v;t)$ is the same form with $a^{ij}, c$ replaced by their time derivatives $a^{ij}_t, c_t$.
--
--   **Assumption 7.1**: $\Omega$ is bounded and open, $T>0$; $a^{ij}, c \in L^\infty(\Omega\times(0,T))$ and their weak time derivatives $a^{ij}_t, c_t$ exist and belong to $L^\infty(\Omega\times(0,T))$; $a^{ij} = a^{ji}$; and for some $\theta > 0$, $\sum_{i,j} a^{ij}(x,t)\xi_i\xi_j \ge \theta|\xi|^2$ for all $(x,t)$ and $\xi \in \mathbb{R}^n$ (6.6).
--
--   **Definition 7.2.** Given $f : [0,T] \to L^2(\Omega)$, $g \in H^1_0(\Omega)$, $h \in L^2(\Omega)$, a function $u : [0,T] \to H^1_0(\Omega)$ is a **weak solution** of $u_{tt} + Lu = f$ in $\Omega\times(0,T)$, $u = 0$ on $\partial\Omega\times(0,T)$, $u = g$, $u_t = h$ at $t=0$ (7.5), if (1) $u$ has weak derivatives $u_t$ and $u_{tt}$ with $u \in C([0,T];H^1_0(\Omega))$, $u_t \in C([0,T];L^2(\Omega))$, $u_{tt} \in L^2(0,T;H^{-1}(\Omega))$; (2) for every $v \in H^1_0(\Omega)$,
--   $$\langle u_{tt}(t), v\rangle + a(u(t), v; t) = (f(t), v)_{L^2} \quad \text{for a.e. } t \in [0,T] \qquad (7.8);$$
--   (3) $u(0) = g$ and $u_t(0) = h$.
--
--   **Formalization Note.** Coefficients are functions of $(x,t) \in \mathbb{R}^n\times\mathbb{R}$ bundled in `Coeffs n` together with $a^{ij}_t, c_t$; `Assumption71` requires the latter to be the weak time derivatives of the former on $\Omega\times(0,T)$. Since the coefficients are $L^\infty$ classes, symmetry and ellipticity are required almost everywhere in $\Omega\times(0,T)$. Part (3) of Assumption 7.1 (the data) is a hypothesis of each theorem. The weak derivative $u_t$ is that of $u$ regarded in $L^2(\Omega)$, and $u_{tt}$ that of $u_t$ regarded in $H^{-1}(\Omega)$. The page prints $\partial_j u$ in the first integral of (7.6); $a(u,v;t) = (Lu,v)_{L^2}$ and the symmetry asserted after Assumption 7.1 fix it as $\partial_j v$. The consequences (7.7) of Assumption 7.1 (coercivity and boundedness of $a$, $a_t$) are not assumed.
-- source:
--   Hunter, Notes on Partial Differential Equations (revised 6/18/2014), pp. 212–213, Eqs. (6.6), (7.4)–(7.6), Assumption 7.1, Definition 7.2

import Mathlib
import Definitions.Def_HunterPDE_Hyperbolic_H10
import Definitions.Def_HunterPDE_Hyperbolic_WeakTimeDeriv

namespace HunterPDE.Hyperbolic

open MeasureTheory Set
open scoped ContDiff

/-- The coefficients of the time-dependent operator (7.4),
`L u = −∑ᵢⱼ ∂ᵢ(aᵢⱼ(x, t) ∂ⱼu) + c(x, t) u` on `Ω × (0, T)`, as functions of `(x, t) ∈ ℝⁿ × ℝ`,
together with the functions `aᵢⱼ_t`, `c_t` that Assumption 7.1 requires to be their time
derivatives. Indices are 0-based (`Fin n`). -/
structure Coeffs (n : ℕ) where
  /-- The principal coefficients `aᵢⱼ(x, t)`. -/
  a : Fin n → Fin n → EuclideanSpace ℝ (Fin n) × ℝ → ℝ
  /-- The zeroth-order coefficient `c(x, t)`. -/
  c : EuclideanSpace ℝ (Fin n) × ℝ → ℝ
  /-- The time derivatives `(aᵢⱼ)_t(x, t)`. -/
  a_t : Fin n → Fin n → EuclideanSpace ℝ (Fin n) × ℝ → ℝ
  /-- The time derivative `c_t(x, t)`. -/
  c_t : EuclideanSpace ℝ (Fin n) × ℝ → ℝ

/-- `F'` is the weak time derivative `∂_t F` of `F` on the space-time cylinder `Ω × (0, T)`:
`F, F'` are locally integrable there and `∫∫ F ∂_t φ = −∫∫ F' φ` for every smooth `φ` with compact
support in `Ω × (0, T)`, where `∂_t φ(x, t) = Dφ(x, t)(0, 1)`. -/
def HasWeakTimeDerivOnCylinder {n : ℕ} (Ω : Set (EuclideanSpace ℝ (Fin n))) (T : ℝ)
    (F F' : EuclideanSpace ℝ (Fin n) × ℝ → ℝ) : Prop :=
  LocallyIntegrableOn F (Ω ×ˢ Ioo 0 T) ∧ LocallyIntegrableOn F' (Ω ×ˢ Ioo 0 T) ∧
    ∀ φ : EuclideanSpace ℝ (Fin n) × ℝ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      tsupport φ ⊆ Ω ×ˢ Ioo 0 T →
        ∫ p in Ω ×ˢ Ioo 0 T, F p * fderiv ℝ φ p (0, 1) = -∫ p in Ω ×ˢ Ioo 0 T, F' p * φ p

/-- Assumption 7.1 (Hunter, p. 213), parts (1)–(2), with the standing hypotheses on `Ω` and `T`:
`Ω ⊂ ℝⁿ` is bounded and open, `T > 0`;
(1) `aᵢⱼ, c ∈ L^∞(Ω × (0, T))` and their weak time derivatives `aᵢⱼ_t, c_t` exist and lie in
`L^∞(Ω × (0, T))`;
(2) `aᵢⱼ = aⱼᵢ` and the uniform ellipticity condition (6.6)
`∑ᵢⱼ aᵢⱼ(x, t) ξᵢ ξⱼ ≥ θ |ξ|²` holds for some `θ > 0`.
Both (2) and the symmetry are imposed almost everywhere in `Ω × (0, T)`, since the coefficients
are `L^∞` classes. Part (3) (the data `f, g, h`) is stated as hypotheses of each theorem. -/
def Assumption71 {n : ℕ} (Ω : Set (EuclideanSpace ℝ (Fin n))) (T : ℝ) (P : Coeffs n) :
    Prop :=
  IsOpen Ω ∧ Bornology.IsBounded Ω ∧ 0 < T ∧
    (∀ i j, MemLp (P.a i j) ⊤ (volume.restrict (Ω ×ˢ Ioo 0 T))) ∧
    MemLp P.c ⊤ (volume.restrict (Ω ×ˢ Ioo 0 T)) ∧
    (∀ i j, MemLp (P.a_t i j) ⊤ (volume.restrict (Ω ×ˢ Ioo 0 T))) ∧
    MemLp P.c_t ⊤ (volume.restrict (Ω ×ˢ Ioo 0 T)) ∧
    (∀ i j, HasWeakTimeDerivOnCylinder Ω T (P.a i j) (P.a_t i j)) ∧
    HasWeakTimeDerivOnCylinder Ω T P.c P.c_t ∧
    (∀ i j, P.a i j =ᵐ[volume.restrict (Ω ×ˢ Ioo 0 T)] P.a j i) ∧
    ∃ θ : ℝ, 0 < θ ∧ ∀ᵐ p ∂(volume.restrict (Ω ×ˢ Ioo 0 T)), ∀ ξ : Fin n → ℝ,
      θ * ∑ i, ξ i ^ 2 ≤ ∑ i, ∑ j, P.a i j p * ξ i * ξ j

/-- The bilinear form (7.6) on `H¹₀(Ω)` at time `t`:
`a(u, v; t) = ∑ᵢⱼ ∫_Ω aᵢⱼ(x, t) ∂ᵢu(x) ∂ⱼv(x) dx + ∫_Ω c(x, t) u(x) v(x) dx`.
(The page prints `∂ⱼu` in the first integral; `a(u, v; t) = (Lu, v)_{L²}` and the symmetry claimed
right after Assumption 7.1 fix it as `∂ⱼv`.) -/
noncomputable def form {n : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin n))} (P : Coeffs n)
    (u v : H10 n Ω) (t : ℝ) : ℝ :=
  (∑ i, ∑ j, ∫ x in Ω, P.a i j (x, t) * pd u i x * pd v j x) +
    ∫ x in Ω, P.c (x, t) * val u x * val v x

/-- The time-differentiated form `a_t(u, v; t)`: the form (7.6) with `aᵢⱼ, c` replaced by their
time derivatives `aᵢⱼ_t, c_t`. -/
noncomputable def form_t {n : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin n))} (P : Coeffs n)
    (u v : H10 n Ω) (t : ℝ) : ℝ :=
  (∑ i, ∑ j, ∫ x in Ω, P.a_t i j (x, t) * pd u i x * pd v j x) +
    ∫ x in Ω, P.c_t (x, t) * val u x * val v x

/-- Definition 7.2 (Hunter, p. 213): `u : [0, T] → H¹₀(Ω)` is a weak solution of the IBVP (7.5)
`u_tt + L u = f` in `Ω × (0, T)`, `u = 0` on `∂Ω × (0, T)`, `u = g`, `u_t = h` at `t = 0`,
with weak derivatives `u_t` (an `L²(Ω)`-valued function) and `u_tt` (an `H⁻¹(Ω)`-valued
function), if
(1) `u_t` is the weak time derivative of `u` (regarded in `L²(Ω)`) and `u_tt` that of `u_t`
(regarded in `H⁻¹(Ω)`), with `u ∈ C([0, T]; H¹₀(Ω))`, `u_t ∈ C([0, T]; L²(Ω))`,
`u_tt ∈ L²(0, T; H⁻¹(Ω))`;
(2) (7.8) for every `v ∈ H¹₀(Ω)`: `⟨u_tt(t), v⟩ + a(u(t), v; t) = (f(t), v)_{L²}` for a.e.
`t ∈ [0, T]`;
(3) `u(0) = g` and `u_t(0) = h`.
Here `f : [0, T] → L²(Ω)`; values of `u, u_t, u_tt` outside `[0, T]` play no role. -/
def IsWeakSolution {n : ℕ} (Ω : Set (EuclideanSpace ℝ (Fin n))) (T : ℝ) (P : Coeffs n)
    (f : ℝ → L2 n Ω) (g : H10 n Ω) (h : L2 n Ω)
    (u : ℝ → H10 n Ω) (u_t : ℝ → L2 n Ω) (u_tt : ℝ → Hm1 n Ω) : Prop :=
  HasWeakTimeDeriv T (fun t => toL2 n Ω (u t)) u_t ∧
    HasWeakTimeDeriv T (fun t => l2ToHm1 (u_t t)) u_tt ∧
    ContinuousOn u (Icc 0 T) ∧ ContinuousOn u_t (Icc 0 T) ∧
    MemLp u_tt 2 (volume.restrict (Ioo 0 T)) ∧
    (∀ v : H10 n Ω, ∀ᵐ t ∂(volume.restrict (Icc 0 T)),
      u_tt t v + form P (u t) v t = inner ℝ (f t) (toL2 n Ω v)) ∧
    u 0 = g ∧ u_t 0 = h

end HunterPDE.Hyperbolic


