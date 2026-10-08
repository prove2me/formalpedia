-- Prove2me | Definitions.Def_WeakMFG_Existence_Reward
-- name    : WeakMFG_Existence_Reward
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T23:13:49.22183+00:00
-- url     : https://prove2.me/theorems/51701fbb-cc97-48bb-856d-bc77c1214f6d
-- title:
--   Girsanov density, P^{µ,α}, the reward J^{µ,q}, optimality, Definition 3.4 (solution of the MFG), the Hamiltonian (3.2) and assumption (C)
-- statement:
--   In the setting of the standing assumptions (S):
--
--   1. **Change of measure.** For $\mu\in\mathcal P_\psi(\mathcal C)$ and $\alpha\in\mathbb A$, the measure $P^{\mu,\alpha}$ is defined by
--   $$\frac{dP^{\mu,\alpha}}{dP}=\mathcal E\Big(\int_0^\cdot\sigma^{-1}b(t,X,\mu,\alpha_t)\,dW_t\Big)_T=\exp\Big(\int_0^T\theta_t\cdot dW_t-\tfrac12\int_0^T|\theta_t|^2\,dt\Big),\qquad \theta_t=\sigma^{-1}b(t,X,\mu,\alpha_t).$$
--   2. **Reward.** For a measurable flow $q:[0,T]\to\mathcal P(A)$,
--   $$J^{\mu,q}(\alpha)=\mathbb E^{\mu,\alpha}\Big[\int_0^T f(t,X,\mu,q_t,\alpha_t)\,dt+g(X,\mu)\Big],\qquad V^{\mu,q}=\sup_{\alpha\in\mathbb A}J^{\mu,q}(\alpha).$$
--   3. **Definition 3.4.** $\mu\in\mathcal P_\psi(\mathcal C)$ and a measurable $q:[0,T]\to\mathcal P(A)$ form a *solution of the MFG* if there is $\alpha\in\mathbb A$ with $V^{\mu,q}=J^{\mu,q}(\alpha)$, $P^{\mu,\alpha}\circ X^{-1}=\mu$, and $P^{\mu,\alpha}\circ\alpha_t^{-1}=q_t$ for almost every $t$.
--   4. **Hamiltonian (3.2).** $h(t,x,\mu,q,z,a)=f(t,x,\mu,q,a)+z\cdot\sigma^{-1}b(t,x,\mu,a)$, $H(t,x,\mu,q,z)=\sup_{a\in A}h$, and $A(t,x,\mu,q,z)=\{a\in A: h(t,x,\mu,q,z,a)=H(t,x,\mu,q,z)\}$.
--   5. **Assumption (C).** For each $(t,x,\mu,z)$ the set $A(t,x,\mu,z)$ is convex.
--
--   **Formalization Note** Itô integrals are relations (a process is *a* version of the integral), so the density is a predicate on versions $D$, and $P^{\mu,\alpha}=D\cdot P$; the solution concept requires that a version exists and that the law identities hold for every version. $V^{\mu,q}=J^{\mu,q}(\alpha)$ is stated as optimality: $J^{\mu,q}(\beta)\le J^{\mu,q}(\alpha)$ for every admissible $\beta$ and all versions; no real supremum is formed. $J$ is computed as $\mathbb E[D(\int_0^T f\,dt+g)]$. "Almost every $t$" is Lebesgue-a.e. on $[0,T]$, and $P^{\mu,\alpha}\circ\alpha_t^{-1}$ (a law on $E_A$) is compared with $q_t$ pushed forward along $A\hookrightarrow E_A$. $\sigma^{-1}$ is Mathlib's matrix inverse; assumption (C) is required wherever $\sigma(t,x)$ is nonsingular, i.e. wherever the page's $\sigma^{-1}$, $h$ and $A(t,x,\mu,z)$ are defined, and for every $q$ (by (S.5) the maximizer set does not depend on $q$). $H$ is a real supremum; every statement using it assumes (S.1) and (S.3), which make it a maximum over the compact set $A$.
-- source:
--   Carmona, Lacker, A probabilistic weak formulation of mean field games and applications, arXiv:1307.1152v2 (2014), §3.1, pp. 9–10 (P^{µ,α}, J^{µ,q}, V^{µ,q}, Definition 3.4); §3.2, p. 10 ((3.2), (C))

import Mathlib
import Definitions.Def_Peng1990_SMP_Stochastic
import Definitions.Def_WeakMFG_Existence_Model
import Definitions.Def_WeakMFG_Existence_Hyp

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal Matrix

namespace WeakMFG.Existence

variable {d : ℕ} {T : ℝ≥0} {Ω : Type*} [MeasurableSpace Ω]
  {EA : Type*} [NormedAddCommGroup EA] [NormedSpace ℝ EA] [MeasurableSpace EA] [BorelSpace EA]

/-- The Girsanov integrand `θ_s = σ⁻¹b(s, X, μ, α_s)` (p. 9). -/
noncomputable def theta {ψ : Path d T → ℝ}
    (σ : ℝ≥0 → Path d T → Matrix (Fin d) (Fin d) ℝ)
    (b : ℝ≥0 → Path d T → Ppsi ψ → EA → (Fin d → ℝ)) (Xp : Ω → Path d T)
    (μ : Ppsi ψ) (α : ℝ≥0 → Ω → EA) (s : ℝ≥0) (ω : Ω) : Fin d → ℝ :=
  (σ s (Xp ω))⁻¹ *ᵥ b s (Xp ω) μ (α s ω)

/-- `D` is a version of the density `dP^{μ,α}/dP = E(∫₀^· σ⁻¹b(t, X, μ, α_t) dW_t)_T` (p. 9):
`D = exp(∑_j J_j(T) − ½ ∫₀ᵀ |θ_s|² ds)` for Itô integrals `J_j = ∫ θ^j dW^j` (Euclidean `|·|²`
written as a coordinate sum).
Formalization Note (D6): Itô integrals are relations (`IsItoIntegral` says `J_j` is *a* version),
so a density is a predicate on versions; statements quantify over all versions. -/
def IsDensity {ψ : Path d T → ℝ} (B : Base d T Ω)
    (σ : ℝ≥0 → Path d T → Matrix (Fin d) (Fin d) ℝ)
    (b : ℝ≥0 → Path d T → Ppsi ψ → EA → (Fin d → ℝ)) (Xp : Ω → Path d T)
    (μ : Ppsi ψ) (α : ℝ≥0 → Ω → EA) (D : Ω → ℝ) : Prop :=
  ∃ J : Fin d → ℝ≥0 → Ω → ℝ,
    (∀ j, Peng1990.SMP.IsItoIntegral B.filt B.P T (fun s ω => B.W s ω j)
      (fun s ω => theta σ b Xp μ α s ω j) (J j)) ∧
    ∀ ω, D ω = Real.exp (∑ j, J j T ω -
      (1 / 2) * ∫ s in Set.Icc (0 : ℝ) T, ∑ j, (theta σ b Xp μ α s.toNNReal ω j) ^ 2)

/-- `P^{μ,α}` for a density version `D`: `dP^{μ,α} = D dP` (p. 9). -/
noncomputable def Pma (P : Measure Ω) (D : Ω → ℝ) : Measure Ω :=
  P.withDensity (fun ω => ENNReal.ofReal (D ω))

/-- The expected reward `J^{μ,q}(α) = E^{μ,α}[∫₀ᵀ f(t, X, μ, q_t, α_t) dt + g(X, μ)]` (p. 10),
computed as `E[D (∫₀ᵀ f dt + g)]` for a density version `D`. -/
noncomputable def Jrew {ψ : Path d T → ℝ} {A : Set EA} (B : Base d T Ω)
    (f : ℝ≥0 → Path d T → Ppsi ψ → PA A → EA → ℝ) (g : Path d T → Ppsi ψ → ℝ)
    (Xp : Ω → Path d T) (μ : Ppsi ψ) (q : ℝ≥0 → PA A) (α : ℝ≥0 → Ω → EA) (D : Ω → ℝ) : ℝ :=
  ∫ ω, D ω * ((∫ t in Set.Icc (0 : ℝ) T,
      f t.toNNReal (Xp ω) μ (q t.toNNReal) (α t.toNNReal ω)) + g (Xp ω) μ) ∂B.P

/-- `V^{μ,q} = J^{μ,q}(α)` (p. 10): `α` is optimal, i.e. `J^{μ,q}(β) ≤ J^{μ,q}(α)` for every
admissible `β`, for all density versions of `α` and of `β`.
Formalization Note: `V^{μ,q} = sup_{α ∈ 𝔸} J^{μ,q}(α)` is never formed as a real supremum. -/
def IsOptimal {ψ : Path d T → ℝ} {A : Set EA} (B : Base d T Ω)
    (σ : ℝ≥0 → Path d T → Matrix (Fin d) (Fin d) ℝ)
    (b : ℝ≥0 → Path d T → Ppsi ψ → EA → (Fin d → ℝ))
    (f : ℝ≥0 → Path d T → Ppsi ψ → PA A → EA → ℝ) (g : Path d T → Ppsi ψ → ℝ)
    (Xp : Ω → Path d T) (μ : Ppsi ψ) (q : ℝ≥0 → PA A) (α : ℝ≥0 → Ω → EA) : Prop :=
  ∀ β : ℝ≥0 → Ω → EA, IsAdmissible B A β →
    ∀ Dα Dβ : Ω → ℝ, IsDensity B σ b Xp μ α Dα → IsDensity B σ b Xp μ β Dβ →
      Jrew B f g Xp μ q β Dβ ≤ Jrew B f g Xp μ q α Dα

/-- Definition 3.4 (p. 10): `μ ∈ P_ψ(C)` and a measurable `q : [0, T] → P(A)` form a solution of
the MFG if there is `α ∈ 𝔸` with `V^{μ,q} = J^{μ,q}(α)`, `P^{μ,α} ∘ X⁻¹ = μ` and
`P^{μ,α} ∘ α_t⁻¹ = q_t` for almost every `t`.
Formalization Notes: (D6) a density version of `α` exists, and the two law identities hold for
every version; "almost every t" is Lebesgue-a.e. on `[0, T]`; `q` is measurable for the Borel
σ-field of the weak topology on `P(A)`; `P^{μ,α} ∘ α_t⁻¹` is a measure on `EA`, compared with
`q_t` pushed forward along `A ↪ EA`. -/
def IsMFGSolution {ψ : Path d T → ℝ} {A : Set EA} (B : Base d T Ω)
    (σ : ℝ≥0 → Path d T → Matrix (Fin d) (Fin d) ℝ)
    (b : ℝ≥0 → Path d T → Ppsi ψ → EA → (Fin d → ℝ))
    (f : ℝ≥0 → Path d T → Ppsi ψ → PA A → EA → ℝ) (g : Path d T → Ppsi ψ → ℝ)
    (Xp : Ω → Path d T) (μ : Ppsi ψ) (q : ℝ≥0 → PA A) : Prop :=
  Measurable q ∧
  ∃ α : ℝ≥0 → Ω → EA, IsAdmissible B A α ∧
    (∃ D, IsDensity B σ b Xp μ α D) ∧
    IsOptimal B σ b f g Xp μ q α ∧
    ∀ D, IsDensity B σ b Xp μ α D →
      (Pma B.P D).map Xp = μ.toMeasure ∧
      ∀ᵐ t ∂(volume.restrict (Set.Icc (0 : ℝ) T)),
        (Pma B.P D).map (α t.toNNReal) = (q t.toNNReal).meas.map Subtype.val

/-- The Hamiltonian `h(t, x, μ, q, z, a) = f(t, x, μ, q, a) + z · σ⁻¹b(t, x, μ, a)` (3.2). -/
noncomputable def ham {ψ : Path d T → ℝ} {A : Set EA}
    (σ : ℝ≥0 → Path d T → Matrix (Fin d) (Fin d) ℝ)
    (b : ℝ≥0 → Path d T → Ppsi ψ → EA → (Fin d → ℝ))
    (f : ℝ≥0 → Path d T → Ppsi ψ → PA A → EA → ℝ)
    (t : ℝ≥0) (x : Path d T) (μ : Ppsi ψ) (q : PA A) (z : Fin d → ℝ) (a : EA) : ℝ :=
  f t x μ q a + z ⬝ᵥ ((σ t x)⁻¹ *ᵥ b t x μ a)

/-- The maximized Hamiltonian `H(t, x, μ, q, z) = sup_{a ∈ A} h(t, x, μ, q, z, a)` (3.2).
Formalization Note: a real `sSup`; every statement using it assumes (S.1) and (S.3), under which
it is a maximum of a continuous function over the compact set `A`. -/
noncomputable def Ham {ψ : Path d T → ℝ} {A : Set EA}
    (σ : ℝ≥0 → Path d T → Matrix (Fin d) (Fin d) ℝ)
    (b : ℝ≥0 → Path d T → Ppsi ψ → EA → (Fin d → ℝ))
    (f : ℝ≥0 → Path d T → Ppsi ψ → PA A → EA → ℝ)
    (t : ℝ≥0) (x : Path d T) (μ : Ppsi ψ) (q : PA A) (z : Fin d → ℝ) : ℝ :=
  sSup ((ham σ b f t x μ q z) '' A)

/-- The maximizer set `A(t, x, μ, q, z) = {a ∈ A : h(t, x, μ, q, z, a) = H(t, x, μ, q, z)}`
(3.2). By (S.5) it does not depend on `q`; the argument is kept. -/
def Amax {ψ : Path d T → ℝ} {A : Set EA}
    (σ : ℝ≥0 → Path d T → Matrix (Fin d) (Fin d) ℝ)
    (b : ℝ≥0 → Path d T → Ppsi ψ → EA → (Fin d → ℝ))
    (f : ℝ≥0 → Path d T → Ppsi ψ → PA A → EA → ℝ)
    (t : ℝ≥0) (x : Path d T) (μ : Ppsi ψ) (q : PA A) (z : Fin d → ℝ) : Set EA :=
  {a ∈ A | ham σ b f t x μ q z a = Ham σ b f t x μ q z}

/-- Assumption (C) (p. 10): for each `(t, x, μ, z)` the set `A(t, x, μ, z)` is convex.
Formalization Note: required at every `(t, x)` where `σ(t, x)` is nonsingular, i.e. wherever the
page's `σ⁻¹` (and so `h` and `A(t, x, μ, z)`) is defined; it is quantified over every `q`. -/
def CondC {ψ : Path d T → ℝ} {A : Set EA}
    (σ : ℝ≥0 → Path d T → Matrix (Fin d) (Fin d) ℝ)
    (b : ℝ≥0 → Path d T → Ppsi ψ → EA → (Fin d → ℝ))
    (f : ℝ≥0 → Path d T → Ppsi ψ → PA A → EA → ℝ) : Prop :=
  ∀ t x, IsUnit (σ t x).det → ∀ μ q z, Convex ℝ (Amax σ b f t x μ q z)

end WeakMFG.Existence


