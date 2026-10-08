-- Prove2me | Definitions.Def_WeakMFG_Approx_Reward
-- name    : WeakMFG_Approx_Reward
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T01:26:34.884525+00:00
-- url     : https://prove2.me/theorems/42099a8d-8b69-4da7-98e1-531747a33342
-- title:
--   The Girsanov measures $P^{\mu,\alpha}$, the reward $J^{\mu,q}(\alpha)$ and solutions of the MFG (Definition 3.4)
-- statement:
--   For $\mu\in\mathcal P_\psi(\mathcal C)$ and $\alpha\in\mathbb A$ the measure $P^{\mu,\alpha}$ on $(\Omega,\mathcal F_T)$ is given by the Doléans exponential
--   $$\frac{dP^{\mu,\alpha}}{dP}=\mathcal E\Big(\int_0^\cdot\sigma^{-1}b(t,X,\mu,\alpha_t)\,dW_t\Big)_T = \exp\Big(\int_0^T\sigma^{-1}b(t,X,\mu,\alpha_t)\,dW_t-\frac12\int_0^T\big|\sigma^{-1}b(t,X,\mu,\alpha_t)\big|^2dt\Big).$$
--   For a measurable flow $q:[0,T]\to\mathcal P(A)$ the expected reward is
--   $$J^{\mu,q}(\alpha)=\mathbb E^{\mu,\alpha}\Big[\int_0^Tf(t,X,\mu,q_t,\alpha_t)\,dt+g(X,\mu)\Big],$$
--   and $V^{\mu,q}=\sup_{\alpha\in\mathbb A}J^{\mu,q}(\alpha)$.
--
--   **Definition 3.4.** A measure $\mu\in\mathcal P_\psi(\mathcal C)$ and a measurable $q:[0,T]\to\mathcal P(A)$ form a *solution of the MFG* if there exists $\alpha\in\mathbb A$ such that $V^{\mu,q}=J^{\mu,q}(\alpha)$, $P^{\mu,\alpha}\circ X^{-1}=\mu$, and $P^{\mu,\alpha}\circ\alpha_t^{-1}=q_t$ for almost every $t$.
--
--   Theorem 4.2 starts from such a solution whose control is given in closed loop, $\alpha_t=\hat\alpha(t,X)$.
--
--   **Formalization Note** A stochastic integral is determined only up to a version, so the density is a relation: $D$ is a version of $dP^{\mu,\alpha}/dP$ when $D=\exp(\sum_j J_j(T)-\frac12\int_0^T|\sigma^{-1}b|^2dt)$ for Itô integrals $J_j$ of the coordinates of $\sigma^{-1}b$ against those of $W$. $J^{\mu,q}(\alpha)$ is computed as $\mathbb E[D(\int_0^Tf\,dt+g)]$ for a version $D$. "$V^{\mu,q}=J^{\mu,q}(\alpha)$" is stated without a real supremum: $J^{\mu,q}(\beta)\le J^{\mu,q}(\alpha)$ for every admissible $\beta$ and all versions of both densities. The solution clauses require a version to exist and hold for every version. Measurability of $q$ refers to the Borel $\sigma$-field of the weak topology on $\mathcal P(A)$.
-- source:
--   Carmona, Lacker, A probabilistic weak formulation of mean field games and applications, arXiv:1307.1152v2 (2014), §3.1, pp. 9–10, density of P^{µ,α}, J^{µ,q}, V^{µ,q}, Definition 3.4

import Mathlib
import Definitions.Def_WeakMFG_Approx_Hyp

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal Matrix

namespace WeakMFG.Approx

variable {d : ℕ} {T : ℝ≥0} {EA : Type*} [NormedAddCommGroup EA] [NormedSpace ℝ EA]
  [MeasurableSpace EA] [BorelSpace EA]
  {Ω : Type*} [MeasurableSpace Ω] {B : Base d Ω} {ψ : WeakMFG.Existence.Path d T → ℝ} {A : Set EA}
  {σ : ℝ≥0 → WeakMFG.Existence.Path d T → Matrix (Fin d) (Fin d) ℝ}
  {b : ℝ≥0 → WeakMFG.Existence.Path d T → Ppsi ψ → EA → (Fin d → ℝ)}

/-- The Girsanov kernel `σ⁻¹ b(s, X, μ, α_s)` of `P^{μ,α}` (p. 9). -/
noncomputable def theta (X : Driftless B ψ A σ b) (μ : Ppsi ψ) (α : ℝ≥0 → Ω → EA) (s : ℝ≥0)
    (ω : Ω) : Fin d → ℝ :=
  (σ s (X.Xp ω))⁻¹ *ᵥ b s (X.Xp ω) μ (α s ω)

/-- `D` is a version of `dP^{μ,α}/dP = 𝓔(∫₀^· σ⁻¹ b(t, X, μ, α_t) dW_t)_T` (p. 9):
`D = exp(Σ_j J_j(T) − ½ ∫₀ᵀ |σ⁻¹ b|² dt)` for Itô integrals `J_j` of the coordinates of the kernel
against the coordinates of `W`, for the filtration `𝔽`.
Formalization Note (D6): Itô integrals are defined up to versions; definitions quantify over all
versions, and statements assert that one exists. -/
def IsDensity (X : Driftless B ψ A σ b) (μ : Ppsi ψ) (α : ℝ≥0 → Ω → EA) (D : Ω → ℝ) : Prop :=
  ∃ J : Fin d → ℝ≥0 → Ω → ℝ,
    (∀ j, Peng1990.SMP.IsItoIntegral B.filt B.P T (fun s ω => B.W s ω j)
      (fun s ω => theta X μ α s ω j) (J j)) ∧
    ∀ ω, D ω = Real.exp (∑ j, J j T ω -
      (1 / 2) * ∫ s in Set.Icc (0 : ℝ) T, ∑ j, (theta X μ α s.toNNReal ω j) ^ 2)

/-- `P^{μ,α}` for a version `D` of its density: `dP^{μ,α} = D dP` (p. 9). -/
noncomputable def Pma (B : Base d Ω) (D : Ω → ℝ) : Measure Ω :=
  B.P.withDensity (fun ω => ENNReal.ofReal (D ω))

/-- The expected reward `J^{μ,q}(α) := E^{μ,α}[∫₀ᵀ f(t, X, μ, q_t, α_t) dt + g(X, μ)]` (p. 10),
computed with the version `D` of `dP^{μ,α}/dP` as `E[D (∫₀ᵀ f dt + g)]`. -/
noncomputable def Jrew (X : Driftless B ψ A σ b)
    (f : ℝ≥0 → WeakMFG.Existence.Path d T → Ppsi ψ → PA A → EA → ℝ) (g : WeakMFG.Existence.Path d T → Ppsi ψ → ℝ)
    (μ : Ppsi ψ) (q : ℝ≥0 → PA A) (α : ℝ≥0 → Ω → EA) (D : Ω → ℝ) : ℝ :=
  ∫ ω, D ω * ((∫ t in Set.Icc (0 : ℝ) T,
      f t.toNNReal (X.Xp ω) μ (q t.toNNReal) (α t.toNNReal ω)) + g (X.Xp ω) μ) ∂B.P

/-- `V^{μ,q} = J^{μ,q}(α)` with `V^{μ,q} = sup_{α ∈ 𝔸} J^{μ,q}(α)` (p. 10), stated without a real
supremum: `α` is admissible and, for every admissible `β` and all versions of the two densities,
`J^{μ,q}(β) ≤ J^{μ,q}(α)`. -/
def IsOptimal (X : Driftless B ψ A σ b)
    (f : ℝ≥0 → WeakMFG.Existence.Path d T → Ppsi ψ → PA A → EA → ℝ) (g : WeakMFG.Existence.Path d T → Ppsi ψ → ℝ)
    (μ : Ppsi ψ) (q : ℝ≥0 → PA A) (α : ℝ≥0 → Ω → EA) : Prop :=
  ∀ β : ℝ≥0 → Ω → EA, IsAdmissible B A β → ∀ Dα Dβ : Ω → ℝ, IsDensity X μ α Dα →
    IsDensity X μ β Dβ → Jrew X f g μ q β Dβ ≤ Jrew X f g μ q α Dα

/-- The clauses of Definition 3.4 (p. 10) for a given control `α`: `α ∈ 𝔸`, `V^{μ,q} = J^{μ,q}(α)`,
`P^{μ,α} ∘ X⁻¹ = μ`, and `P^{μ,α} ∘ α_t⁻¹ = q_t` for almost every `t ∈ [0, T]`. -/
def SolvesMFGWith (X : Driftless B ψ A σ b)
    (f : ℝ≥0 → WeakMFG.Existence.Path d T → Ppsi ψ → PA A → EA → ℝ) (g : WeakMFG.Existence.Path d T → Ppsi ψ → ℝ)
    (μ : Ppsi ψ) (q : ℝ≥0 → PA A) (α : ℝ≥0 → Ω → EA) : Prop :=
  IsAdmissible B A α ∧ (∃ D, IsDensity X μ α D) ∧ IsOptimal X f g μ q α ∧
    ∀ D, IsDensity X μ α D →
      (Pma B D).map X.Xp = μ.μ ∧
      ∀ᵐ t ∂(volume.restrict (Set.Icc (0 : ℝ) T)),
        (Pma B D).map (α t.toNNReal) = (q t.toNNReal : Measure A).map Subtype.val

/-- Definition 3.4, p. 10: `(μ, q)`, with `q : [0, T] → P(A)` measurable (Borel σ-field of the weak
topology), is a solution of the MFG if some `α ∈ 𝔸` satisfies the clauses of `SolvesMFGWith`. -/
def IsMFGSolution (X : Driftless B ψ A σ b)
    (f : ℝ≥0 → WeakMFG.Existence.Path d T → Ppsi ψ → PA A → EA → ℝ) (g : WeakMFG.Existence.Path d T → Ppsi ψ → ℝ)
    (μ : Ppsi ψ) (q : ℝ≥0 → PA A) : Prop :=
  Measurable[_, borel (PA A)] q ∧ ∃ α : ℝ≥0 → Ω → EA, SolvesMFGWith X f g μ q α

end WeakMFG.Approx


