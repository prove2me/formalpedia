-- Prove2me | Definitions.Def_WeakMFG_Uniqueness_Reward
-- name    : WeakMFG_Uniqueness_Reward
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T00:24:22.582542+00:00
-- url     : https://prove2.me/theorems/e623983c-41af-4914-ad83-fbcb93ae5c53
-- title:
--   Girsanov density, $P^{\mu,\alpha}$, the reward $J^{\mu,q}(\alpha)$, solutions of the MFG (Definition 3.4), the Hamiltonian (3.2)
-- statement:
--   Fix the data of the standing assumptions and the driftless state $X$. For $\mu\in\mathcal P_\psi(\mathcal C)$ and an admissible control $\alpha\in\mathbb A$ write $\theta^{\mu,\alpha}_t = \sigma^{-1}b(t,X,\mu,\alpha_t)$.
--
--   1. **Change of measure** (p. 9). $P^{\mu,\alpha}$ is the measure with density
--   $$\frac{dP^{\mu,\alpha}}{dP} = \mathcal E\Big(\int_0^\cdot \sigma^{-1}b(t,X,\mu,\alpha_t)\,dW_t\Big)_T = \exp\Big(\int_0^T\theta^{\mu,\alpha}_t\cdot dW_t - \tfrac12\int_0^T|\theta^{\mu,\alpha}_t|^2dt\Big).$$
--   2. **Reward** (p. 10). For a flow $t\mapsto q_t\in\mathcal P(A)$,
--   $$J^{\mu,q}(\alpha) = E^{\mu,\alpha}\Big[\int_0^T f(t,X,\mu,q_t,\alpha_t)\,dt + g(X,\mu)\Big].$$
--   The control $\alpha$ is *optimal* when $J^{\mu,q}(\beta)\le J^{\mu,q}(\alpha)$ for every $\beta\in\mathbb A$, i.e. $V^{\mu,q} = \sup_{\beta\in\mathbb A}J^{\mu,q}(\beta) = J^{\mu,q}(\alpha)$.
--   3. **Definition 3.4.** $\mu\in\mathcal P_\psi(\mathcal C)$ and a measurable $q:[0,T]\to\mathcal P(A)$ form a *solution of the MFG* if there is $\alpha\in\mathbb A$ with $V^{\mu,q}=J^{\mu,q}(\alpha)$, $P^{\mu,\alpha}\circ X^{-1}=\mu$, and $P^{\mu,\alpha}\circ\alpha_t^{-1}=q_t$ for almost every $t$.
--   4. **Hamiltonian** (3.2).
--   $$h(t,x,\mu,q,z,a) = f(t,x,\mu,q,a) + z\cdot\sigma^{-1}b(t,x,\mu,a),\qquad H(t,x,\mu,q,z) = \sup_{a\in A}h(t,x,\mu,q,z,a),$$
--   and $A(t,x,\mu,q,z) = \{a\in A : h(t,x,\mu,q,z,a) = H(t,x,\mu,q,z)\}$ is the set of maximizers.
--
--   Definition 3.4 is the solution concept of the weak formulation: the population law $\mu$ and the control flow $q$ are reproduced by an optimal control of the representative player.
--
--   **Formalization Note.** A stochastic integral is determined only up to a version, so the density is a predicate on a random variable $D$ (some version of the Itô integrals gives $D$); every statement asserts that a version exists and quantifies over all versions, and $E^{\mu,\alpha}[F]$ is $E[D\,F]$. $|\theta|^2$ is the Euclidean square, written as a sum of squares of coordinates. Optimality is stated against every admissible competitor rather than through a real supremum. The law conditions of Definition 3.4 are asked for every version of the density; the law of $\alpha_t$ is compared with $q_t$ pushed from $A$ into the ambient space. $q$ is measurable for the Borel $\sigma$-field of the weak topology on $\mathcal P(A)$. $H$ is a real supremum of $h(\cdot)$ over $A$; under (S.1) and (S.3) the image is compact, so it is a maximum.
-- source:
--   Carmona, Lacker, A probabilistic weak formulation of mean field games and applications, arXiv:1307.1152v2 (2014), §3.1, p. 9 (P^{µ,α}), p. 10 (J^{µ,q}, V^{µ,q}, Definition 3.4, (3.2))

import Mathlib
import Definitions.Def_WeakMFG_Uniqueness_Hyp

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal Matrix

namespace WeakMFG.Uniqueness

variable {d : ℕ} {T : ℝ≥0} {Ω : Type*} [MeasurableSpace Ω]
  {EA : Type*} [NormedAddCommGroup EA] [NormedSpace ℝ EA] [MeasurableSpace EA] [BorelSpace EA]
  {ψ : WeakMFG.Existence.Path d T → ℝ}

/-- The Girsanov drift `θ^{μ,α}_s = σ⁻¹ b(s, X, μ, α_s)` (p. 9). -/
noncomputable def theta (σ : ℝ≥0 → WeakMFG.Existence.Path d T → Matrix (Fin d) (Fin d) ℝ)
    (b : ℝ≥0 → WeakMFG.Existence.Path d T → Ppsi ψ → EA → (Fin d → ℝ)) (Xp : Ω → WeakMFG.Existence.Path d T) (μ : Ppsi ψ)
    (α : ℝ≥0 → Ω → EA) (s : ℝ≥0) (ω : Ω) : Fin d → ℝ :=
  (σ s (Xp ω))⁻¹ *ᵥ b s (Xp ω) μ (α s ω)

/-- `D` is a version of the density `dP^{μ,α}/dP = 𝓔(∫₀^· σ⁻¹b(t, X, μ, α_t) dW_t)_T` (p. 9), the
Doléans exponential at time `T`:
`D = exp(Σ_j ∫₀ᵀ θ^j dW^j − ½ ∫₀ᵀ |θ_s|² ds)` for Itô integral processes of the coordinates
`θ^j` of `θ^{μ,α}` against `W^j`.
**Formalization Note.** (D6) An Itô integral is determined only up to a version
(`Peng1990.SMP.IsItoIntegral` is "`J` is *a* version of `∫ H dW`"), so the density is a predicate
on `D`; every statement that uses it asserts that a version exists and quantifies over all
versions. The Euclidean square `|θ|²` is written as a sum of squares of coordinates. -/
def IsDensity (B : Base d Ω) (σ : ℝ≥0 → WeakMFG.Existence.Path d T → Matrix (Fin d) (Fin d) ℝ)
    (b : ℝ≥0 → WeakMFG.Existence.Path d T → Ppsi ψ → EA → (Fin d → ℝ)) (Xp : Ω → WeakMFG.Existence.Path d T) (μ : Ppsi ψ)
    (α : ℝ≥0 → Ω → EA) (D : Ω → ℝ) : Prop :=
  ∃ J : Fin d → ℝ≥0 → Ω → ℝ,
    (∀ j, Peng1990.SMP.IsItoIntegral B.filt B.P T (fun s ω => B.W s ω j)
      (fun s ω => theta σ b Xp μ α s ω j) (J j)) ∧
    ∀ ω, D ω = Real.exp (∑ j, J j T ω -
      (1 / 2) * ∫ s in Set.Icc (0 : ℝ) T, ∑ j, (theta σ b Xp μ α s.toNNReal ω j) ^ 2)

/-- The measure `P^{μ,α}` with `dP^{μ,α}/dP = D` (p. 9), for a version `D` of the density. -/
noncomputable def Pma (B : Base d Ω) (D : Ω → ℝ) : Measure Ω :=
  B.P.withDensity (fun ω => ENNReal.ofReal (D ω))

/-- The expected reward `J^{μ,q}(α) = E^{μ,α}[∫₀ᵀ f(t, X, μ, q_t, α_t) dt + g(X, μ)]` (p. 10),
computed with the density version `D` of `dP^{μ,α}/dP` as `E[D · (∫₀ᵀ f dt + g)]`. -/
noncomputable def Jrew (B : Base d Ω) (A : Set EA)
    (f : ℝ≥0 → WeakMFG.Existence.Path d T → Ppsi ψ → PA A → EA → ℝ) (g : WeakMFG.Existence.Path d T → Ppsi ψ → ℝ)
    (Xp : Ω → WeakMFG.Existence.Path d T) (μ : Ppsi ψ) (q : ℝ≥0 → PA A) (α : ℝ≥0 → Ω → EA) (D : Ω → ℝ) : ℝ :=
  ∫ ω, D ω * ((∫ t in Set.Icc (0 : ℝ) T,
      f t.toNNReal (Xp ω) μ (q t.toNNReal) (α t.toNNReal ω)) + g (Xp ω) μ) ∂B.P

/-- `V^{μ,q} = J^{μ,q}(α)` (p. 10), where `V^{μ,q} = sup_{β ∈ 𝔸} J^{μ,q}(β)`: the admissible
control `α` is optimal, i.e. `J^{μ,q}(β) ≤ J^{μ,q}(α)` for every admissible `β`, for every
version of either density.
**Formalization Note.** The value is never written as a real supremum (a real `⨆` of an
unbounded family would be `0`); `V^{μ,q} = J^{μ,q}(α)` for an admissible `α` is exactly this
optimality. -/
def IsOptimal (B : Base d Ω) (A : Set EA) (σ : ℝ≥0 → WeakMFG.Existence.Path d T → Matrix (Fin d) (Fin d) ℝ)
    (b : ℝ≥0 → WeakMFG.Existence.Path d T → Ppsi ψ → EA → (Fin d → ℝ))
    (f : ℝ≥0 → WeakMFG.Existence.Path d T → Ppsi ψ → PA A → EA → ℝ) (g : WeakMFG.Existence.Path d T → Ppsi ψ → ℝ)
    (Xp : Ω → WeakMFG.Existence.Path d T) (μ : Ppsi ψ) (q : ℝ≥0 → PA A) (α : ℝ≥0 → Ω → EA) : Prop :=
  ∀ β : ℝ≥0 → Ω → EA, B.IsAdmissible A β → ∀ Dα Dβ : Ω → ℝ,
    IsDensity B σ b Xp μ α Dα → IsDensity B σ b Xp μ β Dβ →
    Jrew B A f g Xp μ q β Dβ ≤ Jrew B A f g Xp μ q α Dα

/-- `α` witnesses that `(μ, q)` solves the MFG (Definition 3.4, p. 10): `α ∈ 𝔸`, the density of
`P^{μ,α}` exists, `V^{μ,q} = J^{μ,q}(α)`, `P^{μ,α} ∘ X⁻¹ = μ`, and `P^{μ,α} ∘ α_t⁻¹ = q_t` for
almost every `t ∈ [0, T]` (the law of `α_t` is `q_t`, pushed from `A` into `EA`). The two law
conditions hold for every version of the density. -/
def IsMFGWitness (B : Base d Ω) (A : Set EA) (σ : ℝ≥0 → WeakMFG.Existence.Path d T → Matrix (Fin d) (Fin d) ℝ)
    (b : ℝ≥0 → WeakMFG.Existence.Path d T → Ppsi ψ → EA → (Fin d → ℝ))
    (f : ℝ≥0 → WeakMFG.Existence.Path d T → Ppsi ψ → PA A → EA → ℝ) (g : WeakMFG.Existence.Path d T → Ppsi ψ → ℝ)
    (Xp : Ω → WeakMFG.Existence.Path d T) (μ : Ppsi ψ) (q : ℝ≥0 → PA A) (α : ℝ≥0 → Ω → EA) : Prop :=
  B.IsAdmissible A α ∧ (∃ D, IsDensity B σ b Xp μ α D) ∧ IsOptimal B A σ b f g Xp μ q α ∧
    ∀ D, IsDensity B σ b Xp μ α D →
      (Pma B D).map Xp = μ.toMeasure ∧
      ∀ᵐ t ∂(volume.restrict (Set.Icc (0 : ℝ) T)),
        (Pma B D).map (α t.toNNReal) = ((q t.toNNReal : Measure A)).map Subtype.val

/-- Definition 3.4, p. 10: `μ ∈ P_ψ(𝒞)` and a measurable `q : [0, T] → P(A)` (Borel σ-field of
the weak topology) form a *solution of the MFG* if some `α ∈ 𝔸` has `V^{μ,q} = J^{μ,q}(α)`,
`P^{μ,α} ∘ X⁻¹ = μ`, and `P^{μ,α} ∘ α_t⁻¹ = q_t` for almost every `t`. -/
def IsMFGSolution (B : Base d Ω) (A : Set EA) (σ : ℝ≥0 → WeakMFG.Existence.Path d T → Matrix (Fin d) (Fin d) ℝ)
    (b : ℝ≥0 → WeakMFG.Existence.Path d T → Ppsi ψ → EA → (Fin d → ℝ))
    (f : ℝ≥0 → WeakMFG.Existence.Path d T → Ppsi ψ → PA A → EA → ℝ) (g : WeakMFG.Existence.Path d T → Ppsi ψ → ℝ)
    (Xp : Ω → WeakMFG.Existence.Path d T) (μ : Ppsi ψ) (q : ℝ≥0 → PA A) : Prop :=
  @Measurable ℝ≥0 (PA A) _ (borel (PA A)) q ∧
    ∃ α : ℝ≥0 → Ω → EA, IsMFGWitness B A σ b f g Xp μ q α

/-- The Hamiltonian `h(t, x, μ, q, z, a) = f(t, x, μ, q, a) + z · σ⁻¹b(t, x, μ, a)` (3.2), p. 10. -/
noncomputable def ham {A : Set EA} (σ : ℝ≥0 → WeakMFG.Existence.Path d T → Matrix (Fin d) (Fin d) ℝ)
    (b : ℝ≥0 → WeakMFG.Existence.Path d T → Ppsi ψ → EA → (Fin d → ℝ))
    (f : ℝ≥0 → WeakMFG.Existence.Path d T → Ppsi ψ → PA A → EA → ℝ) (t : ℝ≥0) (x : WeakMFG.Existence.Path d T) (μ : Ppsi ψ)
    (q : PA A) (z : Fin d → ℝ) (a : EA) : ℝ :=
  f t x μ q a + z ⬝ᵥ ((σ t x)⁻¹ *ᵥ b t x μ a)

/-- The maximized Hamiltonian `H(t, x, μ, q, z) = sup_{a ∈ A} h(t, x, μ, q, z, a)` (3.2), p. 10.
Under (S.1) and (S.3) the image `h(…, A)` is compact, so this is a maximum. -/
noncomputable def Ham (A : Set EA) (σ : ℝ≥0 → WeakMFG.Existence.Path d T → Matrix (Fin d) (Fin d) ℝ)
    (b : ℝ≥0 → WeakMFG.Existence.Path d T → Ppsi ψ → EA → (Fin d → ℝ))
    (f : ℝ≥0 → WeakMFG.Existence.Path d T → Ppsi ψ → PA A → EA → ℝ) (t : ℝ≥0) (x : WeakMFG.Existence.Path d T) (μ : Ppsi ψ)
    (q : PA A) (z : Fin d → ℝ) : ℝ :=
  sSup ((ham σ b f t x μ q z) '' A)

/-- The set of maximizers `A(t, x, μ, q, z) = {a ∈ A : h(t, x, μ, q, z, a) = H(t, x, μ, q, z)}`
(3.2), p. 10. Under (S.5) it does not depend on `q`; the paper then writes `A(t, x, μ, z)`. -/
def Amax (A : Set EA) (σ : ℝ≥0 → WeakMFG.Existence.Path d T → Matrix (Fin d) (Fin d) ℝ)
    (b : ℝ≥0 → WeakMFG.Existence.Path d T → Ppsi ψ → EA → (Fin d → ℝ))
    (f : ℝ≥0 → WeakMFG.Existence.Path d T → Ppsi ψ → PA A → EA → ℝ) (t : ℝ≥0) (x : WeakMFG.Existence.Path d T) (μ : Ppsi ψ)
    (q : PA A) (z : Fin d → ℝ) : Set EA :=
  {a ∈ A | ham σ b f t x μ q z a = Ham A σ b f t x μ q z}

end WeakMFG.Uniqueness


