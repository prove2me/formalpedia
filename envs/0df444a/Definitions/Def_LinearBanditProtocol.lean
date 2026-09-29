-- Prove2me | Definitions.Def_LinearBanditProtocol
-- name    : LinearBanditProtocol
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-07-29T16:52:45.382579+00:00
-- url     : https://prove2.me/theorems/d1024d12-2c70-433d-b6b4-cb005937ff23
-- statement:
--   The stochastic linear bandit protocol of L&S Ch 24-25 with unit-variance Gaussian noise: histories of (action, reward) pairs in $\mathbb{R}^d \times \mathbb{R}$; policies as families of Markov kernels from histories to actions (`LinearBanditPolicy`, mirroring `BanditPolicy`); the canonical interconnection measure $\mathbb{P}_\theta$ (`linearBanditMeasure`), where round $t$ appends $(A_t, \langle A_t,\theta\rangle + \eta_t)$ with $\eta_t \sim \mathcal{N}(0,1)$ independent; the support predicate `IsSupportedLinearPolicy`; and the expected regret
--
--   $$R_n(\mathcal{A},\theta) = n\max_{a\in\mathcal{A}}\langle a,\theta\rangle - \mathbb{E}_\theta\Big[\sum_t \langle A_t,\theta\rangle\Big].$$
--
--   For fixed finite action sets (Ch 25): `gaussianLinearBandit` (the $k$-armed bandit with arm means $\langle a_j, \theta\rangle$), gaps $\Delta_a$, the expected design matrix
--
--   $$\bar G_n = \sum_j \mathbb{E}[T_j(n)]\, a_j a_j^\top,$$
--
--   the allocation matrix $H_\alpha$, and the allocation-program value $c(\mathcal{A},\theta)$ of Corollary 25.2 (allocations restricted to positive-definite $H_\alpha$).
-- source:
--   L&S Ch 24 p.288 (protocol, regret), Ch 25 §25.1 pp.296-297 (finite-action objects)

import Definitions.Def_BanditPolicy
import Definitions.Def_GaussianBandit
import Definitions.Def_SelfNormalizedProcess

/-!
Lattimore & Szepesvári, *Bandit Algorithms* (CUP 2020), Chapters 24-25:
the stochastic linear bandit protocol used in the linear lower-bound chapters.

CONTINUOUS ACTION SETS (Ch 24, p.288). In round `t` the learner selects an
action `A_t ∈ ℝ^d` based on the history and observes the reward
`X_t = ⟨A_t, θ⟩ + η_t`, where `η_t ~ 𝒩(0,1)` is independent standard Gaussian
noise and `θ ∈ ℝ^d` is the unknown parameter. A history is a finite sequence
of (action, reward) pairs; a policy is a family of Markov kernels from
histories to actions, mirroring `BanditPolicy`. The interconnection measure
`linearBanditMeasure θ π n` is built by the same snoc recursion as
`banditMeasure`: round `n + 1` composes the current history measure with the
selection kernel and an independent standard Gaussian, then appends
`(A, ⟨A, θ⟩ + η)`. The constraint that the policy only plays actions in the
action set `𝒜` is NOT baked into the policy structure; it is the separate
predicate `IsSupportedLinearPolicy 𝒜 π`, taken as a hypothesis by the Ch 24
theorems (this keeps one protocol for all action sets).

The regret (p.288) is `R_n(𝒜, θ) = n max_{a ∈ 𝒜} ⟨a, θ⟩ − E[∑_{t=1}^n X_t]`;
since the noise has mean zero, `E[∑ X_t] = E[∑ ⟨A_t, θ⟩]`, and
`linearBanditExpectedRegret` uses the noise-free form (the sup over `𝒜` is a
real `sSup` of the image of `𝒜` under `⟨·, θ⟩`; it is finite for the compact
action sets of Ch 24).

FIXED FINITE ACTION SETS (Ch 25, §25.1, p.296). A linear bandit with the
finite action set `arms : Fin k → Fin d → ℝ` and Gaussian noise is just the
`k`-armed stochastic bandit whose arm `j` has reward `𝒩(⟨arms j, θ⟩, 1)`
(`gaussianLinearBandit`), so the canonical protocol
(`BanditPolicy`/`banditMeasure`) and `IsConsistentPolicy` are reused
unchanged. Also provides the Ch 25 objects: suboptimality gaps
`Δ_a = max_{a'} ⟨a' − a, θ⟩` (`linearArmGap`), the expected design matrix
`Ḡ_n = E[∑_{t=1}^n A_t A_tᵀ] = ∑_j E[T_j(n)] (arms j)(arms j)ᵀ`
(`linearBanditExpectedDesign`), the allocation design matrix
`H_α = ∑_a α(a) a aᵀ` (`linearAllocationMatrix`), and the value
`c(𝒜, θ) = inf { ∑_a α(a) Δ_a : α ≥ 0, ‖a‖²_{H_α⁻¹} ≤ Δ_a²/2 ∀a with Δ_a > 0 }`
of the allocation program of Corollary 25.2 (`linearBanditAllocationValue`).

JUNK-VALUE GUARD: Mathlib's matrix inverse is `0` on singular matrices, so a
singular `H_α` would make the constraint `‖a‖²_{H_α⁻¹} ≤ Δ_a²/2` trivially
satisfiable by tiny allocations and could make the Lean `c(𝒜, θ)` strictly
smaller than the book's, falsifying the lower bound. The allocation set is
therefore restricted to `(linearAllocationMatrix arms α).PosDef`: for singular
`H_α` the true `‖a‖²_{H_α⁻¹}` is `+∞` for `a` outside the range of `H_α`, so
the book's constraint fails for a spanning action set; the `PosDef`
restriction is the faithful reading (same convention as `IsGOptimalDesign`).

Conventions match `Def_SelfNormalizedProcess`: vectors are plain
`Fin d → ℝ`, quadratic forms `x ⬝ᵥ M *ᵥ x`, outer products `vecMulVec`.
-/

open Matrix MeasureTheory ProbabilityTheory

namespace BanditAlgorithm

/-- A history of `n` completed linear bandit rounds: the sequence
`(A_1, X_1), …, (A_n, X_n)` of (action, reward) pairs (L&S p.288). -/
abbrev LinearBanditHistory (d n : ℕ) := Fin n → (Fin d → ℝ) × ℝ

/-- A linear bandit policy (L&S Ch 24): for each round, a Markov kernel from
the observed history to a distribution over the action played next in `ℝ^d`.
Membership of the played actions in an action set `𝒜` is the separate
predicate `IsSupportedLinearPolicy`. -/
structure LinearBanditPolicy (d : ℕ) where
  /-- The conditional distribution of the action played in round `n + 1`
  given the history of the first `n` rounds. -/
  select : (n : ℕ) → Kernel (LinearBanditHistory d n) (Fin d → ℝ)
  /-- Each round's selection kernel is a Markov kernel. -/
  markov : ∀ n, IsMarkovKernel (select n)

attribute [instance] LinearBanditPolicy.markov

/-- The policy `π` only plays actions in the action set `𝒜`: every selection
kernel puts no mass outside `𝒜`. Hypothesis of the Ch 24 lower bounds
(`𝒜 = [−1,1]^d` or the unit ball). -/
def IsSupportedLinearPolicy {d : ℕ} (𝒜 : Set (Fin d → ℝ))
    (π : LinearBanditPolicy d) : Prop :=
  ∀ (n : ℕ) (h : LinearBanditHistory d n), π.select n h 𝒜ᶜ = 0

/-- Appending the round `(A, ⟨A, θ⟩ + η)` to a linear bandit history is
measurable (in the history, the action `A` and the noise `η` jointly). -/
lemma measurable_linearBanditHistorySnoc {d n : ℕ} (θ : Fin d → ℝ) :
    Measurable (fun p : (LinearBanditHistory d n × (Fin d → ℝ)) × ℝ ↦
      Fin.snoc (α := fun _ ↦ (Fin d → ℝ) × ℝ) p.1.1 (p.1.2, p.1.2 ⬝ᵥ θ + p.2)) := by
  rw [measurable_pi_iff]
  intro t
  by_cases ht : (t : ℕ) < n
  · have : (fun p : (LinearBanditHistory d n × (Fin d → ℝ)) × ℝ ↦
        Fin.snoc (α := fun _ ↦ (Fin d → ℝ) × ℝ) p.1.1 (p.1.2, p.1.2 ⬝ᵥ θ + p.2) t) =
        fun p ↦ p.1.1 (Fin.castLT t ht) := by
      funext p
      simp [Fin.snoc, ht]
    rw [this]
    exact (measurable_pi_apply _).comp (measurable_fst.comp measurable_fst)
  · have : (fun p : (LinearBanditHistory d n × (Fin d → ℝ)) × ℝ ↦
        Fin.snoc (α := fun _ ↦ (Fin d → ℝ) × ℝ) p.1.1 (p.1.2, p.1.2 ⬝ᵥ θ + p.2) t) =
        fun p ↦ (p.1.2, p.1.2 ⬝ᵥ θ + p.2) := by
      funext p
      simp [Fin.snoc, ht]
    rw [this]
    refine Measurable.prodMk (measurable_snd.comp measurable_fst) ?_
    refine Measurable.add ?_ measurable_snd
    show Measurable fun p : (LinearBanditHistory d n × (Fin d → ℝ)) × ℝ ↦
      ∑ i, p.1.2 i * θ i
    exact Finset.measurable_sum _ fun i _ ↦
      ((measurable_pi_apply i).comp (measurable_snd.comp measurable_fst)).mul_const _

/-- The canonical linear bandit probability measure `ℙ_θ` (L&S p.288): the
distribution of the history after `n` rounds of the interconnection of policy
`π` with the Gaussian linear bandit of parameter `θ`. Round `n + 1` samples
`A ~ π.select n (history)` and an independent `η ~ 𝒩(0,1)`, then appends
`(A, ⟨A, θ⟩ + η)`. -/
noncomputable def linearBanditMeasure {d : ℕ} (θ : Fin d → ℝ)
    (π : LinearBanditPolicy d) : (n : ℕ) → Measure (LinearBanditHistory d n)
  | 0 => Measure.dirac (fun t ↦ t.elim0)
  | n + 1 =>
      ((((linearBanditMeasure θ π n).compProd (π.select n)).compProd
          (Kernel.const _ (gaussianReal 0 1))).map
        (fun p ↦ Fin.snoc (α := fun _ ↦ (Fin d → ℝ) × ℝ) p.1.1
          (p.1.2, p.1.2 ⬝ᵥ θ + p.2)))

instance linearBanditMeasure.instIsProbabilityMeasure {d : ℕ} (θ : Fin d → ℝ)
    (π : LinearBanditPolicy d) (n : ℕ) :
    IsProbabilityMeasure (linearBanditMeasure θ π n) := by
  induction n with
  | zero => exact Measure.dirac.isProbabilityMeasure
  | succ n ih =>
      rw [linearBanditMeasure]
      haveI := ih
      exact Measure.isProbabilityMeasure_map
        (measurable_linearBanditHistorySnoc θ).aemeasurable

/-- The expected regret `R_n(𝒜, θ) = n max_{a ∈ 𝒜} ⟨a, θ⟩ − E_θ[∑_{t=1}^n X_t]`
of a policy on the Gaussian linear bandit with action set `𝒜` and parameter
`θ` (L&S p.288). Since the noise has mean zero, the reward sum is written in
its noise-free form `∑_t ⟨A_t, θ⟩`. -/
noncomputable def linearBanditExpectedRegret {d : ℕ} (𝒜 : Set (Fin d → ℝ))
    (θ : Fin d → ℝ) (π : LinearBanditPolicy d) (n : ℕ) : ℝ :=
  n * sSup ((fun a ↦ a ⬝ᵥ θ) '' 𝒜) -
    ∫ h, ∑ t, (h t).1 ⬝ᵥ θ ∂(linearBanditMeasure θ π n)

/-- The Gaussian linear bandit with fixed finite action set
`arms : Fin k → Fin d → ℝ` and parameter `θ` (L&S §25.1): the `k`-armed
stochastic bandit whose arm `j` has reward distribution `𝒩(⟨arms j, θ⟩, 1)`.
The canonical protocol (`BanditPolicy`/`banditMeasure`) applies unchanged. -/
noncomputable def gaussianLinearBandit {k d : ℕ} (arms : Fin k → Fin d → ℝ)
    (θ : Fin d → ℝ) : StochasticBandit k :=
  gaussianBandit (fun j ↦ arms j ⬝ᵥ θ)

/-- The suboptimality gap `Δ_a = max_{a' ∈ 𝒜} ⟨a' − a, θ⟩` of the arm `a = arms j`
in the finite-action linear bandit (L&S §25.1). -/
noncomputable def linearArmGap {k d : ℕ} (arms : Fin k → Fin d → ℝ)
    (θ : Fin d → ℝ) (j : Fin k) : ℝ :=
  (⨆ j', arms j' ⬝ᵥ θ) - arms j ⬝ᵥ θ

/-- The expected design matrix `Ḡ_n = E[∑_{t=1}^n A_t A_tᵀ]` of L&S
Theorem 25.1: since the actions lie in the finite set `arms`, it equals
`∑_j E[T_j(n)] (arms j)(arms j)ᵀ` with `T_j(n)` the pull counts under the
canonical bandit measure. -/
noncomputable def linearBanditExpectedDesign {k d : ℕ}
    (arms : Fin k → Fin d → ℝ) (ν : StochasticBandit k) (π : BanditPolicy k)
    (n : ℕ) : Matrix (Fin d) (Fin d) ℝ :=
  ∑ j : Fin k, (∫ h, (armPullCount j h : ℝ) ∂(banditMeasure ν π n)) •
    vecMulVec (arms j) (arms j)

/-- The design matrix `H_α = ∑_{a ∈ 𝒜} α(a) a aᵀ` of an allocation
`α : 𝒜 → [0, ∞)` (L&S Corollary 25.2). -/
noncomputable def linearAllocationMatrix {k d : ℕ}
    (arms : Fin k → Fin d → ℝ) (α : Fin k → ℝ) : Matrix (Fin d) (Fin d) ℝ :=
  ∑ j : Fin k, α j • vecMulVec (arms j) (arms j)

/-- The optimal allocation value `c(𝒜, θ)` of L&S Corollary 25.2:
`inf_{α : 𝒜 → [0,∞)} ∑_a α(a) Δ_a` subject to `‖a‖²_{H_α⁻¹} ≤ Δ_a² / 2` for
every suboptimal arm `a`. The allocations are restricted to those with
`H_α` positive definite: for singular `H_α` the true `‖a‖²_{H_α⁻¹}` is `+∞`
outside the range of `H_α` (so the book's constraint fails for spanning `𝒜`),
while Mathlib's junk inverse `H_α⁻¹ = 0` would make it trivially satisfiable
and falsify the lower bound. -/
noncomputable def linearBanditAllocationValue {k d : ℕ}
    (arms : Fin k → Fin d → ℝ) (θ : Fin d → ℝ) : ℝ :=
  sInf ((fun α : Fin k → ℝ ↦ ∑ j, α j * linearArmGap arms θ j) ''
    {α | (∀ j, 0 ≤ α j) ∧ (linearAllocationMatrix arms α).PosDef ∧
      ∀ j, 0 < linearArmGap arms θ j →
        arms j ⬝ᵥ (linearAllocationMatrix arms α)⁻¹ *ᵥ arms j ≤
          linearArmGap arms θ j ^ 2 / 2})

end BanditAlgorithm


