-- Prove2me | Definitions.Def_LogMeanVar_Complete_Supplement_Equilibrium
-- name    : LogMeanVar_Complete_Supplement_Equilibrium
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T22:58:25.396172+00:00
-- url     : https://prove2.me/theorems/31bb0209-9341-413c-a17c-6dbacec9d8d1
-- title:
--   Definition 1 and (8), pp. 8–10 — conditional rewards, spikes and fixed-target equilibria
-- statement:
--   Conditional nonnegative expectations are computed by increasing bounded truncations, so $+\infty$ is preserved. Conditional means and variances are used only on the domain of finite conditional terminal second moments. The reward is
--
--   $$J_t(R)=\mathbb E_t[R_T]-\frac{\gamma_t}{2}\operatorname{Var}_t(R_T).$$
--
--   A constant spike uses $v$ on $[t,t+h)$ and then returns to the original feedback policy. A complete response family supplies an admissible SDE solution whenever one exists; it cannot omit an admissible competitor by choosing an invalid response. Equilibrium uses the pointwise almost-sure epsilon form of the nonnegative lower limit of lost reward divided by $h$.
--
--   For a reference return $R$, define its fixed adapted target $\alpha_s=(\mathbb E_s[R_T]-R_s)/(T-s)$. A competitor $S$ meets that target if
--
--   $$\frac{\mathbb E_s[S_T]-S_s}{T-s}\ge\alpha_s\quad\text{for every }s\in[t,T).$$
--
--   The target equilibrium substitutes $-\operatorname{Var}_t$ for $J_t$. The target is always constructed from the reference return, never from a competitor. These definitions retain random, time-varying preference and every admissible constant spike.
--
--   **Formalization Note** Conditional moments use fixed common versions. Initial values of response paths are normalized exactly. Finite conditional second moments make the criterion meaningful; unconditional square integrability is not imposed. Equilibria are described along arbitrary reference trajectories and universally over complete choices of responses, so no uniqueness or Markov assumption on the SDE is needed. The target test is pointwise along the trajectory, including every future time; all almost-surely feasible competitors remain covered.
--
--   Differences from the source:
--   - reading: conditional rewards for admissible policies → actual SDE response trajectories with finite conditional second moments and fixed common conditional versions; reason: the finite mean–variance reward needs finite conditional moments; no unconditional L² or uniqueness premise is imposed
--   - encoding: the liminf equilibrium test and the fixed-target feasible class → pointwise almost-sure epsilon tests with the induced target fixed at every future time; reason: preserves the lower-limit sign and every future target constraint without a default-valued real infimum
--   - generalization: target-feasible competitors satisfying the target constraints almost surely → the target-loss inequality is also tested on each feasible path of a globally admissible spike; reason: this stronger predicate includes every source-feasible competitor and is the explicit conclusion of theorem_1
-- source:
--   Dai, Jin, Kou, Xu, A Dynamic Mean-Variance Analysis for Log Returns, SSRN 3437268 (version of Aug 2019), pp. 8–10, (7), Definition 1, (8), Theorem 1

import Definitions.Def_LogMeanVar_Complete_Supplement_Model

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology
set_option autoImplicit false

/-! Dai, Jin, Kou, Xu, A Dynamic Mean-Variance Analysis for Log Returns,
SSRN 3437268 (version of Aug 2019), pp.8–10, (7), Definition 1, (8), Theorem 1.
Formalization Note: fixed conditional versions, conditional finite second moments,
complete actual spike-response families, and pointwise epsilon limits make the
source's well-defined conditional criterion explicit without unconditional L². -/
namespace LogMeanVar.Complete.Supplement

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

noncomputable def meanCE (P : Measure Ω) (G : MeasurableSpace Ω)
    (U : Ω → ℝ) (ω : Ω) : ℝ :=
  (@lowerCE Ω mΩ P G (fun a => ENNReal.ofReal (U a)) ω).toReal -
    (@lowerCE Ω mΩ P G (fun a => ENNReal.ofReal (-U a)) ω).toReal

noncomputable def varianceCE (P : Measure Ω) (G : MeasurableSpace Ω)
    (U : Ω → ℝ) (ω : Ω) : ℝ :=
  (@lowerCE Ω mΩ P G (fun a => ENNReal.ofReal (U a ^ 2)) ω).toReal - @meanCE Ω mΩ P G U ω ^ 2

/-- The moments actually used must be finite; no real integral or toReal of infinity
is used to certify admissibility. This is the well-definedness convention implicit
in a finite mean–variance criterion, not a bound on the coefficients. -/
def FiniteConditionalSecond (P : Measure Ω) (F : Filtration ℝ≥0 mΩ)
    (t : ℝ) (U : Ω → ℝ) : Prop :=
  AEStronglyMeasurable U P ∧
    ∀ᵐ ω ∂P, lowerCE P (F t.toNNReal) (fun a => ENNReal.ofReal (U a ^ 2)) ω < ⊤

/-- A solution with the source's conditional A_t exposure condition, plus finite
conditional terminal second moments at each future time. No SDE uniqueness is
assumed, and no equilibrium/target identity is hidden in this definition. -/
def GoodReturn (M : Model) (P : Measure Ω) (F : Filtration ℝ≥0 mΩ)
    (B : ℝ≥0 → Ω → ℝ) (X : ℝ → Ω → ℝ) (π : Policy)
    (t : ℝ) (ξ : Ω → ℝ) (R : ℝ → Ω → ℝ) : Prop :=
  IsReturn M P F B X π t ξ R ∧
  (∀ ω, R t ω = ξ ω) ∧
  ∀ s ∈ Set.Ico t M.T, FiniteConditionalSecond P F s (R M.T) ∧
    PrintedAdmissible M P F X R π s

noncomputable def spike (π : Policy) (t h v : ℝ) : Policy := by
  classical
  exact fun s y x => if s ∈ Set.Ico t (t+h) then v else π s y x

abbrev Responses (Ω : Type*) := ℝ → ℝ → ℝ → ℝ → Ω → ℝ

/-- The actual SDE solution of a spike restarted at the reference current wealth.
A response family is a choice of trajectories, not a supplied reward formula. -/
def GoodResponse (M : Model) (P : Measure Ω) (F : Filtration ℝ≥0 mΩ)
    (B : ℝ≥0 → Ω → ℝ) (X R : ℝ → Ω → ℝ) (π : Policy) (Q : Responses Ω)
    (t h v : ℝ) : Prop :=
  GoodReturn M P F B X (spike π t h v) t (R t) (Q t h v)

/-- Completeness of the chosen response family: whenever an admissible solution
of a constant spike exists, Q actually supplies one. Thus a bad choice of Q cannot
remove admissible competitors from the equilibrium test. -/
def RealizesResponses (M : Model) (P : Measure Ω) (F : Filtration ℝ≥0 mΩ)
    (B : ℝ≥0 → Ω → ℝ) (X R : ℝ → Ω → ℝ) (π : Policy) (Q : Responses Ω) : Prop :=
  ∀ t ∈ Set.Ico 0 M.T, ∀ h > (0 : ℝ), ∀ v : ℝ,
    (∃ S : ℝ → Ω → ℝ, GoodReturn M P F B X (spike π t h v) t (R t) S) →
      GoodResponse M P F B X R π Q t h v

noncomputable def reward (M : Model) (P : Measure Ω) (F : Filtration ℝ≥0 mΩ)
    (γ : ℝ → Ω → ℝ) (R : ℝ → Ω → ℝ) (t : ℝ) (ω : Ω) : ℝ :=
  meanCE P (F t.toNNReal) (R M.T) ω -
    γ t ω / 2 * varianceCE P (F t.toNNReal) (R M.T) ω

/-- Definition 1, p.9, along a reference solution, for every admissible spike.
Formalization Note: conditional moments use fixed common versions. The ε-form is
pointwise a.s., for every v, and tests only actual admissible SDE responses.
Theorem 1 is universal over response families; it is not restricted to deterministic
policies or coefficients. Random positive adapted γ is retained. -/
def IsEquilibriumAlong (M : Model) (P : Measure Ω) (F : Filtration ℝ≥0 mΩ)
    (B : ℝ≥0 → Ω → ℝ) (X R : ℝ → Ω → ℝ) (π : Policy)
    (γ : ℝ → Ω → ℝ) (Q : Responses Ω) : Prop :=
  GoodReturn M P F B X π 0 (R 0) R ∧
  RealizesResponses M P F B X R π Q ∧
  ∀ t ∈ Set.Ico 0 M.T, ∀ v : ℝ, ∀ᵐ ω ∂P, ∀ ε > (0 : ℝ),
    ∀ᶠ h in 𝓝[>] (0 : ℝ), GoodResponse M P F B X R π Q t h v →
      -ε ≤ (reward M P F γ R t ω - reward M P F γ (Q t h v) t ω) / h

/-- The target is constructed ONCE from the reference policy's actual return,
not from a competitor. This is exactly the displayed target in Theorem 1, p.10. -/
noncomputable def inducedTarget (M : Model) (P : Measure Ω) (F : Filtration ℝ≥0 mΩ)
    (R : ℝ → Ω → ℝ) (s : ℝ) (ω : Ω) : ℝ :=
  (meanCE P (F s.toNNReal) (R M.T) ω - R s ω) / (M.T-s)

/-- Abar_t of p.10, including every s in [t,T), on common conditional versions.
The target α is fixed; it is not recomputed from S. -/
def MeetsTarget (M : Model) (P : Measure Ω) (F : Filtration ℝ≥0 mΩ)
    (α : ℝ → Ω → ℝ) (S : ℝ → Ω → ℝ) (t : ℝ) (ω : Ω) : Prop :=
  ∀ s ∈ Set.Ico t M.T,
    α s ω ≤ (meanCE P (F s.toNNReal) (S M.T) ω - S s ω) / (M.T-s)

/-- Equilibrium for (8): admissible baseline, fixed-target feasibility at EVERY
future time, and local optimality for reward -Var, on every target-feasible path.
The pointwise feasibility restriction is at least as strong a test as requiring
competitors to be feasible a.s.; it does not discard any a.s.-feasible competitor. -/
def IsTargetEquilibriumAlong (M : Model) (P : Measure Ω) (F : Filtration ℝ≥0 mΩ)
    (B : ℝ≥0 → Ω → ℝ) (X R : ℝ → Ω → ℝ) (π : Policy) (Q : Responses Ω)
    (α : ℝ → Ω → ℝ) : Prop :=
  GoodReturn M P F B X π 0 (R 0) R ∧
  RealizesResponses M P F B X R π Q ∧
  (∀ᵐ ω ∂P, MeetsTarget M P F α R 0 ω) ∧
  ∀ t ∈ Set.Ico 0 M.T, ∀ v : ℝ, ∀ᵐ ω ∂P, ∀ ε > (0 : ℝ),
    ∀ᶠ h in 𝓝[>] (0 : ℝ),
      GoodResponse M P F B X R π Q t h v → MeetsTarget M P F α (Q t h v) t ω →
      -ε ≤ ((-varianceCE P (F t.toNNReal) (R M.T) ω) -
        (-varianceCE P (F t.toNNReal) (Q t h v M.T) ω)) / h

end LogMeanVar.Complete.Supplement


