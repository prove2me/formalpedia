-- Prove2me | Definitions.Def_ModernOnlineLearning_Bandits_Protocol
-- name    : ModernOnlineLearning_Bandits_Protocol
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T02:36:53.813309+00:00
-- url     : https://prove2.me/theorems/83616c1c-70c2-42bf-b0f5-36ba3ad4dae8
-- title:
--   Chapter 9 bandit protocol: finite arm draws, expected loss, pull counts, gaps, and pseudo-regret
-- statement:
--   In a $d$-armed bandit, a path records the selected arm $A_t$ in each round $t=1,\ldots,T$. A policy supplies a probability vector $x_t$ over the arms from the past selected arms and their observed losses. The probability of a complete path is the product of its successive selection probabilities.
--
--   For a fixed loss table $g$, the learner's expected cumulative loss is
--
--   $$\mathbb E\!\left[\sum_{t=1}^{T}g_{t,A_t}\right].$$
--
--   The protocol also defines regret against a fixed arm, the expected pull count $\mathbb E[S_{T,i}]$, the mean gap $\Delta_i=\mu_i-\mu_j$ relative to an optimal arm $j$, and stochastic pseudo-regret $\mathbb E[\sum_t g_{t,A_t}]-T\mu_j$. These objects are shared by Algorithm 9.6 and the chapter's pseudo-regret decomposition.
--
--   **Formalization Note** Arms are `Fin d`; rounds retain the book's indices $1,\ldots,T$. A finite path has an unused coordinate zero fixed to an arbitrary anchor arm. The policy condition requires $x_t$ to be a measurable function of the losses observed before round $t$ (and of the past arms), not merely a measurable random variable that is constant on observation histories; the weaker form would let a non-Borel rule correlate $x_t$ with the current round's losses. The stochastic loss table is sampled independently of the subsequent arm draws, whose conditional law is the product of the policy probabilities.
-- source:
--   Orabona, arXiv:1912.13213v10, §9.1, pp. 151–152; §9.2, p. 157; §9.2.2, p. 160

import Mathlib
set_option autoImplicit false
noncomputable section

namespace ModernOnlineLearning.Bandits

/-- A finite record of arm choices; coordinate zero is unused. -/
abbrev ArmPath (T d : ℕ) := Fin (T + 1) → Fin d

/-- The choice in round `t`, with only rounds `1,...,T` used in statements. -/
def armAt {T d : ℕ} (A : ArmPath T d) (t : ℕ) : Fin d :=
  A ⟨min t T, Nat.lt_succ_of_le (Nat.min_le_right t T)⟩

/-- The book's probability simplex on the arms. -/
def IsSimplex {d : ℕ} (p : Fin d → ℝ) : Prop :=
  (∀ i, 0 ≤ p i) ∧ (∑ i, p i) = 1

/-- Chain-rule mass of a path of algorithmic arm draws. Coordinate zero is fixed to
    `anchor` only to avoid counting the unused round-zero coordinate `d` times. -/
def pathWeight {T d : ℕ} (anchor : Fin d)
    (x : ArmPath T d → ℕ → Fin d → ℝ) (A : ArmPath T d) : ℝ :=
  if A 0 = anchor then
    ∏ t ∈ Finset.Icc 1 T, x A t (armAt A t)
  else 0

/-- Expected cumulative loss under the finite, history-dependent arm-draw law. -/
def expectedLoss {T d : ℕ} (anchor : Fin d) (g : ℕ → Fin d → ℝ)
    (x : ArmPath T d → ℕ → Fin d → ℝ) : ℝ :=
  ∑ A : ArmPath T d, pathWeight anchor x A *
    ∑ t ∈ Finset.Icc 1 T, g t (armAt A t)

/-- Expected regret against one fixed arm for an oblivious loss table. -/
def expectedRegret {T d : ℕ} (anchor : Fin d) (g : ℕ → Fin d → ℝ)
    (x : ArmPath T d → ℕ → Fin d → ℝ) (k : Fin d) : ℝ :=
  ∑ A : ArmPath T d, pathWeight anchor x A *
    ∑ t ∈ Finset.Icc 1 T, (g t (armAt A t) - g t k)

/-- Expected probability of arm `i` in round `t`. -/
def expectedArmProbability {T d : ℕ} (anchor : Fin d)
    (x : ArmPath T d → ℕ → Fin d → ℝ) (t : ℕ) (i : Fin d) : ℝ :=
  ∑ A : ArmPath T d, pathWeight anchor x A * x A t i

/-- Expected number of pulls of arm `i` over the first `T` rounds. -/
def expectedPullCount {T d : ℕ} (anchor : Fin d)
    (x : ArmPath T d → ℕ → Fin d → ℝ) (i : Fin d) : ℝ :=
  ∑ A : ArmPath T d, pathWeight anchor x A *
    ∑ t ∈ Finset.Icc 1 T, if armAt A t = i then (1 : ℝ) else 0

/-- Mean gap relative to a specified optimal arm. -/
def gap {d : ℕ} (μ : Fin d → ℝ) (j i : Fin d) : ℝ := μ i - μ j

/-- A policy uses only earlier arm choices and their observed losses, through a
    measurable rule applied to the observed losses of rounds before `t`. -/
def IsOnlinePolicy {Ω : Type*} [MeasurableSpace Ω] {T d : ℕ}
    (g : Ω → ℕ → Fin d → ℝ)
    (x : Ω → ArmPath T d → ℕ → Fin d → ℝ) : Prop :=
  (∀ ω A t, t ∈ Finset.Icc 1 T → IsSimplex (x ω A t)) ∧
  (∀ A t i, Measurable (fun ω => x ω A t i)) ∧
  (∃ π : ArmPath T d → ℕ → (ℕ → ℝ) → Fin d → ℝ,
    (∀ A t, Measurable (π A t)) ∧
    ∀ ω A t, t ∈ Finset.Icc 1 T →
      x ω A t = π A t (fun s => if s < t then g ω s (armAt A s) else 0)) ∧
  (∀ ω ω' A B t, t ∈ Finset.Icc 1 T →
    (∀ s, s ∈ Finset.Ico 1 t →
      armAt A s = armAt B s ∧
      g ω s (armAt A s) = g ω' s (armAt B s)) →
    x ω A t = x ω' B t)

/-- Pseudo-regret for losses with fixed arm means. -/
def stochasticPseudoRegret {Ω : Type*} [MeasurableSpace Ω]
    {T d : ℕ} (P : MeasureTheory.Measure Ω) (anchor : Fin d)
    (g : Ω → ℕ → Fin d → ℝ)
    (x : Ω → ArmPath T d → ℕ → Fin d → ℝ)
    (μ : Fin d → ℝ) (j : Fin d) : ℝ :=
  (∫ ω, expectedLoss anchor (g ω) (x ω) ∂P) - (T : ℝ) * μ j

/-- The expected number of pulls in a stochastic environment. -/
def stochasticPullCount {Ω : Type*} [MeasurableSpace Ω]
    {T d : ℕ} (P : MeasureTheory.Measure Ω) (anchor : Fin d)
    (x : Ω → ArmPath T d → ℕ → Fin d → ℝ) (i : Fin d) : ℝ :=
  ∫ ω, expectedPullCount anchor (x ω) i ∂P

end ModernOnlineLearning.Bandits


