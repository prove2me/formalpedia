-- Prove2me | Definitions.Def_CalibeatBandit_hard_tree_environment
-- name    : CalibeatBandit_hard_tree_environment
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-23T17:38:59.153801+00:00
-- url     : https://prove2.me/theorems/5583d94f-cd07-4ef6-ab7b-49d62c4ab6e9
-- title:
--   Hard tree environment of the bandit swap-regret lower bound (§4): tree actions, bonus probabilities, reward tape
-- statement:
--   These definitions set up the random reward environment of the swap-regret lower bound (Theorem 4.1 of *Calibeating Bandit Advice*, §4), in the form used by the Lean proof: a complete binary tree of depth $h$, an action set built on it, the bonus probabilities attached to the actions, and the reward sequence obtained from independent uniform draws.
--
--   **Tree and actions.** A node of the complete binary tree of depth $h$ is a pair $v=(d,j)$ with depth $d\in\{0,\dots,h\}$ and index $j<2^d$ (`TreeNode h`). The leaves below $v$ are those with index in $[\mathrm{first}(v),\mathrm{last}(v))$, where $\mathrm{first}(v)=j\,2^{h-d}$ and $\mathrm{last}(v)=(j+1)2^{h-d}$; $\mathrm{mid}(v)$ is the first leaf of the right half. A node is *active* for a leaf $\ell$ if $\ell$ lies below it. The action set (`TreeAction h M U`) consists of two actions $(v,\text{side})$ for every node, $M$ auxiliary actions and $U$ further actions that never receive a bonus. The number of levels is $H=h+1$ (`treeHeight`).
--
--   **Bonus probabilities.** Fix an active leaf $\ell$, a hidden coin $c(v)\in\{0,1\}$ for every node, a leaf coin $b$ and a selected auxiliary action $j^*$. The bonus probability $u(a)$ of an action $a$ (`treeBonusProb`) is
--
--   $$u(v,\text{side})=\begin{cases}\mathbf 1[\text{side}=b]&v\text{ active, }v\text{ a leaf},\\[2pt]\dfrac{d+1}{2H}\,\mathbf 1[\text{side}=g(v)]&v\text{ active, of depth }d<h,\\[4pt]0&v\text{ not active},\end{cases}\qquad u(j)=\mathbf 1[j=j^*],$$
--
--   where the good side $g(v)$ is the left one if $\ell<\mathrm{mid}(v)$ and the coin $c(v)$ otherwise, and $u=0$ on the $U$ further actions.
--
--   **Rewards.** With a base draw $z\in[0,1]$ and a bonus indicator, the reward is (`bonusReward`)
--
--   $$\frac18+\frac z8+\frac\eta8\,z(1-z)\,\mathbf 1[\text{bonus}],$$
--
--   and action $a$ receives the bonus when its threshold draw $U_a\in[0,1)$ is below $u(a)$ (`treeReward`, `boundedRoundReward`). Draws outside $[0,1]$, respectively $[0,1)$, are replaced by $0$ (`supportedBase`, `supportedThreshold`), so the reward is defined and lies in $[0,1]$ for every input when $0\le\eta\le1$.
--
--   **The randomness.** A reward tape of length $t$ (`RewardTape N t`) records, for each of $t$ rounds, a base draw and one threshold draw per action. Its law (`rewardTapeLaw`) makes all draws independent, the base draws uniform on $[0,1]$ and the threshold draws uniform on $[0,1)$. The tables (`TreeTables h M T`) are a leaf coin for every round, a coin for every node and a selected auxiliary action for every leaf; they are uniformly distributed (`finiteTableLaw`). An environment (`TreeEnvironment h M N T`) is a pair of tables and a tape of length $T$, and `treeEnvironmentLaw` is the product law.
--
--   **Schedule.** The horizon is divided into consecutive periods of length $r$; in round $t$ the active leaf is $\min(\lfloor t/r\rfloor,2^h-1)$ (`blockLeaf`). Given a bijection $e$ between the $N$ actions of the learner and the tree actions, `tableBonuses` is the resulting table $u_t(i)$ of bonus probabilities and `treeEnvironmentReward` is the realized reward $y_t(i)$ of action $i$ in round $t$ (rewards after the horizon use the draw $0$).
--
--   **The learner's run.** For a deterministic bandit policy `pick`, which maps the rewards observed so far to the next action, `rawTapeHistory` is its feedback history against a tape and `treeEnvironmentAction` is the action it plays in round $t$ of the environment (a fixed anchor action after the horizon).
--
--   **Scales.** The construction uses $K=16\cdot2^h$ actions (`treeActionBudget`), periods of length $r=16K^3$ (`treePeriodLength`), hence horizon $2^hr=K^4$, and bonus scale $\eta=1/(1000KH)$ (`treeBonusScale`).
--
--   These are the objects in which the hard instance of Theorem 4.1 is stated. The pricing lower bound (Theorem 5.2) embeds the same rewards in demand curves, so both proofs import them.
-- source:
--   Hartline, Wang, Wu, Calibeating Bandit Advice (STOC 2027 submission 1457), https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1457.pdf, §4, pp. 13–21: the construction (pp. 13–15) and the proof of Theorem 4.1 (pp. 20–21). Definitions of jasonhartline's accepted Lean proof of CalibeatBandit.theorem_4_1 (submission 0ae8d87e-4337-4d82-8722-8eeded8a7691).

import Mathlib
import Definitions.Def_CalibeatBandit_lower_bound_models

section

set_option autoImplicit false

namespace CalibeatBandit

open Set MeasureTheory

/-- A level and an index within that level in a complete binary tree.
Depth zero denotes the root, and depth h denotes a leaf. -/
abbrev TreeNode (h : ℕ) := Σ d : Fin (h + 1), Fin (2 ^ (d : ℕ))

namespace TreeNode

def first {h : ℕ} (v : TreeNode h) : ℕ := (v.2 : ℕ) * 2 ^ (h - (v.1 : ℕ))
def last {h : ℕ} (v : TreeNode h) : ℕ := ((v.2 : ℕ) + 1) * 2 ^ (h - (v.1 : ℕ))
def mid {h : ℕ} (v : TreeNode h) : ℕ := v.first + 2 ^ (h - ((v.1 : ℕ) + 1))

def active {h : ℕ} (v : TreeNode h) (l : Fin (2 ^ h)) : Prop :=
  v.first ≤ (l : ℕ) ∧ (l : ℕ) < v.last

instance {h : ℕ} (v : TreeNode h) (l : Fin (2 ^ h)) : Decidable (v.active l) :=
  inferInstanceAs (Decidable (_ ≤ _ ∧ _ < _))

end TreeNode

/-- The construction uses two actions per node, auxiliary actions and
possibly additional actions with zero bonus probability. -/
abbrev TreeAction (h M U : ℕ) := (TreeNode h × Bool) ⊕ (Fin M ⊕ Fin U)

def treeHeight (h : ℕ) : ℝ := (h : ℝ) + 1

/-- Probability of a bonus for the indicated action. Here the active leaf
and the auxiliary choice are fixed for the period, and the leaf coin is fresh. -/
noncomputable def treeBonusProb {h M U : ℕ} (leaf : Fin (2 ^ h))
    (coin : TreeNode h → Bool) (leafCoin : Bool) (selected : Fin M) :
    TreeAction h M U → ℝ
  | .inl (v, side) =>
    if v.active leaf then
      if (v.1 : ℕ) = h then
        if side = leafCoin then 1 else 0
      else
        if side = (if (leaf : ℕ) < v.mid then false else coin v) then
          ((v.1 : ℕ) + 1 : ℝ) / (2 * treeHeight h)
        else 0
    else 0
  | .inr (.inl j) => if j = selected then 1 else 0
  | .inr (.inr _) => 0

noncomputable def bonusReward (η : ℝ) (z : Icc (0 : ℝ) 1) (hit : Bool) : ℝ :=
  1 / 8 + (z : ℝ) / 8 + (η / 8 * (z : ℝ) * (1 - (z : ℝ))) * (if hit then 1 else 0)

/-- Realized rewards in the tree construction. The uniform draws for the
thresholds take values in `[0, 1)`, so probability one gives a bonus in
every realization. -/
noncomputable def treeReward {h M U : ℕ}
    (η : ℝ) (leaf : Fin (2 ^ h)) (coin : TreeNode h → Bool) (leafCoin : Bool)
    (selected : Fin M) (z : Icc (0 : ℝ) 1) (draw : TreeAction h M U → Ico (0 : ℝ) 1)
    (a : TreeAction h M U) : ℝ :=
  bonusReward η z (decide ((draw a : ℝ) < treeBonusProb leaf coin leafCoin selected a))

end CalibeatBandit

end

section

set_option autoImplicit false

namespace CalibeatBandit

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

/-- Primitive independent draws through the preceding round. -/
def RewardTape (N : ℕ) : ℕ → Type
  | 0 => Unit
  | t + 1 => RewardTape N t × (ℝ × (Fin N → ℝ))

instance rewardTapeMeasurable (N t : ℕ) : MeasurableSpace (RewardTape N t) :=
  match t with
  | 0 => inferInstanceAs (MeasurableSpace Unit)
  | t + 1 => @MeasurableSpace.prod (RewardTape N t) _ (rewardTapeMeasurable N t) inferInstance

noncomputable def roundDrawLaw (N : ℕ) : Measure (ℝ × (Fin N → ℝ)) :=
  (volume.restrict (Icc (0 : ℝ) 1)).prod
    (Measure.pi fun _ : Fin N => volume.restrict (Ico (0 : ℝ) 1))

instance roundDrawLaw_probability (N : ℕ) : IsProbabilityMeasure (roundDrawLaw N) := by
  have _ : IsProbabilityMeasure (volume.restrict (Icc (0 : ℝ) 1)) := ⟨by simp [Real.volume_Icc]⟩
  have _ : IsProbabilityMeasure (volume.restrict (Ico (0 : ℝ) 1)) := ⟨by simp [Real.volume_Ico]⟩
  unfold roundDrawLaw
  infer_instance

noncomputable def rewardTapeLaw (N : ℕ) : (t : ℕ) → Measure (RewardTape N t)
  | 0 => Measure.dirac ()
  | t + 1 => (rewardTapeLaw N t).prod (roundDrawLaw N)

instance rewardTapeLaw_probability (N t : ℕ) : IsProbabilityMeasure (rewardTapeLaw N t) := by
  induction t with
  | zero => change IsProbabilityMeasure (Measure.dirac ()); infer_instance
  | succ t ih =>
    let _ := ih
    change IsProbabilityMeasure ((rewardTapeLaw N t).prod (roundDrawLaw N))
    infer_instance

end CalibeatBandit

end

section

set_option autoImplicit false

namespace CalibeatBandit

open MeasureTheory Set

/-- Restrict a reward tape to its first r rounds. -/
def rewardTapePrefix (N : ℕ) {r t : ℕ} (h : r ≤ t) : RewardTape N t → RewardTape N r :=
  Nat.leRec (motive := fun t _ => RewardTape N t → RewardTape N r) id
    (fun {_} _ p => p ∘ Prod.fst) h

open scoped ENNReal

/-- Outside the support of the base draw use zero. This lets boundedness
hold everywhere while preserving the probability law of each reward. -/
noncomputable def supportedBase (x : ℝ) : Icc (0 : ℝ) 1 :=
  if h : x ∈ Icc (0 : ℝ) 1 then ⟨x, h⟩ else ⟨0, by simp⟩

/-- Outside the support of a threshold draw use zero. -/
noncomputable def supportedThreshold (x : ℝ) : Ico (0 : ℝ) 1 :=
  if h : x ∈ Ico (0 : ℝ) 1 then ⟨x, h⟩ else ⟨0, by simp⟩

/-- A globally bounded realization of the reward from one round. -/
noncomputable def boundedRoundReward {N : ℕ} (η u : ℝ) (i : Fin N)
    (d : ℝ × (Fin N → ℝ)) : ℝ :=
  bonusReward η (supportedBase d.1) (decide ((supportedThreshold (d.2 i) : ℝ) < u))

end CalibeatBandit

end

section

set_option autoImplicit false

namespace CalibeatBandit

open MeasureTheory Set

/-- Run a learner against the bounded reward tape, storing raw observations. -/
noncomputable def rawTapeHistory {N : ℕ} (η : ℝ) (u : ℕ → Fin N → ℝ)
    (pick : (t : ℕ) → FeedbackHistory t → Fin N) :
    (t : ℕ) → RewardTape N t → FeedbackHistory t
  | 0, _ => ()
  | t + 1, p =>
    let past := rawTapeHistory η u pick t p.1
    let i := pick t past
    (past, boundedRoundReward η (u t i) i p.2)

/-- The table of bonus probabilities with the tree's active leaf and coins. -/
noncomputable def scheduledBonuses {h M U N : ℕ} (e : Fin N ≃ TreeAction h M U)
    (active : ℕ → Fin (2 ^ h)) (coin : TreeNode h → Bool) (leafCoin : ℕ → Bool)
    (selected : Fin (2 ^ h) → Fin M) (t : ℕ) (i : Fin N) : ℝ :=
  treeBonusProb (active t) coin (leafCoin t) (selected (active t)) (e i)

end CalibeatBandit

end

section

set_option autoImplicit false

namespace CalibeatBandit

open MeasureTheory Set
open scoped ENNReal

/-- The active periods are consecutive equally long blocks. Clamp after
the horizon so the active leaf is monotone at all times. -/
def blockLeaf (h r t : ℕ) : Fin (2 ^ h) :=
  ⟨min (t / r) (2 ^ h - 1), lt_of_le_of_lt (min_le_right _ _) (by
    have hp : 0 < (2 : ℕ) ^ h := by positivity
    omega)⟩

/-- Uniform distribution on a finite table. -/
noncomputable def finiteTableLaw (A : Type*) [Fintype A] [MeasurableSpace A]
    [MeasurableSingletonClass A] : Measure A :=
  (Fintype.card A : ℝ≥0∞)⁻¹ • Measure.count

instance finiteTableLaw_probability (A : Type*) [Fintype A] [Nonempty A] [MeasurableSpace A]
    [MeasurableSingletonClass A] : IsProbabilityMeasure (finiteTableLaw A) := by
  refine ⟨?_⟩
  rw [finiteTableLaw, Measure.smul_apply, smul_eq_mul, ← (Finset.coe_univ : (↑(Finset.univ : Finset A) : Set A) = Set.univ),
    Measure.count_apply_finset, Finset.card_univ]
  exact ENNReal.inv_mul_cancel (by exact_mod_cast (Fintype.card_ne_zero (α := A))) (by simp)

end CalibeatBandit

end

section

set_option autoImplicit false

namespace CalibeatBandit

open MeasureTheory Set

/-- First choose the leaf coins, node coins, and selected actions, then
independently sample the tape of base and threshold draws. -/
abbrev TreeTables (h M T : ℕ) := (Fin T → Bool) × (TreeNode h → Bool) × (Fin (2 ^ h) → Fin M)
abbrev TreeEnvironment (h M N T : ℕ) := TreeTables h M T × RewardTape N T

noncomputable def treeEnvironmentLaw (h M N T : ℕ) : Measure (TreeEnvironment h M N T) :=
  (finiteTableLaw (TreeTables h M T)).prod (rewardTapeLaw N T)

instance treeEnvironmentLaw_probability (h M N T : ℕ) [Nonempty (Fin M)] :
    IsProbabilityMeasure (treeEnvironmentLaw h M N T) := by
  unfold treeEnvironmentLaw
  infer_instance

def tableLeafCoin {T : ℕ} (b : Fin T → Bool) (t : ℕ) : Bool :=
  if ht : t < T then b ⟨t, ht⟩ else false

noncomputable def tableBonuses {h M U N T : ℕ} (e : Fin N ≃ TreeAction h M U)
    (active : ℕ → Fin (2 ^ h)) (table : TreeTables h M T) : ℕ → Fin N → ℝ :=
  scheduledBonuses e active table.2.1 (tableLeafCoin table.1) table.2.2

/-- Extract the fresh draw in the indicated round. The zero extension is
only queried beyond the experiment's horizon. -/
noncomputable def tapeDraw {N T : ℕ} (tape : RewardTape N T) (t : ℕ) : ℝ × (Fin N → ℝ) :=
  if ht : t < T then (rewardTapePrefix N (Nat.succ_le_of_lt ht) tape).2 else (0, fun _ => 0)

noncomputable def treeEnvironmentReward {h M U N T : ℕ} (e : Fin N ≃ TreeAction h M U)
    (active : ℕ → Fin (2 ^ h)) (η : ℝ) (env : TreeEnvironment h M N T) (t : ℕ) (i : Fin N) : ℝ :=
  boundedRoundReward η (tableBonuses e active env.1 t i) i (tapeDraw env.2 t)

noncomputable def treeEnvironmentAction {h M U N T : ℕ} (e : Fin N ≃ TreeAction h M U)
    (active : ℕ → Fin (2 ^ h)) (η : ℝ) (pick : (t : ℕ) → FeedbackHistory t → Fin N)
    (anchor : Fin N) (env : TreeEnvironment h M N T) (t : ℕ) : Fin N :=
  if ht : t < T then pick t (rawTapeHistory η (tableBonuses e active env.1) pick t
    (rewardTapePrefix N ht.le env.2)) else anchor

end CalibeatBandit

end

section

set_option autoImplicit false

namespace CalibeatBandit

open MeasureTheory Set Filter

/-- The dyadic action budget and period length of the hard construction. -/
def treeActionBudget (h : ℕ) : ℕ := 16 * 2 ^ h
def treePeriodLength (h : ℕ) : ℕ := 16 * treeActionBudget h ^ 3

noncomputable def treeBonusScale (h : ℕ) : ℝ := 1 / (1000 * treeActionBudget h * treeHeight h)

end CalibeatBandit

end


