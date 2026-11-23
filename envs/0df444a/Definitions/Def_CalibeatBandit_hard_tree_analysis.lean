-- Prove2me | Definitions.Def_CalibeatBandit_hard_tree_analysis
-- name    : CalibeatBandit_hard_tree_analysis
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-23T18:35:04.784795+00:00
-- url     : https://prove2.me/theorems/b9442449-f8e3-46e1-9ecf-ebf87bd2f0e9
-- title:
--   Quantities of the swap-regret lower bound (§4): bonus transform $h_\eta$, swap gains $\Gamma_{i\to j}$ and $G_i$, play indicators, period counts
-- statement:
--   These definitions name the quantities in which the lemmas of §4 of *Calibeating Bandit Advice* (the swap-regret lower bound) are stated. They build on the hard tree environment (tree actions, bonus probabilities, reward tape).
--
--   **Bonus transform.** $h_\eta(z)=z+\eta z(1-z)$ (`bonusTransform`). On the normalized scale $\hat y=8y-1$ a reward without bonus is $Z$ and a reward with bonus is $h_\eta(Z)$; `boundedObservation` is this normalized reward and `boundedTapeTranscript` is the learner's feedback history on the normalized scale.
--
--   **Swap gains.** For sequences $q_t,u_t\in\mathbb R^K$ (play probabilities and bonus probabilities) and a horizon $T$,
--
--   $$\Gamma_{i\to j}=\sum_{t<T}q_t(i)\big(u_t(j)-u_t(i)\big),\qquad G_i=\max_{j}\Gamma_{i\to j}$$
--
--   (`swapGain`, `bestSwapGain`). Since $\Gamma_{i\to i}=0$, $G_i\ge0$, and $\sum_iG_i$ is the pseudo swap regret of $q$ against $u$.
--
--   **Counting plays in a period.** For a deterministic learner `pick`, a bonus table $u$ and a tape of $r$ rounds, `periodHits` is the number of the $r$ rounds in which the learner plays a given action $j$; here the learner is fed the normalized observations.
--
--   **Play indicators.** `treePlayProbability` is the indicator $q_t(i)$ that a deterministic learner, whose actions are tree actions, plays action $i$ in round $t$ against the rewards determined by the node coins, the leaf coins, the selected auxiliary actions and the draws. `treeEnvironmentPlay` is the same indicator vector for a learner run in an environment (hidden tables and tape). For a randomized learner these indicators are averaged over the seed, and over the hidden coins, to give the conditional play probabilities of the paper.
--
--   **Auxiliary actions.** `treeAuxAction` is the embedding $j\mapsto s_j$ of the $M$ auxiliary actions into the learner's $N$ actions.
-- source:
--   Hartline, Wang, Wu, Calibeating Bandit Advice (STOC 2027 submission 1457), https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1457.pdf, §4, pp. 14–18 (the quantities $\Gamma_{i\to j}$, $G_i$, $Q_i$ on p. 14; the transformed observation on p. 17). Definitions of jasonhartline's accepted Lean proof of CalibeatBandit.theorem_4_1 (submission 0ae8d87e-4337-4d82-8722-8eeded8a7691).

import Mathlib
import Definitions.Def_CalibeatBandit_lower_bound_models
import Definitions.Def_CalibeatBandit_IsColStochastic
import Definitions.Def_CalibeatBandit_fixedPointSol
import Definitions.Def_CalibeatBandit_calibeatPolicy
import Definitions.Def_CalibeatBandit_pseudoSwapRegret
import Definitions.Def_CalibeatBandit_swapRegret
import Definitions.Def_CalibeatBandit_hard_tree_environment

section

set_option autoImplicit false

open Filter MeasureTheory Set InformationTheory
open scoped Interval ENNReal

namespace CalibeatBandit

def bonusTransform (η z : ℝ) : ℝ := z + η * z * (1 - z)

end CalibeatBandit

end

section

set_option autoImplicit false

open Filter MeasureTheory Matrix
open scoped BigOperators

namespace CalibeatBandit

def swapGain {K : ℕ} (T : ℕ) (q u : ℕ → Fin K → ℝ) (i j : Fin K) : ℝ :=
  ∑ t ∈ Finset.range T, q t i * (u t j - u t i)

def bestSwapGain {K : ℕ} (T : ℕ) (q u : ℕ → Fin K → ℝ) (i : Fin K) : ℝ :=
  Finset.univ.sup' ⟨i, Finset.mem_univ i⟩ (swapGain T q u i)

end CalibeatBandit

end

section

set_option autoImplicit false

namespace CalibeatBandit

open MeasureTheory Set

/-- A bounded round reward on the normalized scale used in the information bound. -/
noncomputable def boundedObservation {N : ℕ} (η u : ℝ) (i : Fin N)
    (d : ℝ × (Fin N → ℝ)) : ℝ :=
  8 * boundedRoundReward η u i d - 1

/-- The same run with observations on the normalized scale. -/
noncomputable def boundedTapeTranscript {N : ℕ} (η : ℝ) (u : ℕ → Fin N → ℝ)
    (pick : (t : ℕ) → FeedbackHistory t → Fin N) :
    (t : ℕ) → RewardTape N t → FeedbackHistory t
  | 0, _ => ()
  | t + 1, p =>
    let past := boundedTapeTranscript η u pick t p.1
    let i := pick t past
    (past, boundedObservation η (u t i) i p.2)

/-- The count of plays of one auxiliary action within a period of length r. -/
noncomputable def periodHits {N : ℕ} (η : ℝ) (u : ℕ → Fin N → ℝ)
    (pick : (t : ℕ) → FeedbackHistory t → Fin N) (j : Fin N)
    (r : ℕ) (tape : RewardTape N r) : ℝ :=
  ∑ i : Fin r, if pick i (boundedTapeTranscript η u pick i (rewardTapePrefix N i.isLt.le tape)) = j
    then 1 else 0

end CalibeatBandit

end

section

set_option autoImplicit false

namespace CalibeatBandit

open Set

/-- When the learner's seed is fixed, its distribution for a round is
concentrated on the action it chooses from the preceding feedback. -/
noncomputable def treePlayProbability {h M U N : ℕ} (e : Fin N ≃ TreeAction h M U)
    (pick : (t : ℕ) → FeedbackHistory t → TreeAction h M U)
    (active : ℕ → Fin (2 ^ h)) (η : ℝ) (coin : TreeNode h → Bool) (leafCoin : ℕ → Bool)
    (selected : Fin (2 ^ h) → Fin M) (z : ℕ → Icc (0 : ℝ) 1)
    (draw : ℕ → TreeAction h M U → Ico (0 : ℝ) 1) (t : ℕ) (i : Fin N) : ℝ :=
  let y (s : ℕ) := treeReward η (active s) coin (leafCoin s) (selected (active s)) (z s) (draw s)
  if pick t (feedbackHistory pick y t) = e i then 1 else 0

end CalibeatBandit

end

section

set_option autoImplicit false

namespace CalibeatBandit

open Set

/-- The embedded auxiliary actions of the tree. -/
def treeAuxAction {h M U N : ℕ} (e : Fin N ≃ TreeAction h M U) : Fin M ↪ Fin N where
  toFun j := e.symm (.inr (.inl j))
  inj' := by
    intro j k hj
    have he := e.symm.injective hj
    simpa only [Sum.inr.injEq, Sum.inl.injEq] using he

end CalibeatBandit

end

section

set_option autoImplicit false

namespace CalibeatBandit

open MeasureTheory Set

noncomputable def treeEnvironmentPlay {h M U N T : ℕ} (e : Fin N ≃ TreeAction h M U)
    (active : ℕ → Fin (2 ^ h)) (η : ℝ) (pick : (t : ℕ) → FeedbackHistory t → Fin N)
    (anchor : Fin N) (env : TreeEnvironment h M N T) (t : ℕ) : Fin N → ℝ :=
  Pi.single (treeEnvironmentAction e active η pick anchor env t) 1

end CalibeatBandit

end


