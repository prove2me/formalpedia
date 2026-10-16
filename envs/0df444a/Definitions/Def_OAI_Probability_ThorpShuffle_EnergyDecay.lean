-- Prove2me | Definitions.Def_OAI_Probability_ThorpShuffle_EnergyDecay
-- name    : OAI_Probability_ThorpShuffle_EnergyDecay
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-16T03:32:34.928871+00:00
-- url     : https://prove2.me/theorems/51298643-8e2f-4bef-bead-46452f2d7744
-- title:
--   Appending a coin vector performs one more conditional Thorp step
-- statement:
--   Consider a deck of $2^{d+1}$ cards with positions $Q_{d+1}=\{0,1\}^{d+1}$ and coin vectors $c:Q_d\to\{0,1\}$. A raw state is a pair $v=(B,w)$ of a free marker $B:Q_{d+1}\to\{0,1\}$ and a weight $w:Q_{d+1}\to\mathbb{R}$. A centered state is a raw state with $\sum_xw(x)=0$, $w=0$ off $\{B=1\}$ and $\sum_xw(x)^2\le1$. The conditional Thorp step $\operatorname{next}(v;c)$ transports $B$ by the Thorp step $T_c$. It also transports $w$ by $T_c$, except that on a pair of positions that are both free it replaces the two weights by their average. For a history $\omega$ of length $t$, $\operatorname{iter}_t(v;\omega)$ applies $\operatorname{next}$ with the coin vectors $\omega_0,\dots,\omega_{t-1}$ in this order.
--
--   The module records that appending a coin vector $c$ at the end of a history $\omega$ of length $t$ adds one step at the end:
--   $$
--   \operatorname{iter}_{t+1}\bigl(v;(\omega_0,\dots,\omega_{t-1},c)\bigr)=\operatorname{next}\bigl(\operatorname{iter}_t(v;\omega);\,c\bigr),
--   $$
--   both for raw states and for centered states.
--
--   This is the form of the recursion used when the most recent coin vector is averaged out first, as in conditioning arguments that reveal coins one step at a time.
--
--   **Formalization Note** The lemmas are `Conditional.rawIterate_snoc` and `Conditional.iterateState_snoc`. Appending is `Fin.snoc`, while the defining recursion of `rawIterate` and `iterateState` is phrased with `Fin.castSucc` and `Fin.last`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/ThorpShuffle/EnergyDecay.lean

-- Generated from openai/math@1581d4c lean/OAI/Probability/ThorpShuffle/EnergyDecay.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the ThorpFirstReciprocal mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_ThorpFirstReciprocal
import Definitions.Def_OAI_Probability_ThorpShuffle_Model
import Definitions.Def_OAI_Probability_ThorpShuffle_PairAveraging
import Definitions.Def_OAI_Probability_ThorpShuffle_Walsh
import Definitions.Def_OAI_Probability_ThorpShuffle_Support
import Definitions.Def_OAI_Probability_ThorpShuffle_ConditionalFlow
import Definitions.Def_OAI_Probability_ThorpShuffle_FiniteExpectation
import Definitions.Def_OAI_Probability_ThorpShuffle_WalshFlow
import Definitions.Def_OAI_Probability_ThorpShuffle_FreshCoins
import Definitions.Def_OAI_Probability_ThorpShuffle_HalfHistories
import Definitions.Def_OAI_Probability_ThorpShuffle_NoiseEnergy

namespace OAI

noncomputable section

open scoped BigOperators
open Filter

namespace Thorp

namespace Conditional

end Conditional

namespace Conditional

@[simp] theorem rawIterate_snoc (d t : ℕ) (v : RawState (d + 1))
    (ω : History (d + 1) t) (c : Coins (d + 1)) :
    rawIterate d v (t + 1) (Fin.snoc ω c) = rawNext d (rawIterate d v t ω) c := by
  simp [rawIterate]

@[simp] theorem iterateState_snoc (d t : ℕ) (v : CenteredState (d + 1))
    (ω : History (d + 1) t) (c : Coins (d + 1)) :
    iterateState d v (t + 1) (Fin.snoc ω c) = nextState d (iterateState d v t ω) c := by
  simp [iterateState]

end Conditional

end Thorp

end

end OAI


