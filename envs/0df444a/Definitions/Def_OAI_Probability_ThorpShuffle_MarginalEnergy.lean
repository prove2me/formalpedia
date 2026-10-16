-- Prove2me | Definitions.Def_OAI_Probability_ThorpShuffle_MarginalEnergy
-- name    : OAI_Probability_ThorpShuffle_MarginalEnergy
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-16T03:34:14.40074+00:00
-- url     : https://prove2.me/theorems/dbb3ce36-e1cf-47d5-9352-12eaeee09f02
-- title:
--   A single conditional Thorp step equals the one-step iteration
-- statement:
--   Consider a deck of $2^{d+1}$ cards with positions $Q_{d+1}=\{0,1\}^{d+1}$ and coin vectors $c:Q_d\to\{0,1\}$. A centered state is a pair $v=(B,w)$ of a free marker $B:Q_{d+1}\to\{0,1\}$ and a weight $w:Q_{d+1}\to\mathbb{R}$ with $\sum_xw(x)=0$, $w=0$ off $\{B=1\}$ and $\sum_xw(x)^2\le1$. The conditional Thorp step $\operatorname{next}(v;c)$ transports $B$ and $w$ by the Thorp step $T_c$, except that on a pair of positions that are both free it replaces the two weights by their average. $\operatorname{iter}_t(v;\omega)$ applies $\operatorname{next}$ along a history $\omega$ of $t$ coin vectors.
--
--   The module records that iterating once along the one-element history $(c)$ is the same as applying one step:
--   $$
--   \operatorname{iter}_1\bigl(v;(c)\bigr)=\operatorname{next}(v;c).
--   $$
--
--   The identity lets one-step energy bounds, which are proved for $\operatorname{next}$, be read off for averages over histories of length one.
--
--   **Formalization Note** The lemma is `Conditional.iterateState_one`. It holds by definition (`rfl`), and the one-element history is the constant function `fun _ => c` on `Fin 1`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/ThorpShuffle/MarginalEnergy.lean

-- Generated from openai/math@1581d4c lean/OAI/Probability/ThorpShuffle/MarginalEnergy.lean by skeleton subtraction
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
import Definitions.Def_OAI_Probability_ThorpShuffle_EnergyDecay

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe uα

noncomputable section

open scoped BigOperators
open Filter

namespace Thorp

namespace Conditional

@[simp] theorem iterateState_one (d : ℕ) (v : CenteredState (d + 1)) (c : Coins (d + 1)) :
    iterateState d v 1 (fun _ => c) = nextState d v c := rfl

end Conditional

namespace Conditional

end Conditional

end Thorp

end

end OAI


