-- Prove2me | Definitions.Def_OAI_Probability_ThorpShuffle_ConditionalLaw
-- name    : OAI_Probability_ThorpShuffle_ConditionalLaw
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-16T03:37:17.704053+00:00
-- url     : https://prove2.me/theorems/6d670bd6-b009-49b2-b676-98c2164b2a31
-- title:
--   Appending a coin vector to a Thorp history composes one more shuffle step
-- statement:
--   Let $Q_d=\{0,1\}^d$ be the set of positions of a deck of $2^d$ cards, and let $T_c\in\mathrm{Sym}(Q_d)$ be the Thorp step driven by a coin vector $c$. For $d\ge1$ and $c:Q_{d-1}\to\{0,1\}$, $T_c(x_0,x_1,\dots,x_{d-1})=(x_1,\dots,x_{d-1},x_0\oplus c(x_1,\dots,x_{d-1}))$ with $\oplus$ addition modulo $2$; for $d=0$, $T_c$ is the identity. For a history $\omega=(\omega_0,\dots,\omega_{t-1})$ of coin vectors, $\mathrm{run}_t(\omega)=T_{\omega_{t-1}}\circ\cdots\circ T_{\omega_0}$.
--
--   The module records that, for all $d,t\in\mathbb{N}$, every history $\omega$ of length $t$ and every coin vector $c$,
--   $$
--   \mathrm{run}_{t+1}(\omega_0,\dots,\omega_{t-1},c)=T_c\circ\mathrm{run}_t(\omega_0,\dots,\omega_{t-1}).
--   $$
--
--   This form, with the new coin vector appended at the end, is the one used when the last step of the shuffle is averaged over its coins while the earlier history is held fixed.
--
--   **Formalization Note** The lemma is `Conditional.run_snoc`. Appending is `Fin.snoc`, and composition is the product in `Equiv.Perm`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/ThorpShuffle/ConditionalLaw.lean

-- Generated from openai/math@1581d4c lean/OAI/Probability/ThorpShuffle/ConditionalLaw.lean by skeleton subtraction
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
import Definitions.Def_OAI_Probability_ThorpShuffle_MarginalEnergy

namespace OAI

universe uι uα

noncomputable section

open scoped BigOperators
open Filter

namespace Thorp

namespace Conditional

@[simp] theorem run_snoc (d t : ℕ) (ω : History d t) (c : Coins d) :
    run d (t + 1) (Fin.snoc ω c) = step d c * run d t ω := by
  rw [run_succ]
  simp

end Conditional

end Thorp

end

end OAI


