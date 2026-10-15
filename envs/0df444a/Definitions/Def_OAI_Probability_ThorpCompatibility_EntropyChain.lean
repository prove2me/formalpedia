-- Prove2me | Definitions.Def_OAI_Probability_ThorpCompatibility_EntropyChain
-- name    : OAI_Probability_ThorpCompatibility_EntropyChain
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-14T23:21:36.919531+00:00
-- url     : https://prove2.me/theorems/0d36c517-079f-4385-a096-bff295f590e0
-- title:
--   Revealed history of a finite sequence of random variables
-- statement:
--   Let $\Omega$ and $B$ be finite sets, let $n\in\mathbb{N}$, and let $X_0,\dots,X_{n-1}:\Omega\to B$ be random variables. Adjoin to $B$ a symbol $\star$ meaning *not yet revealed*. For a time $t\in\mathbb{N}$ and an outcome $a\in\Omega$, the history at time $t$ is the vector $\mathrm{hist}_t(a)\in(B\cup\{\star\})^{n}$ with entries
--   $$
--   \mathrm{hist}_t(a)_i=\begin{cases}X_i(a), & i<t,\\ \star, & i\ge t,\end{cases}\qquad i\in\{0,\dots,n-1\}.
--   $$
--   Thus $\mathrm{hist}_0$ reveals nothing and $\mathrm{hist}_t$ reveals $X_0,\dots,X_{t-1}$. For $t\ge n$, $\mathrm{hist}_t$ reveals the whole vector $(X_0,\dots,X_{n-1})$.
--
--   Encoding the revealed past as one random variable with values in a fixed finite set lets the chain rule for entropy,
--   $$
--   \sum_{i=0}^{n-1}H\big(X_i\mid\mathrm{hist}_i\big)=H(X_0,\dots,X_{n-1}),
--   $$
--   be written with the conditional entropy of two random variables. It is used to expose a permutation one value at a time.
--
--   **Formalization Note** The definition is `Law.history X t a : Fin n → Option β`, where `none` plays the role of $\star$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/ThorpCompatibility/EntropyChain.lean

-- Generated from openai/math@1581d4c lean/OAI/Probability/ThorpCompatibility/EntropyChain.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the ThorpWeightedCompatibility mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_ThorpWeightedCompatibility
import Definitions.Def_OAI_Probability_ThorpCompatibility_FiniteLaw
import Definitions.Def_OAI_Probability_ThorpCompatibility_Entropy
import Definitions.Def_OAI_Probability_ThorpCompatibility_ConditionalEntropy
import Definitions.Def_OAI_Probability_ThorpCompatibility_LightRescaling
import Definitions.Def_OAI_Probability_ThorpCompatibility_Prediction
import Definitions.Def_OAI_Probability_ThorpCompatibility_RankLaw
import Definitions.Def_OAI_Probability_ThorpCompatibility_Model

namespace OAI

open scoped Classical
namespace ThorpCompatibility
namespace Law
open Finset
variable {α β γ δ : Type*} [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]

noncomputable def history {n : ℕ} (X : Fin n → α → β) (t : ℕ) (a : α) :
    Fin n → Option β := fun i => if (i : ℕ) < t then some (X i a) else none

end Law
end ThorpCompatibility

end OAI


