-- Prove2me | Definitions.Def_OAI_Probability_ThorpCompatibility_UniformSupport
-- name    : OAI_Probability_ThorpCompatibility_UniformSupport
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-14T23:36:21.516361+00:00
-- url     : https://prove2.me/theorems/349d94ab-abdc-479d-8d8e-87bec9d3c62f
-- title:
--   Uniform law on a nonempty finite subset
-- statement:
--   Let $\Omega$ be a finite set and $s\subseteq\Omega$ a nonempty subset. The uniform law on $s$ is the law on $\Omega$ given by
--   $$
--   U_s(a)=\begin{cases}\dfrac{1}{|s|},&a\in s,\\ 0,&a\notin s.\end{cases}
--   $$
--
--   If a law $P$ on $\Omega$ is supported in $s$, then its relative entropy with respect to $U_s$ is $D(P\,\|\,U_s)=\log|s|-H(P)$. Applied to the predicted law of a column entry, which is supported on the $A-i$ values not yet used by the column permutation, this bounds the mass of the heavy values: for $H>0$,
--   $$
--   (\log H-1)\,P\big(\{w: P(w)>H/|s|\}\big)\le\log|s|-H(P).
--   $$
--
--   **Formalization Note** The definition is `Law.uniformOn s hs`, where `hs` is a proof that `s` is nonempty.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/ThorpCompatibility/UniformSupport.lean

-- Generated from openai/math@1581d4c lean/OAI/Probability/ThorpCompatibility/UniformSupport.lean by skeleton subtraction
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
import Definitions.Def_OAI_Probability_ThorpCompatibility_EntropyChain
import Definitions.Def_OAI_Probability_ThorpCompatibility_GridEntropy
import Definitions.Def_OAI_Probability_ThorpCompatibility_GridExposure
import Definitions.Def_OAI_Probability_ThorpCompatibility_ClumpCost
import Definitions.Def_OAI_Probability_ThorpCompatibility_PermutationProbability
import Definitions.Def_OAI_Probability_ThorpCompatibility_ListIncidence
import Definitions.Def_OAI_Probability_ThorpCompatibility_ClumpMoments
import Definitions.Def_OAI_Probability_ThorpCompatibility_HeavyEntries
import Definitions.Def_OAI_Probability_ThorpCompatibility_ExposureEntropy

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

open scoped Classical
namespace ThorpCompatibility
namespace Law
open Finset
variable {α : Type*} [Fintype α]

noncomputable def uniformOn (s : Finset α) (hs : s.Nonempty) : Law α where
  mass a := if a ∈ s then 1 / (s.card : ℝ) else 0
  nonneg a := by split_ifs <;> positivity
  total := by
    rw [← Finset.sum_filter]
    simp [hs.card_ne_zero]

end Law
open Finset

end ThorpCompatibility

end OAI


