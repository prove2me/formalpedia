-- Prove2me | Definitions.Def_OAIQ069A005
-- name    : OAIQ069A005
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-28T01:47:14.269744+00:00
-- url     : https://prove2.me/theorems/f3048dbe-9b84-403d-b308-fa962fd6828b
-- title:
--   Definitions bundle OAIQ069A005 of the split of OpenAI, Hardness of finding large independent sets in three-colorable graphs (result family 106)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.LargeIndependentSets.mainTheoremReal`, carved from OpenAI's openai/math development (OpenAI, *Hardness of finding large independent sets in three-colorable graphs (result family 106)*, OpenAI Math Release, September 24, 2026, result family 106, [github.com/openai/math](https://github.com/openai/math) at commit 1581d4c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 5 declarations of OpenAI's Lean: 2 definitions, 1 instance and 2 theorems. The definitions and types are `OAI.IndependentSetsGames.Foundations.PCP.CodeComposition.singletonMask`, `OAI.LargeIndependentSets.embeddingLayerLaw`.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics, in whole or in part: [`IndependentSets_Encoding_GraphPrinter`](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/IndependentSets/Encoding/GraphPrinter.lean), [`IndependentSets_Expansion_Capped`](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/IndependentSets/Expansion/Capped.lean), [`IndependentSets_Geometry_EmbeddingLayerLaw`](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/IndependentSets/Geometry/EmbeddingLayerLaw.lean), [`IndependentSets_PCP_CodeComposition`](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/IndependentSets/PCP/CodeComposition.lean), [`IndependentSets_PCP_LCTable`](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/IndependentSets/PCP/LCTable.lean).
--
--   **Imports.** It imports the published bundle `Def_IndependentSets`; the bundles `OAIQ069A000`, `OAIQ069A001` and `OAIQ069A002` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ069A007`.
-- source:
--   OpenAI, Hardness of finding large independent sets in three-colorable graphs (result family 106), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 106; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/Hardness-of-finding-large-independent-sets-in-three-colorable-graphs-September-24-2026/Hardness-of-finding-large-independent-sets-in-three-colorable-graphs-September-24-2026.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics at commit 1581d4c

import Mathlib
import Definitions.Def_IndependentSets
import Definitions.Def_OAIQ069A000
import Definitions.Def_OAIQ069A001
import Definitions.Def_OAIQ069A002

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_PCP_CodeComposition
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace IndependentSetsGames.Foundations.PCP.CodeComposition

open scoped BigOperators
open IndependentSetsGames.Foundations.Hastad

def singletonMask {A : Type*} [DecidableEq A] (a : A) : Cube A :=
  fun i => decide (i = a)

end IndependentSetsGames.Foundations.PCP.CodeComposition
end

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Geometry_EmbeddingLayerLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LargeIndependentSets
open scoped Classical BigOperators

noncomputable def embeddingLayerLaw {r s : ℕ}
    (p : (Fin s ↪o Fin r) → ℚ)
    (hp : (∀ coordinate, 0 ≤ p coordinate) ∧ ∑ coordinate, p coordinate = 1) : LayerLaw r s where
  weight B := ∑ e, if B = Finset.univ.map e.toEmbedding then p e else 0
  nonneg B := Finset.sum_nonneg (fun e _ => by split_ifs; exact hp.1 e; rfl)
  total := by
    rw [Finset.sum_comm]
    simpa using hp.2
  support B hB := by
    apply Finset.sum_eq_zero
    intro e _
    apply ite_eq_right
    intro h
    apply hB
    rw [h]
    simp

end LargeIndependentSets

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Expansion_Capped
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LargeIndependentSets.ShortestPaths

namespace Capped

lemma clip_le_iff (B : ℕ) (c : ℕ∞) {t : ℕ} (ht : t≤B) :
    (clip B c).val ≤ t ↔ c ≤ (t:ℕ∞) := by
  induction c using ENat.recTopCoe with
  | top => simp; omega
  | coe c => simp only [clip_nat,ENat.natCast_le_natCast]; omega

end Capped
end LargeIndependentSets.ShortestPaths

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Encoding_GraphPrinter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LargeIndependentSets.GraphPrinter
open IndependentSetsCut.CounterMachine
open IndependentSetsGames.Foundations.Complexity
open scoped Classical
noncomputable section

lemma bits_get (G : Graph) (w : ℕ) (hw : w<(graphBits G).length) :
    ((graphBits G)[w]?).getD false=
      if h : w<(nameBits G.vertices).length then ((nameBits G.vertices)[w]?).getD false
      else G.adj
        (⟨w-(nameBits G.vertices).length,by
          apply Nat.sub_lt_left_of_lt_add (Nat.le_of_not_gt h)
          simpa only [graphBits,List.length_append,matrix_eq,List.length_ofFn] using hw⟩ : Fin (G.vertices*G.vertices)).divNat
        (⟨w-(nameBits G.vertices).length,by
          apply Nat.sub_lt_left_of_lt_add (Nat.le_of_not_gt h)
          simpa only [graphBits,List.length_append,matrix_eq,List.length_ofFn] using hw⟩ : Fin (G.vertices*G.vertices)).modNat := by
  simp only [graphBits,matrix_eq]
  split_ifs with h
  · rw [List.getElem?_append_left h]
  · rw [List.getElem?_append_right (Nat.le_of_not_gt h),List.getElem?_ofFn]
    have hb : w-(nameBits G.vertices).length<G.vertices*G.vertices := by
      apply Nat.sub_lt_left_of_lt_add (Nat.le_of_not_gt h)
      simpa only [graphBits,List.length_append,matrix_eq,List.length_ofFn] using hw
    simp only [dite_eq_left hb,Option.getD_some]

end
end LargeIndependentSets.GraphPrinter

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_PCP_LCTable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LargeIndependentSets.UniformLC
open IndependentSetsCut.CounterMachine
open scoped Classical BigOperators
noncomputable section

instance instNonemptyFinNe {L R : Type} (t : Table L R) : Nonempty (Fin t.ne) := ⟨⟨0,t.he⟩⟩

end
end LargeIndependentSets.UniformLC

end OAI
end


