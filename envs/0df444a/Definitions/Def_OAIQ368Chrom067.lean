-- Prove2me | Definitions.Def_OAIQ368Chrom067
-- name    : OAIQ368Chrom067
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-17T20:19:21.391622+00:00
-- url     : https://prove2.me/theorems/cfc739f7-f5b9-4092-99d7-17faf8b486e2
-- title:
--   Definitions bundle OAIQ368Chrom067 of the split of OpenAI, Elementary Positivity of Chromatic Quasisymmetric Functions
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.elementaryPositivityWitness_exists`, carved from OpenAI's openai/math development (OpenAI, *Elementary Positivity of Chromatic Quasisymmetric Functions*, OpenAI Math Release, September 24, 2026, result family 169, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 3 declarations of OpenAI's Lean: 3 theorems.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics, in whole or in part: [`Chromatic_QuantumTorus_Admissible`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/Chromatic/QuantumTorus/Admissible.lean), [`Chromatic_Witness_HistoryMainWitness`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/Chromatic/Witness/HistoryMainWitness.lean).
--
--   **Imports.** It imports the published bundle `Def_ElementaryPositivity`; the bundles `OAIQ368Chrom060`, `OAIQ368Chrom064` and `OAIQ368Chrom066` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ368Chrom069`.
-- source:
--   OpenAI, Elementary Positivity of Chromatic Quasisymmetric Functions, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 169; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Elementary-Positivity-of-Chromatic-Quasisymmetric-Functions-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics at commit 7ef5c0c

import Mathlib
import Definitions.Def_ElementaryPositivity
import Definitions.Def_OAIQ368Chrom060
import Definitions.Def_OAIQ368Chrom064
import Definitions.Def_OAIQ368Chrom066

section
-- module Solutions.OAIQ368_CHROM.Chromatic_QuantumTorus_Admissible
attribute [-instance] _root_.OAI.ElementaryPositivity.FiniteSearch.instDecidableTest _root_.OAI.ElementaryPositivity.FiniteSearch.instDecidableWordOK
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.NaturalUnitIntervalGraph
variable {n : ℕ} (G : ElementaryPositivity.NaturalUnitIntervalGraph n)

theorem graphInversions_add_reverse (σ : Equiv.Perm (Fin n)) :
    G.graphInversions σ + G.graphInversions (reversePerm σ) = G.edgeCount := by
  rw [G.graphInversions_eq_card_invertedEdges,
    G.graphInversions_eq_card_invertedEdges, invertedEdges_reverse]
  exact Finset.card_filter_add_card_filter_not (s := G.edges) (fun ab => σ.symm ab.2 < σ.symm ab.1)

theorem graphInversions_le_edges (σ : Equiv.Perm (Fin n)) :
    G.graphInversions σ ≤ G.edgeCount := by
  have h := G.graphInversions_add_reverse σ
  omega

end ElementaryPositivity.NaturalUnitIntervalGraph

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Witness_HistoryMainWitness
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.FiniteSearch
open scoped BigOperators
open Packets
open Classical
noncomputable section
variable {n:ℕ} (G:NaturalUnitIntervalGraph n)

lemma witnessCount_zero_high (t:Table n) (a:Fin n → ℕ) (k:ℕ) (hk:G.edgeCount<k):witnessCount G t a k=0 := by
  unfold witnessCount
  apply Finset.sum_eq_zero
  intro w hw
  rw [ite_eq_right]
  rintro ⟨hp,he⟩
  have h:=G.graphInversions_le_edges (Equiv.ofBijective w hp.1)
  change wordEnergy G w≤G.edgeCount at h
  omega
end
end ElementaryPositivity.FiniteSearch

end

end OAI
end


