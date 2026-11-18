-- Prove2me | Definitions.Def_OAIQ368Chrom066
-- name    : OAIQ368Chrom066
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-17T18:38:10.407497+00:00
-- url     : https://prove2.me/theorems/7b4f8b0f-6c19-4d37-8893-32e8b3ebe29c
-- title:
--   Definitions bundle OAIQ368Chrom066 of the split of OpenAI, Elementary Positivity of Chromatic Quasisymmetric Functions
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.elementaryPositivityWitness_exists`, carved from OpenAI's openai/math development (OpenAI, *Elementary Positivity of Chromatic Quasisymmetric Functions*, OpenAI Math Release, September 24, 2026, result family 169, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 1 declaration of OpenAI's Lean: 1 theorem.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics, in whole or in part: [`Chromatic_QuantumTorus_Admissible`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/Chromatic/QuantumTorus/Admissible.lean).
--
--   **Imports.** It imports the published bundle `Def_ElementaryPositivity`; the bundle `OAIQ368Chrom058` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ368Chrom067`.
-- source:
--   OpenAI, Elementary Positivity of Chromatic Quasisymmetric Functions, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 169; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Elementary-Positivity-of-Chromatic-Quasisymmetric-Functions-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics at commit 7ef5c0c

import Mathlib
import Definitions.Def_ElementaryPositivity
import Definitions.Def_OAIQ368Chrom058

section
-- module Solutions.OAIQ368_CHROM.Chromatic_QuantumTorus_Admissible
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.NaturalUnitIntervalGraph
variable {n : ℕ} (G : ElementaryPositivity.NaturalUnitIntervalGraph n)

lemma invertedEdges_reverse (σ : Equiv.Perm (Fin n)) :
    G.invertedEdges (reversePerm σ) =
      G.edges.filter (fun ab => ¬ σ.symm ab.2 < σ.symm ab.1) := by
  ext ab
  simp only [mem_invertedEdges, Finset.mem_filter, mem_edges,
    inverse_reverse_apply, Fin.rev_lt_rev, not_lt]
  constructor
  · rintro ⟨hab,he,hpos⟩
    exact ⟨⟨hab,he⟩,hpos.le⟩
  · rintro ⟨⟨hab,he⟩,hpos⟩
    refine ⟨hab,he,lt_of_le_of_ne hpos ?_⟩
    exact fun hh => hab.ne (σ.symm.injective hh)

end ElementaryPositivity.NaturalUnitIntervalGraph

end

end OAI
end


