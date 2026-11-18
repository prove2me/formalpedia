-- Prove2me | Definitions.Def_OAIQ368Chrom068
-- name    : OAIQ368Chrom068
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-17T20:19:33.268347+00:00
-- url     : https://prove2.me/theorems/c7045003-caeb-47b0-9c93-54de89b28014
-- title:
--   Definitions bundle OAIQ368Chrom068 of the split of OpenAI, Elementary Positivity of Chromatic Quasisymmetric Functions
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.elementaryPositivityWitness_exists`, carved from OpenAI's openai/math development (OpenAI, *Elementary Positivity of Chromatic Quasisymmetric Functions*, OpenAI Math Release, September 24, 2026, result family 169, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 2 declarations of OpenAI's Lean: 1 definition and 1 theorem. The definitions and types are `OAI.ElementaryPositivity.NaturalUnitIntervalGraph.reversalEquiv`.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics, in whole or in part: [`Chromatic_QuantumTorus_Admissible`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/Chromatic/QuantumTorus/Admissible.lean).
--
--   **Imports.** It imports the published bundle `Def_ElementaryPositivity`; the bundles `OAIQ368Chrom060` and `OAIQ368Chrom062` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ368Chrom069`.
-- source:
--   OpenAI, Elementary Positivity of Chromatic Quasisymmetric Functions, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 169; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Elementary-Positivity-of-Chromatic-Quasisymmetric-Functions-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics at commit 7ef5c0c

import Mathlib
import Definitions.Def_ElementaryPositivity
import Definitions.Def_OAIQ368Chrom060
import Definitions.Def_OAIQ368Chrom062

section
-- module Solutions.OAIQ368_CHROM.Chromatic_QuantumTorus_Admissible
attribute [-simp] _root_.OAI.ElementaryPositivity.WallUnits.rescale_C
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.NaturalUnitIntervalGraph
variable {n : ℕ} (G : ElementaryPositivity.NaturalUnitIntervalGraph n)

theorem nondescent_iff_reverse_admissible (σ : Equiv.Perm (Fin n)) :
    G.Nondescent σ ↔ G.Admissible (reversePerm σ) := by
  constructor
  · intro h i j hij hlt
    exact (G.edge_comm _ _).mp (h j.rev i.rev (rev_adjacent hij) hlt)
  · intro h i j hij hlt
    have he := h j.rev i.rev (rev_adjacent hij)
    simpa using he (by simpa using hlt)

def reversalEquiv : {σ : Equiv.Perm (Fin n) // G.Nondescent σ} ≃
    {w : Equiv.Perm (Fin n) // G.Admissible w} where
  toFun σ := ⟨reversePerm σ.val, (G.nondescent_iff_reverse_admissible _).mp σ.property⟩
  invFun w := ⟨reversePerm w.val,
    (G.nondescent_iff_reverse_admissible _).mpr (by simpa using w.property)⟩
  left_inv σ := Subtype.ext (reversePerm_reverse _)
  right_inv w := Subtype.ext (reversePerm_reverse _)

end ElementaryPositivity.NaturalUnitIntervalGraph

end

end OAI
end


