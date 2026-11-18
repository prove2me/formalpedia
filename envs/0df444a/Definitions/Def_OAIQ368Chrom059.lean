-- Prove2me | Definitions.Def_OAIQ368Chrom059
-- name    : OAIQ368Chrom059
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-17T20:13:04.052207+00:00
-- url     : https://prove2.me/theorems/2f4d724c-f0ff-4dcb-befa-65ebe62e964f
-- title:
--   Definitions bundle OAIQ368Chrom059 of the split of OpenAI, Elementary Positivity of Chromatic Quasisymmetric Functions
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.elementaryPositivityWitness_exists`, carved from OpenAI's openai/math development (OpenAI, *Elementary Positivity of Chromatic Quasisymmetric Functions*, OpenAI Math Release, September 24, 2026, result family 169, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 6 declarations of OpenAI's Lean: 4 definitions and 2 theorems. The definitions and types are `OAI.ElementaryPositivity.TriangularDynamics.HistoryLeaf`, `OAI.ElementaryPositivity.TriangularDynamics.historyDimension`, `OAI.ElementaryPositivity.TriangularDynamics.historySyntax`, `OAI.ElementaryPositivity.TriangularDynamics.historyWeight`.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics, in whole or in part: [`Chromatic_Histories_CommonHistoryLeaves`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/Chromatic/Histories/CommonHistoryLeaves.lean), [`Chromatic_Witness_ElementarySingletonCoefficient`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/Chromatic/Witness/ElementarySingletonCoefficient.lean).
--
--   **Imports.** It imports the published bundle `Def_ElementaryPositivity`; the bundle `OAIQ368Chrom058` of this split; the published statement `OAI.ElementaryPositivity.TriangularDynamics.graph_common_history`.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ368Chrom060`; the statement `OAI.ElementaryPositivity.TriangularDynamics.historyWeight_positive`; the proof of `OAI.ElementaryPositivity.TriangularDynamics.historyWeight_positive`.
-- source:
--   OpenAI, Elementary Positivity of Chromatic Quasisymmetric Functions, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 169; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Elementary-Positivity-of-Chromatic-Quasisymmetric-Functions-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics at commit 7ef5c0c

import Mathlib
import Definitions.Def_ElementaryPositivity
import Definitions.Def_OAIQ368Chrom058
import Theorems.Thm_OAI_ElementaryPositivity_TriangularDynamics_graph_common_history

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Histories_CommonHistoryLeaves
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus.LocalHistoryFormula
open PowerSeries PowerSeriesAdjoint PowerSeriesSplit LaurentPositive WallUnits
open scoped BigOperators
open Classical
noncomputable section
variable {M E I:Type*} [AddCommGroup M] [AddCommGroup E] [Module ℝ E] [Fintype I]

variable (Ω:M →+ M →+ ℤ) (C:(I → ℤ) →+ M) (e:M →+ E)
variable (F:CompletedPositive LaurentRay.vUnit Ω C)

lemma leafWeight_positive (p:LocalHistoryFormula M E) (hp:p.Positive Ω C e F) (l:p.Leaf) :
    LaurentPositive.Positive (leafWeight Ω C e F p l) := by
  induction p with
  | zero=>exact l.elim
  | stop j m=>exact positive_one
  | add p q ihp ihq=>cases l with
    | inl l=>exact ihp hp.1 l
    | inr l=>exact ihq hp.2 l
  | jump d m r t p ih=>exact hp.1.mul (ih hp.2 l)

end
end ElementaryPositivity.QuantumTorus.LocalHistoryFormula

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Witness_ElementarySingletonCoefficient
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.TriangularDynamics
open QuantumTorus WallUnits LatticeExtension LatticeRealization
open scoped BigOperators
open Classical
noncomputable section
variable {n:ℕ} (G:NaturalUnitIntervalGraph n)

def historyDimension : ℕ:=(graph_common_history G).choose

def historySyntax : LocalHistoryFormula (Extended (Vertex (historyDimension G) (Cell (historyDimension G))))
    ((Vertex (historyDimension G) (Cell (historyDimension G)) → ℝ) ×
      (Vertex (historyDimension G) (Cell (historyDimension G)) → ℝ)) :=
  (graph_common_history G).choose_spec.choose

lemma historySyntax_positive : (historySyntax G).Positive
    (extendedOmega (historyDimension G)) (extendedRoots (historyDimension G)) extendedCast
    (simpleTotalTransport (extendedOmega (historyDimension G)) (extendedRoots (historyDimension G))) :=
  (graph_common_history G).choose_spec.choose_spec.1

abbrev HistoryLeaf := {l:(historySyntax G).Leaf // AnchoredLeaf n (historySyntax G) l}

def historyWeight (l:HistoryLeaf G) : LaurentSeries ℚ:=
  (historySyntax G).leafWeight (extendedOmega (historyDimension G)) (extendedRoots (historyDimension G))
    extendedCast (simpleTotalTransport (extendedOmega (historyDimension G))
      (extendedRoots (historyDimension G))) l.val
end
end ElementaryPositivity.TriangularDynamics

end

end OAI
end


