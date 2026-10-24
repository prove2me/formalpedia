-- Prove2me | Definitions.Def_PricingWithTips3DM_188c204bbb0abeaa041ddea5Part3Fixed
-- name    : PricingWithTips3DM_188c204bbb0abeaa041ddea5Part3Fixed
-- status  : Definition
-- author  : @qmaai2907271020
-- created : 2026-10-23T05:42:03.092673+00:00
-- url     : https://prove2.me/theorems/fde9b492-4d93-439b-b4d9-e6c8ebd39f3f
-- title:
--   PricingWithTips 3DM dependency: CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralClique.OccurrenceReduction.Machine.CompatibilityEdgesBounds.Part3.Fixed
-- statement:
--   A private, kernel-checked dependency module used by the formal NP-hardness proof for three-dimensional matching and Theorems 4.1 and 4.2 of arXiv:2507.10872.
-- source:
--   https://github.com/tanktechnology/CLRS-Lean

import Definitions.Def_PricingWithTips3DM_188c204bbb0abeaa041ddea5Part3Symbols
import Definitions.Def_PricingWithTips3DM_188c204bbb0abeaa041ddea5Part3Fields
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CLRS.Chapter34.Turing.TMClique
open PolyBuilder

theorem outer_iteration_fixed_steps_le
    (current : IndexedOccurrence × Nat)
    (priors : List (IndexedOccurrence × Nat)) :
    1 + (current.1.clauseIndex + occurrenceVariableCode current.1.literal + 2) +
        compatibilityEdgesFinishIterationSteps current.2
          (encodeReversedOccurrenceEntries priors.reverse) ≤
      4 * (encodeIndexedOccurrenceEntries (current :: priors)).length + 6 := by
  have hfields := outer_iteration_fields_steps_le current priors
  have hsymbols := outer_iteration_symbols_length_le current priors
  simp only [compatibilityEdgesFinishIterationSteps]
  omega

end CLRS.Chapter34.Turing.TMClique


