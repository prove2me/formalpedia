-- Prove2me | Definitions.Def_PricingWithTips3DM_d4904298ab86e1b10dc4a2cf
-- name    : PricingWithTips3DM_d4904298ab86e1b10dc4a2cf
-- status  : Definition
-- author  : @qmaai2907271020
-- created : 2026-10-22T20:51:41.42717+00:00
-- url     : https://prove2.me/theorems/f8259e97-78ab-48f8-b537-5f545926c984
-- title:
--   PricingWithTips 3DM dependency: CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralClique.OccurrenceReduction.Machine.Occurrences
-- statement:
--   A private, kernel-checked dependency module used by the formal NP-hardness proof for three-dimensional matching and Theorems 4.1 and 4.2 of arXiv:2507.10872.
-- source:
--   https://github.com/tanktechnology/CLRS-Lean

import Definitions.Def_PricingWithTips3DM_a0617eb55b13f160277f4218
import Definitions.Def_PricingWithTips3DM_29d6d64e2e63e0eda9750402
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false

/-!
# Canonical occurrence-descriptor stream

The existing linear occurrence relabeler is reused after raw CNF
normalization.  The resulting stream contains an explicit `vertexMark` before
each decoded literal and retains clause boundaries, polarity, and unary
variable indices.  It is the canonical machine input for the later numeric
edge generator.
-/

noncomputable section

namespace CLRS
namespace Chapter34
namespace Turing
namespace TMClique

/-- Canonical occurrence stream of the CNF decoded from an arbitrary input. -/
def canonicalOccurrenceStream (input : List CNFSym) : List GraphSym :=
  relabel (normalizeCNFInput input)

/-- Pure identification of the descriptor stream with the decoded CNF. -/
theorem canonicalOccurrenceStream_eq (input : List CNFSym) :
    canonicalOccurrenceStream input = relabel (encCNF (decodeCNF input)) := by
  simp [canonicalOccurrenceStream, normalizeCNFInput_eq_encCNF_decodeCNF]

/-- Normalization followed by occurrence marking is one composed
polynomial-time TM2. -/
noncomputable def canonicalOccurrenceStream_computableInPolyTime :
    _root_.Turing.TM2ComputableInPolyTime id id
      canonicalOccurrenceStream := by
  let composed :=
    _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch
      normalizeCNFInput_computableInPolyTime
      cliqueComputableInPolyTime
  change _root_.Turing.TM2ComputableInPolyTime id id
    (fun input => relabel (normalizeCNFInput input))
  simpa [Function.comp_def] using Classical.choice composed

end TMClique
end Turing
end Chapter34
end CLRS


