-- Prove2me | Definitions.Def_PricingWithTips3DM_a24b63b7f54ee231b2f69f5e
-- name    : PricingWithTips3DM_a24b63b7f54ee231b2f69f5e
-- status  : Definition
-- author  : @qmaai2907271020
-- created : 2026-10-22T20:37:17.471796+00:00
-- url     : https://prove2.me/theorems/0ae460f6-96e3-44ea-a49e-525f7ca16132
-- title:
--   PricingWithTips 3DM dependency: CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralClique.Language
-- statement:
--   A private, kernel-checked dependency module used by the formal NP-hardness proof for three-dimensional matching and Theorems 4.1 and 4.2 of arXiv:2507.10872.
-- source:
--   https://github.com/tanktechnology/CLRS-Lean

import Definitions.Def_PricingWithTips3DM_a6f12e82e39df26683946dd8
import Definitions.Def_PricingWithTips3DM_3e204cff19d090c0cf77322e
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false

/-!
# The honest serialized general CLIQUE language

The language accepts exactly complete decodings of well-formed finite graphs
that contain a clique of the explicitly encoded target size.  Malformed and
decoded-but-ill-formed strings are no-instances.
-/

namespace CLRS
namespace Chapter34

/-! ## Raw language and typed bridge -/

/-- General graph-plus-{lit}`k` CLIQUE over the unique {lit}`CliqueSym` grammar. -/
def GeneralCLIQUE : Language CliqueSym :=
  { input |
      ∃ I, decodeCliqueInstance input = some I ∧ I.WellFormed ∧ I.HasClique }

/-- Exact raw-string membership characterization for general CLIQUE. -/
theorem mem_generalCLIQUE_iff (input : List CliqueSym) :
    input ∈ GeneralCLIQUE ↔
      ∃ I, decodeCliqueInstance input = some I ∧ I.WellFormed ∧ I.HasClique := by
  rfl

/-- A canonical instance encoding belongs to general CLIQUE exactly when the
underlying graph representation is well formed and has the requested clique. -/
theorem encodeCliqueInstance_mem_generalCLIQUE_iff (I : CliqueInstance) :
    encodeCliqueInstance I ∈ GeneralCLIQUE ↔ I.WellFormed ∧ I.HasClique := by
  simp [GeneralCLIQUE, decode_encodeCliqueInstance]

/-- A string rejected by the complete instance parser is outside general
CLIQUE. -/
theorem not_mem_generalCLIQUE_of_decode_none {input : List CliqueSym}
    (hdecode : decodeCliqueInstance input = none) : input ∉ GeneralCLIQUE := by
  simp [GeneralCLIQUE, hdecode]

end Chapter34
end CLRS


