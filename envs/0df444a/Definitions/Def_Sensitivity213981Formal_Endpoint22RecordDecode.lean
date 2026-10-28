-- Prove2me | Definitions.Def_Sensitivity213981Formal_Endpoint22RecordDecode
-- name    : Sensitivity213981Formal_Endpoint22RecordDecode
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T17:10:22.391152+00:00
-- url     : https://prove2.me/theorems/f8c297a6-f481-4299-a5ca-1c3eb07987c2
-- title:
--   Endpoint22 Record Decode — sensitivity certificate definitions
-- statement:
--   The definitions for Endpoint22 Record Decode in the Boolean sensitivity construction. This interface preserves the data, predicates, finite structures, and essential constructor facts of the verified source module. All variables, indexing types, and numerical constants have the meanings specified by these definitions. The subsequent certificate theorems establish the required bounds; this interface adds no unproved assumptions.
--
--   The principal source declarations are `ThreeBoundEndpoint22Records.decodeRow`.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; Endpoint22RecordDecode.lean, lines 1–9.

import Definitions.Def_Sensitivity213981Formal_Namespaces
import Definitions.Def_Sensitivity213981Formal_RecordSetLookup
import Definitions.Def_SensitivityCampaign
import Definitions.Def_SensitivitySeparation
import Lean.Elab.Tactic.Omega
import Mathlib.Data.Finset.Sort
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.Sort

namespace Sensitivity213981Formal
section
/- Lossless compact encoding of the concrete relaxed table.
   Every decoded row is still checked through the ordinary Tree interface. -/

set_option autoImplicit false
namespace ThreeBoundEndpoint22Records
def decodeRow : ℕ → ℕ → List ℕ
  | 0, _ => []
  | n+1, x => (if x%16=15 then 1000000 else x%16)::decodeRow n (x/16)
end ThreeBoundEndpoint22Records

end
end Sensitivity213981Formal


