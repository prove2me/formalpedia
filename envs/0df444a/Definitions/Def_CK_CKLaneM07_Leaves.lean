-- Prove2me | Definitions.Def_CK_CKLaneM07_Leaves
-- name    : CK_CKLaneM07_Leaves
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-06T08:01:02.939002+00:00
-- url     : https://prove2.me/theorems/f1b077f7-306b-47ba-ab9b-2e1bd69f7b33
-- title:
--   Courtade–Kumar proof module `CKLaneM07.Leaves` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneM07.Leaves` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneM07.Leaves` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneM07.Leaves (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneM07/Leaves.lean)

import Definitions.Def_CK_CKLaneM07_FleetT_T0000__5
import Definitions.Def_CK_CKLaneM07_FleetT_T0005__4
import Definitions.Def_CK_CKLaneM07_FleetT_T0009__5
import Definitions.Def_CK_CKLaneM07_FleetT_T0014__4
import Definitions.Def_CK_CKLaneM07_FleetT_T0018__4
import Definitions.Def_CK_CKLaneM07_FleetT_T0022__4
import Definitions.Def_CK_CKLaneM07_FleetT_T0026__4
import Definitions.Def_CK_CKLaneM07_FleetT_T0030__3
import Definitions.Def_CK_CKLaneM07_G3Adapter

-- ===== source module CKLaneM07.Leaves =====
section

/-!
# Lane M07: all archived same-side `derivative` leaves

`allLeaves` is the concatenation of the 33 fleet shards (3205 leaves, each an archived
path of `same_side/ADAPT_RESULT.json` with owner `derivative`, sha256
b134020b83227cdfb54ec8a85cebf00a67bc2537320b0731836fbc8f324fe9c8).  `allLeaves_sound` proves the semantic owner statement
`SemSBox (ssBox p)` on the exact archived leaf box of every path `p`.
-/

set_option maxRecDepth 100000

namespace CKLaneM07.Leaves
open CKLaneM07

theorem sound_append {L1 L2 : List (List ℕ × Wit)}
    (h1 : ∀ x ∈ L1, SemSBox (ssBox x.1)) (h2 : ∀ x ∈ L2, SemSBox (ssBox x.1)) :
    ∀ x ∈ L1 ++ L2, SemSBox (ssBox x.1) := by
  intro x hx
  rcases List.mem_append.mp hx with h | h
  · exact h1 x h
  · exact h2 x h

/-- All archived derivative leaves with their witnesses. -/
def allLeaves : List (List ℕ × Wit) :=
  CKLaneM07.FleetT.T0000.L ++ (CKLaneM07.FleetT.T0001.L ++ (CKLaneM07.FleetT.T0002.L ++ (CKLaneM07.FleetT.T0003.L ++ (CKLaneM07.FleetT.T0004.L ++ (CKLaneM07.FleetT.T0005.L ++ (CKLaneM07.FleetT.T0006.L ++ (CKLaneM07.FleetT.T0007.L ++ (CKLaneM07.FleetT.T0008.L ++ (CKLaneM07.FleetT.T0009.L ++ (CKLaneM07.FleetT.T0010.L ++ (CKLaneM07.FleetT.T0011.L ++ (CKLaneM07.FleetT.T0012.L ++ (CKLaneM07.FleetT.T0013.L ++ (CKLaneM07.FleetT.T0014.L ++ (CKLaneM07.FleetT.T0015.L ++ (CKLaneM07.FleetT.T0016.L ++ (CKLaneM07.FleetT.T0017.L ++ (CKLaneM07.FleetT.T0018.L ++ (CKLaneM07.FleetT.T0019.L ++ (CKLaneM07.FleetT.T0020.L ++ (CKLaneM07.FleetT.T0021.L ++ (CKLaneM07.FleetT.T0022.L ++ (CKLaneM07.FleetT.T0023.L ++ (CKLaneM07.FleetT.T0024.L ++ (CKLaneM07.FleetT.T0025.L ++ (CKLaneM07.FleetT.T0026.L ++ (CKLaneM07.FleetT.T0027.L ++ (CKLaneM07.FleetT.T0028.L ++ (CKLaneM07.FleetT.T0029.L ++ (CKLaneM07.FleetT.T0030.L ++ (CKLaneM07.FleetT.T0031.L ++ (CKLaneM07.FleetT.T0032.L))))))))))))))))))))))))))))))))

/-- The archived derivative paths. -/
def derivativePaths : List (List ℕ) := allLeaves.map Prod.fst

theorem allLeaves_sound : ∀ x ∈ allLeaves, SemSBox (ssBox x.1) :=
  sound_append CKLaneM07.FleetT.T0000.L_sound (sound_append CKLaneM07.FleetT.T0001.L_sound (sound_append CKLaneM07.FleetT.T0002.L_sound (sound_append CKLaneM07.FleetT.T0003.L_sound (sound_append CKLaneM07.FleetT.T0004.L_sound (sound_append CKLaneM07.FleetT.T0005.L_sound (sound_append CKLaneM07.FleetT.T0006.L_sound (sound_append CKLaneM07.FleetT.T0007.L_sound (sound_append CKLaneM07.FleetT.T0008.L_sound (sound_append CKLaneM07.FleetT.T0009.L_sound (sound_append CKLaneM07.FleetT.T0010.L_sound (sound_append CKLaneM07.FleetT.T0011.L_sound (sound_append CKLaneM07.FleetT.T0012.L_sound (sound_append CKLaneM07.FleetT.T0013.L_sound (sound_append CKLaneM07.FleetT.T0014.L_sound (sound_append CKLaneM07.FleetT.T0015.L_sound (sound_append CKLaneM07.FleetT.T0016.L_sound (sound_append CKLaneM07.FleetT.T0017.L_sound (sound_append CKLaneM07.FleetT.T0018.L_sound (sound_append CKLaneM07.FleetT.T0019.L_sound (sound_append CKLaneM07.FleetT.T0020.L_sound (sound_append CKLaneM07.FleetT.T0021.L_sound (sound_append CKLaneM07.FleetT.T0022.L_sound (sound_append CKLaneM07.FleetT.T0023.L_sound (sound_append CKLaneM07.FleetT.T0024.L_sound (sound_append CKLaneM07.FleetT.T0025.L_sound (sound_append CKLaneM07.FleetT.T0026.L_sound (sound_append CKLaneM07.FleetT.T0027.L_sound (sound_append CKLaneM07.FleetT.T0028.L_sound (sound_append CKLaneM07.FleetT.T0029.L_sound (sound_append CKLaneM07.FleetT.T0030.L_sound (sound_append CKLaneM07.FleetT.T0031.L_sound (CKLaneM07.FleetT.T0032.L_sound))))))))))))))))))))))))))))))))

/-- **Population theorem**: every archived derivative leaf box satisfies the owner statement. -/
theorem derivative_leaves_sem : ∀ p ∈ derivativePaths, SemSBox (ssBox p) := by
  intro p hp
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hp
  exact allLeaves_sound x hx

theorem derivativePaths_length : derivativePaths.length = 3205 := by decide +kernel

/-- **Population theorem, canonical form** (`CKLaneG3.SCover`, BRIEF §7): every archived derivative
leaf path carries the `SS_Compact` per-leaf obligation on the canonical box `CKLaneG3.sBox p`. -/
theorem derivative_sLeafOK : ∀ p ∈ derivativePaths, CKLaneG3.SLeafOK (CKLaneG3.sBox p) :=
  fun p hp => sLeafOK_of_semSBox (derivative_leaves_sem p hp)

end CKLaneM07.Leaves

end


