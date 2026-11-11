-- Prove2me | Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_HistoryComponentMask
-- name    : QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_HistoryComponentMask
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-10T07:00:42.187938+00:00
-- url     : https://prove2.me/theorems/1855a8e3-c842-4e63-bed3-c6d52f272692
-- title:
--   History Component Mask
-- statement:
--   Definitions and structural lemmas for History Component Mask, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/HistoryComponentMask.lean

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_HistoryWitness
import Theorems.Thm_QEC_Coding_BDL26OwnerIncidenceMasks_outputMarks_contains_syndrome

set_option autoImplicit false
namespace QEC.Coding.BDL26OwnerIncidenceMasks
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder MultiscaleDecoder
open scoped Classical
abbrev StrictLowerNode := Σ i : Fin 4, GraphVertex scaleFive i.val
noncomputable def includeLowerNode (v : StrictLowerNode) : BDL26TopOwnerIsolation.Node :=
  ⟨v.1.castSucc, v.2⟩
noncomputable def marksWithLower (lower : Finset StrictLowerNode) : Finset BDL26TopOwnerIsolation.Node :=
  witnessTopMarks.image BDL26TopOwnerIsolation.topNode ∪ lower.image includeLowerNode
theorem marksWithLower_top_iff (lower : Finset StrictLowerNode)
    (v : Vertex (state scaleFive 3).presentation) :
    BDL26TopOwnerIsolation.topNode v ∈ marksWithLower lower ↔ v ∈ witnessTopMarks := by
  constructor
  · intro h
    rcases Finset.mem_union.mp h with ht | hl
    · obtain ⟨w, hw, he⟩ := Finset.mem_image.mp ht
      have hv : w = v := by cases he; rfl
      exact hv ▸ hw
    · obtain ⟨w, _, he⟩ := Finset.mem_image.mp hl
      have hv := congrArg (fun p : BDL26TopOwnerIsolation.Node => p.1.val) he
      change w.1.val = 4 at hv
      have hlt := w.1.isLt
      omega
  · intro h
    exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨v, h, rfl⟩)
theorem marksWithLower_active (lower : Finset StrictLowerNode)
    (p : FamilyZ scaleFive 4 (4 : LevelIndex 4)) (hp : witnessUpper.val p ≠ 0) :
    BDL26TopOwnerIsolation.topNode (witnessTopOwner p) ∈ marksWithLower lower :=
  (marksWithLower_top_iff lower _).mpr
    (outputMarks_contains_syndrome witnessTopOutput witnessTopOwner witnessTopComponentOwner p hp)
noncomputable def componentWithLower (lower : Finset StrictLowerNode)
    (p : FamilyZ scaleFive 4 (4 : LevelIndex 4)) (hp : witnessUpper.val p ≠ 0) :
    Finset BDL26TopOwnerIsolation.Node :=
  (BDL26TopOwnerIsolation.markedComponent (marksWithLower lower)
    ⟨BDL26TopOwnerIsolation.topNode (witnessTopOwner p), marksWithLower_active lower p hp⟩).image Subtype.val
noncomputable def upperOwnerMaskRegion (K : Finset BDL26TopOwnerIsolation.Node) :
    Finset (FamilyZ scaleFive 4 (4 : LevelIndex 4)) :=
  Finset.univ.filter (fun q => BDL26TopOwnerIsolation.topNode (witnessTopOwner q) ∈ K)
noncomputable def lowerOwnerMaskRegion (K : Finset BDL26TopOwnerIsolation.Node) :
    Finset (FamilyZ scaleFive 4 (3 : LevelIndex 4)) :=
  Finset.univ.filter (fun q => (⟨(3 : Fin 5), witnessNextOwner q⟩ : BDL26TopOwnerIsolation.Node) ∈ K)
end QEC.Coding.BDL26OwnerIncidenceMasks


