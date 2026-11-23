-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SpecialFibreConnectedOfBaseChange
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_SpecialFibreConnectedOfBaseChange
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T15:25:05.820858+00:00
-- url     : https://prove2.me/theorems/b8ffe5e8-236f-4867-922d-6d839061ab5b
-- title:
--   Special Fibre Connected Of Base Change
-- statement:
--   Definitions and structural lemmas for Special Fibre Connected Of Base Change, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SpecialFibreConnectedOfBaseChange.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_SpecialFibreUnits
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits AlgebraicGeometry
namespace GlobalTheory.FibSurj
open IsLocalRing
section
variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
  {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (φ : V →+* O) [IsLocalHom φ]
  {X : Scheme.{0}} (s : X ⟶ Spec (.of V))
theorem spec_square :
    Spec.map (CommRingCat.ofHom (residue O)) ≫ Spec.map (CommRingCat.ofHom φ) =
      Spec.map (CommRingCat.ofHom (ResidueField.map φ)) ≫ Spec.map (CommRingCat.ofHom (residue V)) := by
  rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
  congr 2
noncomputable def fibMap :
    pullback (pullback.snd s (Spec.map (CommRingCat.ofHom φ))) (Spec.map (CommRingCat.ofHom (residue O))) ⟶
      pullback s (Spec.map (CommRingCat.ofHom (residue V))) :=
  pullback.lift (pullback.fst _ _ ≫ pullback.fst _ _)
    (pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom (ResidueField.map φ))) (by
      simp only [Category.assoc]
      rw [← spec_square, pullback.condition, ← Category.assoc, pullback.condition, Category.assoc])
end
end GlobalTheory.FibSurj


