-- Prove2me | Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_KaehlerRingIso
-- name    : QEC_Coding_AlgebraicGeometry_Differentials_KaehlerRingIso
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T11:52:45.701955+00:00
-- url     : https://prove2.me/theorems/777ee7a3-e823-4741-8a83-dd0172c2674e
-- title:
--   Kaehler Ring Iso
-- statement:
--   Definitions and structural lemmas for Kaehler Ring Iso, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Differentials/KaehlerRingIso.lean

import Mathlib.Algebra.Category.ModuleCat.Differentials.Basic
set_option autoImplicit false
namespace QEC.Coding.AlgebraicGeometry
open CategoryTheory
noncomputable section
universe u
variable {k B B' : CommRingCat.{u}} (phi : k ⟶ B) (psi : k ⟶ B')
  (e : B ≅ B') (h : phi ≫ e.hom = psi)
include h in
lemma kaehlerRingIso_inverse_square : psi ≫ e.inv = phi := by
  rw [← h, Category.assoc, e.hom_inv_id, Category.comp_id]
def kaehlerRingIso_forward : CommRingCat.KaehlerDifferential phi ⟶
    (ModuleCat.restrictScalars e.hom.hom).obj (CommRingCat.KaehlerDifferential psi) :=
  CommRingCat.KaehlerDifferential.map (g := 𝟙 k) (g' := e.hom)
    ((Category.id_comp psi).trans h.symm)
def kaehlerRingIso_backward : CommRingCat.KaehlerDifferential psi ⟶
    (ModuleCat.restrictScalars e.inv.hom).obj (CommRingCat.KaehlerDifferential phi) :=
  CommRingCat.KaehlerDifferential.map (g := 𝟙 k) (g' := e.inv)
    ((Category.id_comp phi).trans (kaehlerRingIso_inverse_square phi psi e h).symm)
end
end QEC.Coding.AlgebraicGeometry


