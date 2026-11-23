-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsProjByOfIsPullback
-- name    : Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsProjByOfIsPullback
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T03:38:36.778502+00:00
-- url     : https://prove2.me/theorems/2d7df7c9-f10f-4e6e-b00b-969add2047c4
-- title:
--   Is Proj By Of Is Pullback
-- statement:
--   Definitions and structural lemmas for Is Proj By Of Is Pullback, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/IsProjByOfIsPullback.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
noncomputable section
namespace GlobalTheory.AbLaw.Segre
variable {X Y P : Scheme.{0}} {R : Type} [CommRing R]
def ap (p : P ⟶ X) {U : X.Opens} {W : P.Opens} (h : W ≤ p ⁻¹ᵁ U) : Γ(X, U) →+* Γ(P, W) :=
  (p.appLE U W h).hom
theorem rs_ap (p : P ⟶ X) {U : X.Opens} {W W' : P.Opens} (h : W ≤ p ⁻¹ᵁ U) (h' : W' ≤ W) (x : Γ(X, U)) :
    rs P h' (ap p h x) = ap p (h'.trans h) x :=
  congr($(p.appLE_map h (homOfLE h').op).hom x)
theorem ap_rs (p : P ⟶ X) {U U' : X.Opens} {W : P.Opens} (h : W ≤ p ⁻¹ᵁ U') (h' : U' ≤ U) (x : Γ(X, U)) :
    ap p h (rs X h' x) = ap p (h.trans fun _ hy => h' hy) x :=
  congr($(p.map_appLE h (homOfLE h').op).hom x)
theorem le_pre (p : P ⟶ X) {U V : X.Opens} {W : P.Opens} (h : W ≤ p ⁻¹ᵁ U) (h' : W ≤ p ⁻¹ᵁ V) :
    W ≤ p ⁻¹ᵁ (U ⊓ V) := fun _ hy => ⟨h hy, h' hy⟩
def box (p : P ⟶ X) (q : P ⟶ Y) (H : LB X) (K : LB Y) : LB P :=
  ⟨H.ι × K.ι, fun a => p ⁻¹ᵁ H.U a.1 ⊓ q ⁻¹ᵁ K.U a.2, fun a b =>
    Units.map (ap p (le_pre p (inf_le_left.trans inf_le_left) (inf_le_right.trans inf_le_left))).toMonoidHom
      (H.g a.1 b.1) *
    Units.map (ap q (le_pre q (inf_le_left.trans inf_le_right) (inf_le_right.trans inf_le_right))).toMonoidHom
      (K.g a.2 b.2)⟩
variable (p : P ⟶ X) (q : P ⟶ Y) {H : LB X} {K : LB Y}
theorem rs_mul {U : X.Opens} {V : Y.Opens} {W W' : P.Opens} (h₁ : W ≤ p ⁻¹ᵁ U) (h₂ : W ≤ q ⁻¹ᵁ V)
    (h : W' ≤ W) (x : Γ(X, U)) (y : Γ(Y, V)) :
    rs P h (ap p h₁ x * ap q h₂ y) = ap p (h.trans h₁) x * ap q (h.trans h₂) y := by
  rw [map_mul, rs_ap, rs_ap]
theorem ap_compat (s : LB.Sec H) (i j : H.ι) {W : P.Opens} (h₁ : W ≤ p ⁻¹ᵁ H.U i) (h₂ : W ≤ p ⁻¹ᵁ H.U j)
    (h : W ≤ p ⁻¹ᵁ (H.U i ⊓ H.U j)) :
    ap p h₁ (s.f i) = ap p h (H.g i j).val * ap p h₂ (s.f j) := by
  have e : rs X inf_le_left (s.f i) = (H.g i j).val * rs X inf_le_right (s.f j) := s.compat i j
  have e' := congrArg (ap p h) e
  simpa only [ap_rs, map_mul] using e'
def boxSec (s : LB.Sec H) (t : LB.Sec K) : LB.Sec (box p q H K) where
  f := fun a => ap p (W := p ⁻¹ᵁ H.U a.1 ⊓ q ⁻¹ᵁ K.U a.2) inf_le_left (s.f a.1) *
    ap q (W := p ⁻¹ᵁ H.U a.1 ⊓ q ⁻¹ᵁ K.U a.2) inf_le_right (t.f a.2)
  compat := fun a b => by
    refine (rs_mul p q _ _ _ _ _).trans (Eq.trans ?_ (congrArg (_ * ·) (rs_mul p q _ _ _ _ _).symm))
    exact (congrArg₂ (· * ·) (ap_compat p s a.1 b.1 _ _ _) (ap_compat q t a.2 b.2 _ _ _)).trans
      (mul_mul_mul_comm _ _ _ _)
end GlobalTheory.AbLaw.Segre


