-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_TopLeTranslate
-- name    : Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_TopLeTranslate
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T12:59:23.450958+00:00
-- url     : https://prove2.me/theorems/ef167f21-2f26-41f9-bd61-9b929d00b8b4
-- title:
--   Top Le Translate
-- statement:
--   Definitions and structural lemmas for Top Le Translate, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/TopLeTranslate.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_SignSwap
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_KeyFormula_IsSquareDeterminantComparison
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_IsPluriharmonicSiegel
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_MapsAtLeA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_OneEqSpTranslZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyKa
noncomputable section
namespace GlobalTheory.KaUnique
variable {T T' : Type} [CommRing T] [CommRing T'] {X : Scheme.{0}}
def evalHom (w : Sp T ⟶ X) (U : X.Opens) (h : ⊤ ≤ w ⁻¹ᵁ U) : Γ(X, U) →+* T :=
  (w.appLE U ⊤ h ≫ (Scheme.ΓSpecIso (CommRingCat.of T)).hom).hom
theorem valT_eq (w : Sp T ⟶ X) (U : X.Opens) (h : ⊤ ≤ w ⁻¹ᵁ U) (f : Γ(X, U)) : valT w U f = evalHom w U h f :=
  dif_pos h
theorem valT_res (w : Sp T ⟶ X) {U V : X.Opens} (hle : V ≤ U) (h : ⊤ ≤ w ⁻¹ᵁ V) (f : Γ(X, U)) :
    valT w V (rs X hle f) = valT w U f := by
  have h' : ⊤ ≤ w ⁻¹ᵁ U := fun p hp => hle (h hp)
  rw [valT_eq w V h, valT_eq w U h']
  change ((X.presheaf.map (homOfLE hle).op ≫ w.appLE V ⊤ h) ≫ _).hom f = _
  rw [Scheme.Hom.map_appLE]
  rfl
theorem valT_cst (w : Sp T ⟶ X) (π : X ⟶ Sp T) (hw : w ≫ π = 𝟙 _) (U : X.Opens) (h : ⊤ ≤ w ⁻¹ᵁ U) (a : T) :
    valT w U (cst π U a) = a := by
  have e := valT_res w (le_top : U ≤ ⊤) h (π.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of T)).inv.hom a))
  refine e.trans ?_
  rw [valT_eq w ⊤ (fun _ _ => trivial)]
  have e2 : w.appLE ⊤ ⊤ (fun _ _ => trivial) = w.appTop := by
    rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]; rfl
  unfold evalHom
  rw [e2]
  change ((Scheme.ΓSpecIso (CommRingCat.of T)).inv ≫ (π.appTop ≫ w.appTop) ≫ (Scheme.ΓSpecIso (CommRingCat.of T)).hom).hom a = a
  rw [← Scheme.Hom.comp_appTop, hw]
  simp
def trU (w : Sp T ⟶ X) (L : LB X) (c c' : L.ι) (h : ⊤ ≤ w ⁻¹ᵁ L.U c) (h' : ⊤ ≤ w ⁻¹ᵁ L.U c') : Tˣ :=
  Units.map (evalHom w (L.U c ⊓ L.U c') (fun _ hp => ⟨h hp, h' hp⟩)).toMonoidHom (L.g c c')
variable {R : Type} [CommRing R]
end GlobalTheory.KaUnique
end
noncomputable section
namespace GlobalTheory.KaUnique
section Comb
variable {R : Type} [CommRing R] {X : Scheme.{0}} (π : X ⟶ Sp R) (L : LB X)
def IsComb {N : ℕ} (b : Fin N → ∀ i, Γ(X, L.U i)) (c : Fin N → R) (f : ∀ i, Γ(X, L.U i)) : Prop :=
  ∀ i, f i = ∑ k, cst π (L.U i) (c k) * b k i
variable {π L}
theorem IsComb.mulVec {N N' : ℕ} {b : Fin N → ∀ i, Γ(X, L.U i)} {b' : Fin N' → ∀ i, Γ(X, L.U i)}
    {M : Matrix (Fin N) (Fin N') R} {u f : ∀ i, Γ(X, L.U i)} {e : Fin N' → R}
    (hM : ∀ k, IsComb π L b (fun k' => M k' k) (fun i => u i * b' k i)) (he : IsComb π L b' e f) :
    IsComb π L b (M.mulVec e) (fun i => u i * f i) := by
  intro i
  simp only [he i, Finset.mul_sum, Matrix.mulVec, dotProduct, map_sum, map_mul, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  have := hM k i
  simp only at this
  rw [mul_left_comm, this, Finset.mul_sum]
  exact Finset.sum_congr rfl fun k' _ => by ring
theorem IsComb.valT {N : ℕ} {b : Fin N → ∀ i, Γ(X, L.U i)} {c : Fin N → R} {f : ∀ i, Γ(X, L.U i)}
    (h : IsComb π L b c f) (w : Sp R ⟶ X) (hw : w ≫ π = 𝟙 _) (i : L.ι) (hi : ⊤ ≤ w ⁻¹ᵁ L.U i) :
    valT w (L.U i) (f i) = ∑ k, valT w (L.U i) (b k i) * c k := by
  rw [h i, valT_eq w _ hi, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_mul, ← valT_eq, ← valT_eq, valT_cst w π hw _ hi, mul_comm]
def combSec {M : LB X} {N : ℕ} (b : Fin N → LB.Sec M) (c : Fin N → R) : LB.Sec M where
  f := fun i => ∑ k, cst π (M.U i) (c k) * (b k).f i
  compat := fun i j => by
    rw [map_sum, map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_mul, map_mul, (b k).compat i j, rs_cst, rs_cst]
    ring
end Comb
variable {R : Type} [CommRing R]
abbrev fam (x : KeyIn R) {l N : ℕ} (b : Fin N → RR x l) : Fin N → ∀ i, Γ(x.P.A.left, x.P.L.U i) := fun k => (b k).f
end GlobalTheory.KaUnique
end


