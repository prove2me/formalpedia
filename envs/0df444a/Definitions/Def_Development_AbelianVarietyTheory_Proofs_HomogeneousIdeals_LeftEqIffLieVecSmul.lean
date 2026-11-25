-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_LeftEqIffLieVecSmul
-- name    : Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_LeftEqIffLieVecSmul
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-25T15:15:45.109381+00:00
-- url     : https://prove2.me/theorems/5c0efd5a-6f11-550a-bde4-849f8b6e869f
-- title:
--   Left Eq Iff Lie Vec Smul
-- statement:
--   Definitions and structural lemmas for Left Eq Iff Lie Vec Smul, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/LeftEqIffLieVecSmul.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsLieBasis
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_EigLatBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_LocallyOfFinitePresentationDiagMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_FormallyUnramifiedOfTangentMapInjective
import Theorems.Thm_GlobalTheory_Diag_coord_ofChar
import Theorems.Thm_GlobalTheory_Diag_coord_single_add
import Theorems.Thm_GlobalTheory_Diag_coord_single_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Semi.Rosenlicht
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR epsScaleR IsTangent IsLieComb IsLieBasis OAct epsPt
  IsLieEigen LieMult)
open ReciprocityTheory.ChartRestriction.G.Chart (dualMapR)
open TrivSqZeroExt (inl inr)
namespace GlobalTheory.Diag
section Act
variable (S : Scheme.{0}) (O : Type) [CommRing O] (X : Type) [AddCommGroup X] [Module O X]
def diagAct : OAct O (splitTorus S X) where
  act a := diagMap S (DistribSMul.toAddMonoidHom X a)
  hom _ := inferInstance
  one := by
    rw [← diagMap_id]; congr 1; ext x; simp
  mul a b := by
    rw [← diagMap_comp]; congr 1; ext x; simp [mul_smul]
  add a b := by
    rw [← diagMap_add]; congr 1; ext x; simp [add_smul]
end Act
section Val
variable {S : Scheme.{0}} {A : Type} [CommRing A] {g : Sp A ⟶ S}
  {X Y : Type} [AddCommGroup X] [AddCommGroup Y]
def charVal (w : Over.mk g ⟶ splitTorus S X) (x : X) : A :=
  (Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom (w.left.appTop.hom (chi X x))
theorem charVal_eq_coord (w : Over.mk g ⟶ splitTorus S X) (x : X) :
    charVal w x = (Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom
      ((coord w).hom (AddMonoidAlgebra.single x 1)) := by
  simp [charVal, chi, coord]
  rfl
theorem charVal_ext {v w : Over.mk g ⟶ splitTorus S X} (h : ∀ x, charVal v x = charVal w x) :
    v = w := by
  refine hom_ext fun x => ?_
  have e := congrArg (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom (h x)
  simpa [charVal_eq_coord] using e
theorem charVal_one (x : X) : charVal (1 : Over.mk g ⟶ splitTorus S X) x = 1 := by
  rw [charVal_eq_coord, coord_one, map_one]
theorem charVal_zero (w : Over.mk g ⟶ splitTorus S X) : charVal w 0 = 1 := by
  rw [charVal_eq_coord, coord_single_zero, map_one]
theorem charVal_add (w : Over.mk g ⟶ splitTorus S X) (x y : X) :
    charVal w (x + y) = charVal w x * charVal w y := by
  rw [charVal_eq_coord, charVal_eq_coord, charVal_eq_coord, coord_single_add, map_mul]
theorem charVal_eq_torusFst (w : Over.mk g ⟶ splitTorus S X) (x : X) :
    charVal w x = (Spec.preimage (w.left ≫ torusFst S X)).hom (AddMonoidAlgebra.single x 1) := by
  obtain ⟨φ, hφ⟩ : ∃ φ, Spec.map φ = w.left ≫ torusFst S X := ⟨_, Spec.map_preimage _⟩
  rw [charVal_eq_coord]
  unfold coord
  rw [← hφ, Spec.preimage_map]
  have e := congrArg (fun k => k.hom ((Scheme.ΓSpecIso (torusRing ZU X)).inv.hom (AddMonoidAlgebra.single x 1)))
    (Scheme.ΓSpecIso_naturality φ)
  refine e.trans ?_
  simp
theorem torusFst_eq_iff {S' : Scheme.{0}} {A' : Type} [CommRing A'] {g' : Sp A' ⟶ S'} (φ : A →+* A')
    (w' : Over.mk g' ⟶ splitTorus S' X) (w : Over.mk g ⟶ splitTorus S X) :
    w'.left ≫ torusFst S' X = spMap φ ≫ w.left ≫ torusFst S X ↔
      ∀ x, charVal w' x = φ (charVal w x) := by
  obtain ⟨φ1, h1⟩ : ∃ φ1, Spec.map φ1 = w'.left ≫ torusFst S' X := ⟨_, Spec.map_preimage _⟩
  obtain ⟨φ2, h2⟩ : ∃ φ2, Spec.map φ2 = w.left ≫ torusFst S X := ⟨_, Spec.map_preimage _⟩
  simp only [charVal_eq_torusFst, ← h1, ← h2, Spec.preimage_map, spMap, ← Spec.map_comp]
  rw [Spec.map_inj]
  constructor
  · intro h x
    rw [h]
    rfl
  · intro h
    ext1
    apply AddMonoidAlgebra.ringHom_ext
    · intro b
      have := RingHom.congr_fun (RingHom.ext_int
        ((φ1.hom.comp AddMonoidAlgebra.singleZeroRingHom).comp (ULift.ringEquiv : ULift ℤ ≃+* ℤ).symm.toRingHom)
        (((φ2 ≫ CommRingCat.ofHom φ).hom.comp AddMonoidAlgebra.singleZeroRingHom).comp
          (ULift.ringEquiv : ULift ℤ ≃+* ℤ).symm.toRingHom)) b.down
      exact this
    · intro x
      simpa using h x
theorem left_eq_iff {A' : Type} [CommRing A'] {g' : Sp A' ⟶ S} (φ : A →+* A') (hg : g' = spMap φ ≫ g)
    (w' : Over.mk g' ⟶ splitTorus S X) (w : Over.mk g ⟶ splitTorus S X) :
    w'.left = spMap φ ≫ w.left ↔ ∀ x, charVal w' x = φ (charVal w x) := by
  rw [← torusFst_eq_iff φ w' w]
  constructor
  · intro h
    rw [h, Category.assoc]
  · intro h
    apply pullback.hom_ext
    · rw [← Category.assoc] at h
      exact h
    · have e1 := Over.w w'
      have e2 := Over.w w
      simp only [Over.mk_hom] at e1 e2
      change w'.left ≫ (splitTorus S X).hom = (spMap φ ≫ w.left) ≫ (splitTorus S X).hom
      rw [e1, Category.assoc, e2, hg]
variable (g) in

def ofVal (f : Multiplicative X →* A) : Over.mk g ⟶ splitTorus S X :=
  ofChar _ ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom.toMonoidHom.comp f)
theorem charVal_ofVal (f : Multiplicative X →* A) (x : X) :
    charVal (ofVal g f) x = f (Multiplicative.ofAdd x) := by
  rw [charVal_eq_coord, ofVal, coord_ofChar]
  simp
end Val
section Eps
variable {S : Scheme.{0}} {R : Type} [CommRing R] {g : Sp (DualNumber R) ⟶ S}
  {X Y : Type} [AddCommGroup X] [AddCommGroup Y]
variable (g) in

def epsVec (c : X →+ R) : Over.mk g ⟶ splitTorus S X :=
  ofVal g
    { toFun := fun x => 1 + inr (c x.toAdd)
      map_one' := by simp
      map_mul' := fun x y => by ext <;> simp [add_comm] }
theorem charVal_epsVec (c : X →+ R) (x : X) : charVal (epsVec g c) x = 1 + inr (c x) := by
  rw [epsVec, charVal_ofVal]
  rfl
theorem epsVec_injective : Function.Injective (epsVec g : (X →+ R) → _) := by
  intro c d h
  ext x
  have e := congrArg (fun w => (charVal w x).snd) h
  simpa [charVal_epsVec] using e
def epsCoeff (w : Over.mk g ⟶ splitTorus S X) (hw : ∀ x, (charVal w x).fst = 1) : X →+ R where
  toFun x := (charVal w x).snd
  map_zero' := by rw [charVal_zero]; rfl
  map_add' x y := by rw [charVal_add]; simp [hw, add_comm]
theorem epsVec_epsCoeff (w : Over.mk g ⟶ splitTorus S X) (hw : ∀ x, (charVal w x).fst = 1) :
    epsVec g (epsCoeff w hw) = w := by
  refine charVal_ext fun x => ?_
  rw [charVal_epsVec]
  ext
  · simp [hw x]
  · simp [epsCoeff]
theorem exists_epsVec_iff (w : Over.mk g ⟶ splitTorus S X) :
    (∃ c, epsVec g c = w) ↔ ∀ x, (charVal w x).fst = 1 := by
  constructor
  · rintro ⟨c, rfl⟩ x
    simp [charVal_epsVec]
  · intro h
    exact ⟨epsCoeff w h, epsVec_epsCoeff w h⟩
theorem reduces_iff {t : Sp R ⟶ S} (ht : t = spMap (TrivSqZeroExt.fstHom R R R).toRingHom ≫ g)
    (w : Over.mk g ⟶ splitTorus S X) :
    spMap (TrivSqZeroExt.fstHom R R R).toRingHom ≫ w.left = (1 : Over.mk t ⟶ splitTorus S X).left ↔
      ∀ x, (charVal w x).fst = 1 := by
  rw [eq_comm, left_eq_iff _ ht]
  simp [charVal_one, eq_comm]
theorem fstHom_base :
    spMap (TrivSqZeroExt.fstHom R R R).toRingHom ≫ spMap (algebraMap R (DualNumber R)) = 𝟙 _ := by
  simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  convert Spec.map_id (CommRingCat.of R)
  ext r
  simp
end Eps
section Lie
variable {R : Type} [CommRing R] {X Y : Type} [AddCommGroup X] [AddCommGroup Y]
def lieVec (c : X →+ R) : epsR R ⟶ splitTorus (Sp R) X := epsVec _ c
theorem isTangent_iff_charVal (w : epsR R ⟶ splitTorus (Sp R) X) :
    IsTangent w ↔ ∀ x, (charVal w x).fst = 1 := by
  unfold IsTangent
  convert reduces_iff (t := 𝟙 _) fstHom_base.symm w using 2
  show _ = Over.Hom.left (toUnit (Over.mk (𝟙 (Sp R))) ≫ η)
  rw [Over.comp_left]
  exact (Category.id_comp _).symm
theorem isTangent_iff_exists (w : epsR R ⟶ splitTorus (Sp R) X) :
    IsTangent w ↔ ∃ c, lieVec c = w := by
  rw [isTangent_iff_charVal]
  exact (exists_epsVec_iff w).symm
theorem isTangent_lieVec (c : X →+ R) : IsTangent (lieVec c) := (isTangent_iff_exists _).2 ⟨c, rfl⟩
variable (R X) in

def lieEquiv : {w : epsR R ⟶ splitTorus (Sp R) X // IsTangent w} ≃ (X →+ R) where
  toFun w := epsCoeff w.1 ((isTangent_iff_charVal _).1 w.2)
  invFun c := ⟨lieVec c, isTangent_lieVec c⟩
  left_inv _ := Subtype.ext (epsVec_epsCoeff _ _)
  right_inv _ := epsVec_injective (epsVec_epsCoeff _ _)
def transpose (R : Type) [CommRing R] (u : Y →+ X) : (X →+ R) →ₗ[R] (Y →+ R) where
  toFun c := c.comp u
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
section Basis
variable {I J : Type} [Fintype I] [Fintype J]
variable (R) in

def dualBasis (b : Module.Basis I ℤ X) : Module.Basis I R (X →+ R) :=
  Module.Basis.ofEquivFun
    { toFun := fun c i => c (b i)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      invFun := fun f => (b.constr ℤ f).toAddMonoidHom
      left_inv := fun c => congrArg LinearMap.toAddMonoidHom
        (b.constr_eq (S := ℤ) (f := c.toIntLinearMap) fun _ => rfl)
      right_inv := fun f => funext fun i => b.constr_basis ℤ f i }
end Basis
instance free_addHom [Module.Free ℤ X] [Module.Finite ℤ X] : Module.Free R (X →+ R) :=
  Module.Free.of_basis (dualBasis R (Module.Free.chooseBasis ℤ X))
instance finite_addHom [Module.Free ℤ X] [Module.Finite ℤ X] : Module.Finite R (X →+ R) :=
  Module.Finite.of_basis (dualBasis R (Module.Free.chooseBasis ℤ X))
end Lie
section Fibre
variable {S : Scheme.{0}} {k : Type} [Field k] (t : Sp k ⟶ S) {O : Type} [CommRing O]
  {X : Type} [AddCommGroup X] [Module O X] (τ : O →+* k)
variable (X) in

def eigenHom {k : Type} [CommRing k] (τ : O →+* k) : Submodule k (X →+ k) where
  carrier := {c | ∀ (a : O) (x : X), c (a • x) = τ a * c x}
  add_mem' hc hd a x := by simp [hc a x, hd a x, mul_add]
  zero_mem' a x := by simp
  smul_mem' r c hc a x := by simp [hc a x, mul_left_comm]
end Fibre
end GlobalTheory.Diag
namespace GlobalTheory
open Diag
end GlobalTheory


