-- Prove2me | Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IdealPrincipalization_MarkedBlowupSequence_BlowupSequenceData
-- name    : Development_ResolutionOfSingularities_EmbeddedResolution_IdealPrincipalization_MarkedBlowupSequence_BlowupSequenceData
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-24T13:01:31.339431+00:00
-- url     : https://prove2.me/theorems/d882c6fd-7b7e-49ca-a636-b72f78c8571c
-- title:
--   Blowup Sequence Data
-- statement:
--   Definitions and structural lemmas for Blowup Sequence Data, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/IdealPrincipalization/MarkedBlowupSequence/BlowupSequenceData.lean

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IteratedBlowups_BlowupSequenceBasic
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_StrictTransform
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_StrictNormalCrossings
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_IdealSheafOrder
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IdealPrincipalization_MarkedBlowupSequence_IdealBlowupSequence
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IdealPrincipalization_MarkedBlowupSequence_MarkedSequenceOfBlowups
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionOfSingularities
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_IdealBlowupSequence_boundary_succ_eq_map_strictTransform_append
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_MarkedSequenceOfBlowups_projectionToSpec_eq
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_MarkedSequenceOfBlowups_toMarkedSequence_lastIdeal
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_MarkedSequenceOfBlowups_toMarkedSequence_toSequenceOfBlowups
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_SequenceOfBlowups_blowupMorphism_eq_transitionMap
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_SequenceOfBlowups_isBlowupAlongIdealSheaf_blowupMorphism
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_SequenceOfBlowups_projectionToBase_def
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_SequenceOfBlowups_projectionToBase_succ
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_SequenceOfBlowups_projectionToBase_zero
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_SequenceOfBlowups_transitionMap_def
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] FunctorialResolution.EmbeddedResolution.MarkedSequenceOfBlowups.toMarkedSequence_lastIdeal
attribute [local simp] FunctorialResolution.EmbeddedResolution.MarkedSequenceOfBlowups.toMarkedSequence_toSequenceOfBlowups


set_option autoImplicit false
universe u
open CategoryTheory Opposite AlgebraicGeometry
noncomputable section
namespace FunctorialResolution.EmbeddedResolution
structure BlowupSequenceData (X : Scheme.{u}) : Type (u + 1) where
  length : ℕ
  obj : ℕ → Scheme.{u}
  map : ∀ i : ℕ, obj (i + 1) ⟶ obj i
  isoZero : obj 0 ≅ X
  center : ∀ i : ℕ, (obj i).IdealSheafData
  isBlowup : ∀ i, i < length → Blowup.IsBlowupAlongIdealSheaf (map i) (center i)
namespace BlowupSequenceData
variable {X : Scheme.{u}}
def projectionToBase (d : BlowupSequenceData X) : ∀ i : ℕ, d.obj i ⟶ X
  | 0 => d.isoZero.hom
  | (i + 1) => d.map i ≫ projectionToBase d i
@[simp]
theorem projectionToBase_zero (d : BlowupSequenceData X) : projectionToBase d 0 = d.isoZero.hom := rfl
@[simp]
theorem projectionToBase_succ (d : BlowupSequenceData X) (i : ℕ) :
    projectionToBase d (i + 1) = d.map i ≫ projectionToBase d i := rfl
def homAdd (d : BlowupSequenceData X) (i : ℕ) : ∀ k : ℕ, d.obj (i + k) ⟶ d.obj i
  | 0 => 𝟙 (d.obj i)
  | (k + 1) => d.map (i + k) ≫ homAdd d i k
def homOfLE (d : BlowupSequenceData X) {i j : ℕ} (h : i ≤ j) : d.obj j ⟶ d.obj i :=
  eqToHom (congrArg d.obj (Nat.add_sub_cancel' h).symm) ≫ homAdd d i (j - i)
theorem eqToHom_comp_iteratedBlowupMorphism_of_eq_zero (d : BlowupSequenceData X) (i k : ℕ)
    (h : d.obj i = d.obj (i + k)) (hk : k = 0) :
    eqToHom h ≫ homAdd d i k = 𝟙 (d.obj i) := by
  subst hk
  have h1 : homAdd d i 0 = 𝟙 (d.obj i) := rfl
  have h2 : eqToHom h = 𝟙 (d.obj i) := rfl
  rw [h1, h2]
  exact Category.id_comp (𝟙 (d.obj i))
theorem towerMorphism_refl (d : BlowupSequenceData X) (i : ℕ) :
    homOfLE d (le_refl i) = 𝟙 (d.obj i) :=
  eqToHom_comp_iteratedBlowupMorphism_of_eq_zero d i (i - i)
    (congrArg d.obj (Nat.add_sub_cancel' (le_refl i)).symm) (Nat.sub_self i)
theorem iteratedBlowupMorphism_zero (d : BlowupSequenceData X) (i : ℕ) :
    homAdd d i 0 = 𝟙 (d.obj i) := rfl
theorem iteratedBlowupMorphism_succ (d : BlowupSequenceData X) (i k : ℕ) :
    homAdd d i (k + 1) = d.map (i + k) ≫ homAdd d i k := rfl
theorem blowupMorphism_comp_eqToHom (d : BlowupSequenceData X) {n m : ℕ} (h : n = m) :
    d.map n ≫ eqToHom (congrArg d.obj h) =
      eqToHom (show d.obj (n + 1) = d.obj (m + 1) by rw [h]) ≫ d.map m := by
  subst h
  simp
theorem iteratedBlowupMorphism_congr_length (d : BlowupSequenceData X) (i : ℕ) {k k' : ℕ} (h : k = k') :
    homAdd d i k =
      eqToHom (show d.obj (i + k) = d.obj (i + k') by rw [h]) ≫ homAdd d i k' := by
  subst h
  simp
theorem iteratedBlowupMorphism_congr_start (d : BlowupSequenceData X) {i i' : ℕ} (h : i = i') (k : ℕ) :
    homAdd d i k =
      eqToHom (show d.obj (i + k) = d.obj (i' + k) by rw [h]) ≫ homAdd d i' k ≫
        eqToHom (show d.obj i' = d.obj i by rw [h]) := by
  subst h
  simp
theorem iteratedBlowupMorphism_comp_iteratedBlowupMorphism (d : BlowupSequenceData X) (i a b : ℕ) :
    homAdd d (i + a) b ≫ homAdd d i a =
      eqToHom (congrArg d.obj (Nat.add_assoc i a b)) ≫ homAdd d i (a + b) := by
  induction b with
  | zero =>
      show homAdd d (i + a) 0 ≫ homAdd d i a
          = eqToHom (rfl : d.obj (i + a) = d.obj (i + a)) ≫ homAdd d i a
      rw [iteratedBlowupMorphism_zero, eqToHom_refl, Category.id_comp]
      exact Category.id_comp _
  | succ b ih =>
      rw [iteratedBlowupMorphism_succ, Category.assoc, ih, ← Category.assoc,
        blowupMorphism_comp_eqToHom d (Nat.add_assoc i a b), Category.assoc]
      rfl
theorem towerMorphism_eq_iteratedBlowupMorphism (d : BlowupSequenceData X) {i j : ℕ} (h : i ≤ j) (k : ℕ)
    (hk : j = i + k) :
    homOfLE d h = eqToHom (congrArg d.obj hk) ≫ homAdd d i k := by
  subst hk
  unfold homOfLE
  rw [iteratedBlowupMorphism_congr_length d i (show i + k - i = k by omega)]
  simp
theorem towerMorphism_comp (d : BlowupSequenceData X) {i j l : ℕ} (hij : i ≤ j) (hjl : j ≤ l) :
    homOfLE d hjl ≫ homOfLE d hij = homOfLE d (hij.trans hjl) := by
  rw [towerMorphism_eq_iteratedBlowupMorphism d hjl (l - j) (by omega), towerMorphism_eq_iteratedBlowupMorphism d hij (j - i) (by omega),
    towerMorphism_eq_iteratedBlowupMorphism d (hij.trans hjl) ((j - i) + (l - j)) (by omega),
    iteratedBlowupMorphism_congr_start d (show j = i + (j - i) by omega) (l - j)]
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
  rw [iteratedBlowupMorphism_comp_iteratedBlowupMorphism d i (j - i) (l - j)]
  simp
def tower (d : BlowupSequenceData X) : ℕᵒᵖ ⥤ Scheme.{u} where
  obj n := d.obj n.unop
  map f := homOfLE d (leOfHom f.unop)
  map_id n := towerMorphism_refl d n.unop
  map_comp f g := (towerMorphism_comp d (leOfHom g.unop) (leOfHom f.unop)).symm
@[simp]
theorem tower_obj (d : BlowupSequenceData X) (i : ℕ) : d.tower.obj (op i) = d.obj i := rfl
theorem iteratedBlowupMorphism_one (d : BlowupSequenceData X) (i : ℕ) :
    homAdd d i 1 = d.map i := by
  show d.map (i + 0) ≫ homAdd d i 0 = d.map i
  exact Category.comp_id _
theorem eqToHom_comp_iteratedBlowupMorphism (d : BlowupSequenceData X) (i : ℕ) {k k' : ℕ} (h : k = k')
    (hobj : d.obj (i + k) = d.obj (i + k')) :
    eqToHom hobj ≫ homAdd d i k' = homAdd d i k := by
  subst h
  simp
theorem towerMorphism_succ (d : BlowupSequenceData X) (i : ℕ) (h : i ≤ i + 1) :
    homOfLE d h = d.map i := by
  have h1 : i + 1 - i = 1 := by omega
  have h2 := eqToHom_comp_iteratedBlowupMorphism d i h1
    (show d.obj (i + (i + 1 - i)) = d.obj (i + 1) by rw [h1])
  unfold homOfLE
  rw [← h2, ← Category.assoc, eqToHom_trans, eqToHom_refl, Category.id_comp]
  exact iteratedBlowupMorphism_one d i
@[simp]
theorem tower_map_succ (d : BlowupSequenceData X) (i : ℕ) :
    d.tower.map (CategoryTheory.homOfLE (Nat.le_succ i)).op = d.map i :=
  towerMorphism_succ d i (Nat.le_succ i)
theorem isBlowupAlongIdealSheaf_tower_map (d : BlowupSequenceData X) (i : ℕ) (hi : i < d.length) :
    Blowup.IsBlowupAlongIdealSheaf (d.tower.map (CategoryTheory.homOfLE (Nat.le_succ i)).op) (d.center i) := by
  have h := d.isBlowup i hi
  rw [tower_map_succ]
  exact h
def toSequenceOfBlowups (d : BlowupSequenceData X) : SequenceOfBlowups X where
  length := d.length
  tower := d.tower
  isoZero := d.isoZero
  center := d.center
  isBlowup := fun i hi => isBlowupAlongIdealSheaf_tower_map d i hi
@[simp]
theorem toSequenceOfBlowups_length (d : BlowupSequenceData X) : d.toSequenceOfBlowups.length = d.length := rfl
@[simp]
theorem toSequenceOfBlowups_tower (d : BlowupSequenceData X) : d.toSequenceOfBlowups.tower = d.tower := rfl
@[simp]
theorem toSequenceOfBlowups_center (d : BlowupSequenceData X) (i : ℕ) : d.toSequenceOfBlowups.center i = d.center i := rfl
@[simp]
theorem toSequenceOfBlowups_isoObjZero (d : BlowupSequenceData X) : d.toSequenceOfBlowups.isoZero = d.isoZero := rfl
@[simp]
theorem toSequenceOfBlowups_blowupMorphism (d : BlowupSequenceData X) (i : ℕ) : d.toSequenceOfBlowups.transitionMapSucc i = d.map i :=
  tower_map_succ d i
@[simp]
theorem toSequenceOfBlowups_projectionToBase (d : BlowupSequenceData X) (i : ℕ) : d.toSequenceOfBlowups.projectionToBase i = projectionToBase d i := by
  induction i with
  | zero =>
      have h0 : d.toSequenceOfBlowups.transitionMap (Nat.zero_le 0) = 𝟙 (d.toSequenceOfBlowups.schemeAt 0) :=
        d.toSequenceOfBlowups.tower.map_id (op 0)
      have h1 : d.toSequenceOfBlowups.projectionToBase 0 = d.toSequenceOfBlowups.transitionMap (Nat.zero_le 0) ≫ d.toSequenceOfBlowups.isoZero.hom :=
        SequenceOfBlowups.projectionToBase_def d.toSequenceOfBlowups 0
      have h2 : d.toSequenceOfBlowups.projectionToBase 0 = d.toSequenceOfBlowups.isoZero.hom := by
        rw [h1, h0, Category.id_comp]
      exact h2
  | succ j ih =>
      have h2 : d.toSequenceOfBlowups.transitionMap (Nat.le_succ j) = d.map j :=
        (SequenceOfBlowups.transitionMap_def d.toSequenceOfBlowups (Nat.le_succ j)).trans (tower_map_succ d j)
      have h3 : d.toSequenceOfBlowups.transitionMap (Nat.le_succ j) ≫ d.toSequenceOfBlowups.projectionToBase j
          = d.toSequenceOfBlowups.projectionToBase (j + 1) :=
        SequenceOfBlowups.transitionMap_comp_projectionToBase d.toSequenceOfBlowups (Nat.le_succ j)
      have h5 : d.toSequenceOfBlowups.transitionMap (Nat.le_succ j) ≫ d.toSequenceOfBlowups.projectionToBase j
          = d.map j ≫ projectionToBase d j := by
        rw [h2, ih]
        exact rfl
      exact h3.symm.trans h5
def ofSequenceOfBlowups (s : SequenceOfBlowups X) : BlowupSequenceData X where
  length := s.length
  obj := s.schemeAt
  map := s.transitionMapSucc
  isoZero := s.isoZero
  center := s.center
  isBlowup := fun i hi => s.isBlowupAlongIdealSheaf_blowupMorphism i hi
@[simp]
theorem ofSequenceOfBlowups_length (s : SequenceOfBlowups X) : (ofSequenceOfBlowups s).length = s.length := rfl
@[simp]
theorem ofSequenceOfBlowups_schemeAt (s : SequenceOfBlowups X) (i : ℕ) : (ofSequenceOfBlowups s).obj i = s.schemeAt i := rfl
@[simp]
theorem ofSequenceOfBlowups_blowupMorphism (s : SequenceOfBlowups X) (i : ℕ) : (ofSequenceOfBlowups s).map i = s.transitionMapSucc i := rfl
@[simp]
theorem ofSequenceOfBlowups_center (s : SequenceOfBlowups X) (i : ℕ) : (ofSequenceOfBlowups s).center i = s.center i := rfl
@[simp]
theorem ofSequenceOfBlowups_isoObjZero (s : SequenceOfBlowups X) : (ofSequenceOfBlowups s).isoZero = s.isoZero := rfl
end BlowupSequenceData
def emptyBlowupSequenceData (X : Scheme.{u}) : BlowupSequenceData X where
  length := 0
  obj := fun _ => X
  map := fun _ => 𝟙 X
  isoZero := Iso.refl X
  center := fun _ => ⊤
  isBlowup := fun i hi => absurd hi (Nat.not_lt_zero i)
@[simp]
theorem emptyBlowupSequenceData_length (X : Scheme.{u}) : (emptyBlowupSequenceData X).length = 0 := rfl
@[simp]
theorem emptyBlowupSequenceData_schemeAt (X : Scheme.{u}) (i : ℕ) : (emptyBlowupSequenceData X).obj i = X := rfl
@[simp]
theorem emptyBlowupSequenceData_blowupMorphism (X : Scheme.{u}) (i : ℕ) : (emptyBlowupSequenceData X).map i = 𝟙 X := rfl
@[simp]
theorem emptyBlowupSequenceData_center (X : Scheme.{u}) (i : ℕ) : (emptyBlowupSequenceData X).center i = ⊤ := rfl
@[simp]
theorem emptyBlowupSequenceData_isoObjZero (X : Scheme.{u}) :
    (emptyBlowupSequenceData X).isoZero = Iso.refl X := rfl
structure MarkedBlowupSequenceData {k : Type u} [Field k] {X : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of k)) (I : X.IdealSheafData) (m : ℕ)
    (E : List X.IdealSheafData) extends BlowupSequenceData X where
  proj : ∀ i : ℕ, toBlowupSequenceData.obj i ⟶ X
  proj_zero : proj 0 = toBlowupSequenceData.isoZero.hom
  proj_succ : ∀ i : ℕ, proj (i + 1) = toBlowupSequenceData.map i ≫ proj i
  ideal : ∀ i : ℕ, (toBlowupSequenceData.obj i).IdealSheafData
  boundary : ∀ i : ℕ, List (toBlowupSequenceData.obj i).IdealSheafData
  ideal_zero : ideal 0 = I.comap toBlowupSequenceData.isoZero.hom
  boundary_zero : boundary 0 = E.map (fun D => D.comap toBlowupSequenceData.isoZero.hom)
  center_order : ∀ i, i < toBlowupSequenceData.length →
    ((toBlowupSequenceData.center i).support : Set ↥(toBlowupSequenceData.obj i)) ⊆ orderAtLeastLocus (ideal i) m
  center_smooth : ∀ i, i < toBlowupSequenceData.length →
    AlgebraicGeometry.Smooth ((toBlowupSequenceData.center i).subschemeι ≫ proj i ≫ p)
  center_snc : ∀ i, i < toBlowupSequenceData.length →
    HasStrictNormalCrossingsWith (proj i ≫ p) (toBlowupSequenceData.center i) (boundary i)
  ideal_succ : ∀ i, i < toBlowupSequenceData.length →
    Blowup.exceptionalIdeal (toBlowupSequenceData.map i) (toBlowupSequenceData.center i) ^ m * ideal (i + 1) =
      (ideal i).comap (toBlowupSequenceData.map i)
  boundary_succ : ∀ i, i < toBlowupSequenceData.length →
    boundary (i + 1) =
      (boundary i).map (Blowup.strictTransform (toBlowupSequenceData.map i) (toBlowupSequenceData.center i)) ++
        [Blowup.exceptionalIdeal (toBlowupSequenceData.map i) (toBlowupSequenceData.center i)]
namespace MarkedBlowupSequenceData
variable {k : Type u} [Field k] {X : Scheme.{u}} {p : X ⟶ Spec (CommRingCat.of k)}
  {I : X.IdealSheafData} {m : ℕ} {E : List X.IdealSheafData}
theorem projectionToBase_eq (d : MarkedBlowupSequenceData p I m E) (i : ℕ) :
    d.proj i = BlowupSequenceData.projectionToBase d.toBlowupSequenceData i := by
  induction i with
  | zero =>
      rw [BlowupSequenceData.projectionToBase_zero]
      exact d.proj_zero
  | succ i ih =>
      rw [d.proj_succ i, BlowupSequenceData.projectionToBase_succ, ih]
theorem projectionToBase_eq_toSequenceOfBlowups (d : MarkedBlowupSequenceData p I m E) (i : ℕ) :
    d.proj i = d.toBlowupSequenceData.toSequenceOfBlowups.projectionToBase i :=
  (d.projectionToBase_eq i).trans (BlowupSequenceData.toSequenceOfBlowups_projectionToBase d.toBlowupSequenceData i).symm
theorem center_support_subset_orderAtLeastLocus (d : MarkedBlowupSequenceData p I m E) (i : ℕ)
    (hi : i < d.toBlowupSequenceData.length) :
    ((d.toBlowupSequenceData.center i).support : Set ↥(d.toBlowupSequenceData.obj i)) ⊆
      orderAtLeastLocus (d.ideal i) m :=
  d.center_order i hi
theorem smooth_center_comp_projection (d : MarkedBlowupSequenceData p I m E) (i : ℕ)
    (hi : i < d.toBlowupSequenceData.length) :
    AlgebraicGeometry.Smooth
      ((d.toBlowupSequenceData.center i).subschemeι ≫ d.toBlowupSequenceData.toSequenceOfBlowups.projectionToBase i ≫ p) := by
  have h := d.center_smooth i hi
  rw [projectionToBase_eq_toSequenceOfBlowups d i] at h
  exact h
theorem hasStrictNormalCrossingsWith_center_boundary (d : MarkedBlowupSequenceData p I m E) (i : ℕ)
    (hi : i < d.toBlowupSequenceData.length) :
    HasStrictNormalCrossingsWith (d.toBlowupSequenceData.toSequenceOfBlowups.projectionToBase i ≫ p) (d.toBlowupSequenceData.center i)
      (d.boundary i) := by
  have h := d.center_snc i hi
  rw [d.projectionToBase_eq_toSequenceOfBlowups i] at h
  exact h
theorem exceptionalIdeal_pow_mul_ideal_succ_eq_comap (d : MarkedBlowupSequenceData p I m E) (i : ℕ)
    (hi : i < d.toBlowupSequenceData.length) :
    Blowup.exceptionalIdeal (d.toBlowupSequenceData.toSequenceOfBlowups.transitionMapSucc i)
          (show (d.toBlowupSequenceData.toSequenceOfBlowups.schemeAt i).IdealSheafData from d.toBlowupSequenceData.center i) ^ m *
        (show (d.toBlowupSequenceData.toSequenceOfBlowups.schemeAt (i + 1)).IdealSheafData from d.ideal (i + 1)) =
      (show (d.toBlowupSequenceData.toSequenceOfBlowups.schemeAt i).IdealSheafData from d.ideal i).comap
        (d.toBlowupSequenceData.toSequenceOfBlowups.transitionMapSucc i) := by
  have key := d.ideal_succ i hi
  have h : d.toBlowupSequenceData.toSequenceOfBlowups.transitionMapSucc i = d.toBlowupSequenceData.map i :=
    BlowupSequenceData.toSequenceOfBlowups_blowupMorphism d.toBlowupSequenceData i
  rw [h]
  exact key
theorem boundary_succ_eq_map_strictTransform_append (d : MarkedBlowupSequenceData p I m E) (i : ℕ)
    (hi : i < d.toBlowupSequenceData.length) :
    d.boundary (i + 1) =
      (d.boundary i).map
          (Blowup.strictTransform (d.toBlowupSequenceData.toSequenceOfBlowups.transitionMapSucc i) (d.toBlowupSequenceData.center i)) ++
        [Blowup.exceptionalIdeal (d.toBlowupSequenceData.toSequenceOfBlowups.transitionMapSucc i) (d.toBlowupSequenceData.center i)] := by
  have key := d.boundary_succ i hi
  have h : d.toBlowupSequenceData.toSequenceOfBlowups.transitionMapSucc i = d.toBlowupSequenceData.map i :=
    BlowupSequenceData.toSequenceOfBlowups_blowupMorphism d.toBlowupSequenceData i
  rw [h]
  exact key
def toMarkedSequenceOfBlowups (d : MarkedBlowupSequenceData p I m E) : MarkedSequenceOfBlowups p I m E where
  toSequenceOfBlowups := d.toBlowupSequenceData.toSequenceOfBlowups
  ideal := d.ideal
  boundary := d.boundary
  ideal_zero := d.ideal_zero
  boundary_zero := d.boundary_zero
  center_smooth := fun i hi => smooth_center_comp_projection d i hi
  center_snc := fun i hi => hasStrictNormalCrossingsWith_center_boundary d i hi
  center_order := fun i hi => center_support_subset_orderAtLeastLocus d i hi
  ideal_succ := fun i hi => exceptionalIdeal_pow_mul_ideal_succ_eq_comap d i hi
  boundary_succ := fun i hi => boundary_succ_eq_map_strictTransform_append d i hi
@[simp]
theorem toMarkedSequence_toSequenceOfBlowups (d : MarkedBlowupSequenceData p I m E) :
    d.toMarkedSequenceOfBlowups.toSequenceOfBlowups = d.toBlowupSequenceData.toSequenceOfBlowups := rfl
@[simp]
theorem toMarkedSequence_length (d : MarkedBlowupSequenceData p I m E) :
    d.toMarkedSequenceOfBlowups.toSequenceOfBlowups.length = d.toBlowupSequenceData.length := rfl
@[simp]
theorem toMarkedSequence_ideal (d : MarkedBlowupSequenceData p I m E) (i : ℕ) :
    d.toMarkedSequenceOfBlowups.ideal i = d.ideal i := rfl
@[simp]
theorem toMarkedSequence_boundary (d : MarkedBlowupSequenceData p I m E) (i : ℕ) :
    d.toMarkedSequenceOfBlowups.boundary i = d.boundary i := rfl
@[simp]
theorem toMarkedSequence_center (d : MarkedBlowupSequenceData p I m E) (i : ℕ) :
    d.toMarkedSequenceOfBlowups.toSequenceOfBlowups.center i = d.toBlowupSequenceData.center i := rfl
theorem toMarkedSequence_projectionToBase (d : MarkedBlowupSequenceData p I m E) (i : ℕ) :
    d.toMarkedSequenceOfBlowups.toSequenceOfBlowups.projectionToBase i = d.proj i :=
  (BlowupSequenceData.toSequenceOfBlowups_projectionToBase d.toBlowupSequenceData i).trans (d.projectionToBase_eq i).symm
@[simp]
theorem toMarkedSequence_projectionToSpec (d : MarkedBlowupSequenceData p I m E) (i : ℕ) :
    d.toMarkedSequenceOfBlowups.projectionToSpec i = d.proj i ≫ p := by
  rw [MarkedSequenceOfBlowups.projectionToSpec_eq, toMarkedSequence_projectionToBase]
  rfl
@[simp]
theorem toMarkedSequence_lastIdeal (d : MarkedBlowupSequenceData p I m E) :
    d.toMarkedSequenceOfBlowups.lastIdeal = d.ideal d.toBlowupSequenceData.length := rfl
theorem toSequenceOfBlowups_projectionToBase_zero (s : MarkedSequenceOfBlowups p I m E) :
    s.toSequenceOfBlowups.projectionToBase 0 = (BlowupSequenceData.ofSequenceOfBlowups s.toSequenceOfBlowups).isoZero.hom := by
  have h1 : s.toSequenceOfBlowups.tower.map (homOfLE (le_refl (0 : ℕ))).op
      = 𝟙 (s.toSequenceOfBlowups.tower.obj (Opposite.op 0)) :=
    s.toSequenceOfBlowups.tower.map_id (Opposite.op 0)
  show s.toSequenceOfBlowups.projectionToBase 0 = s.toSequenceOfBlowups.isoZero.hom
  rw [SequenceOfBlowups.projectionToBase_def, SequenceOfBlowups.transitionMap_def, h1, Category.id_comp]
theorem toSequenceOfBlowups_projectionToBase_succ (s : MarkedSequenceOfBlowups p I m E) (i : ℕ) :
    s.toSequenceOfBlowups.projectionToBase (i + 1) =
      (BlowupSequenceData.ofSequenceOfBlowups s.toSequenceOfBlowups).map i ≫ s.toSequenceOfBlowups.projectionToBase i := by
  show s.toSequenceOfBlowups.projectionToBase (i + 1)
      = s.toSequenceOfBlowups.transitionMapSucc i ≫ s.toSequenceOfBlowups.projectionToBase i
  rw [SequenceOfBlowups.blowupMorphism_eq_transitionMap, SequenceOfBlowups.transitionMap_comp_projectionToBase]
def ofMarkedSequence (s : MarkedSequenceOfBlowups p I m E) : MarkedBlowupSequenceData p I m E where
  toBlowupSequenceData := BlowupSequenceData.ofSequenceOfBlowups s.toSequenceOfBlowups
  proj := fun i => s.toSequenceOfBlowups.projectionToBase i
  proj_zero := toSequenceOfBlowups_projectionToBase_zero s
  proj_succ := fun i => toSequenceOfBlowups_projectionToBase_succ s i
  ideal := s.ideal
  boundary := s.boundary
  ideal_zero := s.ideal_zero
  boundary_zero := s.boundary_zero
  center_order := fun i hi => s.center_order i hi
  center_smooth := fun i hi => s.center_smooth i hi
  center_snc := fun i hi => s.center_snc i hi
  ideal_succ := fun i hi => s.ideal_succ i hi
  boundary_succ := fun i hi => s.boundary_succ i hi
@[simp]
theorem blowupSequenceData_ofMarkedSequence (s : MarkedSequenceOfBlowups p I m E) :
    (ofMarkedSequence s).toBlowupSequenceData = BlowupSequenceData.ofSequenceOfBlowups s.toSequenceOfBlowups := rfl
@[simp]
theorem ofMarkedSequence_length (s : MarkedSequenceOfBlowups p I m E) :
    (ofMarkedSequence s).toBlowupSequenceData.length = s.toSequenceOfBlowups.length := rfl
@[simp]
theorem ofMarkedSequence_projectionToBase (s : MarkedSequenceOfBlowups p I m E) (i : ℕ) :
    (ofMarkedSequence s).proj i = s.toSequenceOfBlowups.projectionToBase i := rfl
@[simp]
theorem ofMarkedSequence_blowupMorphism (s : MarkedSequenceOfBlowups p I m E) (i : ℕ) :
    (ofMarkedSequence s).toBlowupSequenceData.map i = s.toSequenceOfBlowups.transitionMapSucc i := rfl
@[simp]
theorem ofMarkedSequence_ideal (s : MarkedSequenceOfBlowups p I m E) (i : ℕ) :
    (ofMarkedSequence s).ideal i = s.ideal i := rfl
@[simp]
theorem ofMarkedSequence_boundary_apply (s : MarkedSequenceOfBlowups p I m E) (i : ℕ) :
    (ofMarkedSequence s).boundary i = s.boundary i := rfl
@[simp]
theorem ofMarkedSequence_center (s : MarkedSequenceOfBlowups p I m E) (i : ℕ) :
    (ofMarkedSequence s).toBlowupSequenceData.center i = s.toSequenceOfBlowups.center i := rfl
end MarkedBlowupSequenceData
def emptyMarkedBlowupSequenceData {k : Type u} [Field k] {X : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of k)) (I : X.IdealSheafData) (m : ℕ)
    (E : List X.IdealSheafData) : MarkedBlowupSequenceData p I m E where
  toBlowupSequenceData := emptyBlowupSequenceData X
  proj := fun _ => 𝟙 X
  proj_zero := rfl
  proj_succ := fun _ => (Category.id_comp _).symm
  ideal := fun _ => I
  boundary := fun _ => E
  ideal_zero := (Scheme.IdealSheafData.comap_id I).symm
  boundary_zero := by simp [Scheme.IdealSheafData.comap_id]
  center_order := fun i hi => absurd hi (Nat.not_lt_zero i)
  center_smooth := fun i hi => absurd hi (Nat.not_lt_zero i)
  center_snc := fun i hi => absurd hi (Nat.not_lt_zero i)
  ideal_succ := fun i hi => absurd hi (Nat.not_lt_zero i)
  boundary_succ := fun i hi => absurd hi (Nat.not_lt_zero i)
end FunctorialResolution.EmbeddedResolution


