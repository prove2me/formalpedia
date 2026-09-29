-- Prove2me | solution 1 for AlgebraicGeometry.ProjSpace.exists_linearEquiv_baseChange_cochain_twist_of_isPullback
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/4f3337a6-f9fd-51fe-87ad-b6f00290b6a7

import Mathlib
import Definitions.Def_AlgebraicGeometry_ProjSpace
import Definitions.Def_AlgebraicGeometry_ProjSpaceCover
import Definitions.Def_AlgebraicGeometry_ProjTwistDatum
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverComap
import Theorems.Thm_AlgebraicGeometry_ProjSpace_exists_linearEquiv_twistObj_of_le_pullbackChart
import Theorems.Thm_AlgebraicGeometry_Scheme_isAffineOpen_and_exists_linearEquiv_tensor_sections_of_isPullback
import Theorems.Thm_AlgebraicGeometry_ProjSpace_map_preimage_basicOpen_X
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_ProjSpace_exists_linearEquiv_baseChange_cochain_twist_of_isPullback

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MvPolynomial TensorProduct

attribute [local instance] MvPolynomial.gradedAlgebra

open HomogeneousLocalization

namespace P2mWs6C3

section Setup

variable {A : Type u} [CommRing A] {n : ℕ} {Z : Scheme.{u}}
  (ι : Z ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A)) [IsAffineHom ι]
  (B : Type u) [CommRing B] [Algebra A B] {Z' : Scheme.{u}}
  (ι' : Z' ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) B)) [IsAffineHom ι']
  (e : Z' ⟶ Z)

local notation "𝒜A" => MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A
local notation "𝒜B" => MvPolynomial.homogeneousSubmodule (Fin (n + 1)) B

theorem preimage_pullbackChart (hcomp : e ≫ ι = ι' ≫ ProjSpace.map A B n) (j : Fin (n + 1)) :
    e ⁻¹ᵁ ProjSpace.pullbackChart ι j = ProjSpace.pullbackChart ι' j := by
  rw [ProjSpace.pullbackChart_eq, ProjSpace.pullbackChart_eq, ← Scheme.Hom.comp_preimage, hcomp,
    Scheme.Hom.comp_preimage, ProjSpace.map_preimage_basicOpen_X]

theorem preimage_inter (hcomp : e ≫ ι = ι' ≫ ProjSpace.map A B n) {i : ℕ} (s : (ProjSpace.stdCoverPullback ι).Idx i) :
    e ⁻¹ᵁ (ProjSpace.stdCoverPullback ι).inter s = (ProjSpace.stdCoverPullback ι').inter s := by
  show e ⁻¹ᵁ (⨅ j, (ProjSpace.stdCoverPullback ι).U (s.1 j)) = ⨅ j, (ProjSpace.stdCoverPullback ι').U (s.1 j)
  rw [Scheme.OrderedAffineCover.preimage_iInf_fin]
  congr 1
  funext j
  rw [ProjSpace.stdCoverPullback_U, ProjSpace.stdCoverPullback_U, ProjSpace.stdCover_U, ProjSpace.stdCover_U,
    ← Scheme.Hom.comp_preimage, hcomp, Scheme.Hom.comp_preimage, ProjSpace.map_preimage_basicOpen_X]

theorem inter_le_pullbackChart {W : Scheme.{u}} {R : Type u} [CommRing R]
    (φ : W ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)) [IsAffineHom φ]
    {i : ℕ} (s : (ProjSpace.stdCoverPullback φ).Idx i) (t : Fin (i + 1)) :
    (ProjSpace.stdCoverPullback φ).inter s ≤ ProjSpace.pullbackChart φ ((s.1 t).down) := by
  refine (Scheme.OrderedAffineCover.inter_le _ s t).trans ?_
  rw [ProjSpace.stdCoverPullback_U, ProjSpace.stdCover_U, ProjSpace.pullbackChart_eq]

theorem isAffineOpen_inter {W : Scheme.{u}} {R : Type u} [CommRing R]
    (φ : W ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)) [IsAffineHom φ]
    {i : ℕ} (s : (ProjSpace.stdCoverPullback φ).Idx i) :
    IsAffineOpen ((ProjSpace.stdCoverPullback φ).inter s) := by

  have : (ProjSpace.stdCoverPullback φ).inter s = φ ⁻¹ᵁ (⨅ j, (ProjSpace.stdCover R n).U (s.1 j)) := by
    show (⨅ j, (ProjSpace.stdCoverPullback φ).U (s.1 j)) = _
    rw [Scheme.OrderedAffineCover.preimage_iInf_fin]
    rfl
  rw [this]
  refine IsAffineOpen.preimage ?_ φ

  have key : ∀ (m : ℕ) (g : Fin (m + 1) → MvPolynomial (Fin (n + 1)) R),
      (⨅ j, Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) (g j))
        = Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) (∏ j, g j) := by
    intro m
    induction m with
    | zero =>
      intro g
      rw [Fin.prod_univ_one]
      exact le_antisymm (iInf_le _ 0) (le_iInf fun j => by fin_cases j; exact le_rfl)
    | succ m ih =>
      intro g
      rw [Fin.prod_univ_succ, Proj.basicOpen_mul, ← ih (fun j => g j.succ)]
      exact le_antisymm (le_inf (iInf_le _ 0) (le_iInf fun j => iInf_le _ j.succ))
        (le_iInf fun j => Fin.cases inf_le_left (fun k => inf_le_right.trans (iInf_le _ k)) j)
  have hdeg : ∀ (m : ℕ) (t : Fin (m + 1) → Fin (n + 1)),
      (∏ j, MvPolynomial.X (t j) : MvPolynomial (Fin (n + 1)) R) ∈ MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R (m + 1) := by
    intro m t
    have := SetLike.prod_mem_graded (A := MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)
      (F := (Finset.univ : Finset (Fin (m + 1)))) (i := fun _ => (1 : ℕ)) (g := fun j => MvPolynomial.X (t j))
      (fun j _ => ProjSpace.X_mem_one R n (t j))
    simpa using this
  simp only [ProjSpace.stdCover_U]
  rw [key]
  exact Proj.isAffineOpen_basicOpen _ _ (hdeg i (fun j => (s.1 j).down)) (Nat.succ_pos _)

theorem X_eq_mvMapGraded_mul_one (i : Fin (n + 1)) :
    (MvPolynomial.X i : MvPolynomial (Fin (n + 1)) B) = (ProjSpace.mvMapGraded A B n) (MvPolynomial.X i) * 1 := by
  rw [ProjSpace.mvMapGraded_X, mul_one]

theorem one_mem_zero : (1 : MvPolynomial (Fin (n + 1)) B) ∈ (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) B) 0 :=
  SetLike.one_mem_graded _

noncomputable def toB (i : Fin (n + 1)) : Away 𝒜A (MvPolynomial.X i) →+* Away 𝒜B (MvPolynomial.X i) :=
  (awayMap 𝒜B (one_mem_zero (n := n) B) (X_eq_mvMapGraded_mul_one (A := A) B i)).comp
    (Away.map (ProjSpace.mvMapGraded A B n) (MvPolynomial.X i))

theorem toB_ratio (i j : Fin (n + 1)) : toB (A := A) B i (ProjSpace.ratio A n i j) = ProjSpace.ratio B n i j := by
  apply HomogeneousLocalization.val_injective
  rw [toB, RingHom.comp_apply, ProjSpace.ratio, Away.map_mk]
  rw [Away.mk, val_awayMap_mk, ProjSpace.ratio, Away.val_mk, Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  exact ⟨1, by simp [ProjSpace.mvMapGraded_X]⟩

theorem restrictFun_app_pullAway (hcomp : e ≫ ι = ι' ≫ ProjSpace.map A B n) (i : Fin (n + 1))
    (a : Away 𝒜A (MvPolynomial.X i)) {W' : Z'.Opens}
    (h₁ : W' ≤ e ⁻¹ᵁ ProjSpace.pullbackChart ι i) (h₂ : W' ≤ ProjSpace.pullbackChart ι' i) :
    ProjSpace.restrictFun h₁ ((e.app (ProjSpace.pullbackChart ι i)).hom
        ((ι.app (Proj.basicOpen 𝒜A (MvPolynomial.X i))).hom ((Proj.awayToSection 𝒜A (MvPolynomial.X i)).hom a)))
      = ProjSpace.restrictFun h₂ ((ι'.app (Proj.basicOpen 𝒜B (MvPolynomial.X i))).hom
          ((Proj.awayToSection 𝒜B (MvPolynomial.X i)).hom (toB (A := A) B i a))) := by

  have s1 : (e.app (ProjSpace.pullbackChart ι i)).hom
      ((ι.app (Proj.basicOpen 𝒜A (MvPolynomial.X i))).hom ((Proj.awayToSection 𝒜A (MvPolynomial.X i)).hom a))
      = ((e ≫ ι).app (Proj.basicOpen 𝒜A (MvPolynomial.X i))).hom ((Proj.awayToSection 𝒜A (MvPolynomial.X i)).hom a) := by
    rfl
  rw [s1]
  have s2 := Scheme.Hom.congr_app hcomp (Proj.basicOpen 𝒜A (MvPolynomial.X i))
  rw [s2]
  change ProjSpace.restrictFun h₁ ((Z'.presheaf.map _).hom
      ((ι'.app ((ProjSpace.map A B n) ⁻¹ᵁ Proj.basicOpen 𝒜A (MvPolynomial.X i))).hom
        (((ProjSpace.map A B n).app (Proj.basicOpen 𝒜A (MvPolynomial.X i))).hom
          ((Proj.awayToSection 𝒜A (MvPolynomial.X i)).hom a)))) = _

  have s3 : ((ProjSpace.map A B n).app (Proj.basicOpen 𝒜A (MvPolynomial.X i))).hom
      ((Proj.awayToSection 𝒜A (MvPolynomial.X i)).hom a)
      = (Proj.awayToSection 𝒜B ((ProjSpace.mvMapGraded A B n) (MvPolynomial.X i))).hom
          (Away.map (ProjSpace.mvMapGraded A B n) (MvPolynomial.X i) a) := by
    have := Proj.awayToSection_comp_appLE (ProjSpace.mvMapGraded A B n) (ProjSpace.irrelevant_le_map_mvMapGraded A B n)
      (ProjSpace.X_mem_one A n i)
    have h := congrArg (fun ψ => ψ.hom a) this
    simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at h
    have h' : ((ProjSpace.map A B n).appLE (Proj.basicOpen 𝒜A (MvPolynomial.X i))
        ((ProjSpace.map A B n) ⁻¹ᵁ Proj.basicOpen 𝒜A (MvPolynomial.X i)) le_rfl).hom
        ((Proj.awayToSection 𝒜A (MvPolynomial.X i)).hom a)
        = (Proj.awayToSection 𝒜B ((ProjSpace.mvMapGraded A B n) (MvPolynomial.X i))).hom
          (Away.map (ProjSpace.mvMapGraded A B n) (MvPolynomial.X i) a) := h
    rw [Scheme.Hom.appLE_eq_app] at h'
    exact h'
  rw [s3]

  have s4 := congrArg (fun ψ => ψ.hom (Away.map (ProjSpace.mvMapGraded A B n) (MvPolynomial.X i) a))
    (Proj.awayMap_awayToSection 𝒜B (one_mem_zero (n := n) B) (X_eq_mvMapGraded_mul_one (A := A) B i))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at s4

  have s5 : (Proj.awayToSection 𝒜B (MvPolynomial.X i)).hom (toB (A := A) B i a)
      = ((Proj 𝒜B).presheaf.map (homOfLE (Proj.basicOpen_mono 𝒜B _ _
          ⟨_, X_eq_mvMapGraded_mul_one (A := A) B i⟩)).op).hom
        ((Proj.awayToSection 𝒜B ((ProjSpace.mvMapGraded A B n) (MvPolynomial.X i))).hom
          (Away.map (ProjSpace.mvMapGraded A B n) (MvPolynomial.X i) a)) := by
    rw [toB, RingHom.comp_apply]
    exact s4
  rw [s5]

  have s6 := congrArg (fun ψ => ψ.hom ((Proj.awayToSection 𝒜B ((ProjSpace.mvMapGraded A B n) (MvPolynomial.X i))).hom
          (Away.map (ProjSpace.mvMapGraded A B n) (MvPolynomial.X i) a)))
    (ι'.naturality (homOfLE (Proj.basicOpen_mono 𝒜B _ _ ⟨_, X_eq_mvMapGraded_mul_one (A := A) B i⟩)).op)
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at s6
  rw [s6]

  show (Z'.presheaf.map _ ≫ Z'.presheaf.map _).hom _ = (Z'.presheaf.map _ ≫ Z'.presheaf.map _).hom _
  rw [← Functor.map_comp, ← Functor.map_comp]
  rfl

theorem restrictFun_app_frameUnit (hcomp : e ≫ ι = ι' ≫ ProjSpace.map A B n) (i j : Fin (n + 1)) {W' : Z'.Opens}
    (h₁ : W' ≤ e ⁻¹ᵁ ProjSpace.pullbackChart ι i) (h₂ : W' ≤ ProjSpace.pullbackChart ι' i) :
    ProjSpace.restrictFun h₁ ((e.app (ProjSpace.pullbackChart ι i)).hom (ProjSpace.frameUnit ι i j))
      = ProjSpace.restrictFun h₂ (ProjSpace.frameUnit ι' i j) := by
  rw [ProjSpace.frameUnit, ProjSpace.frameUnit, restrictFun_app_pullAway ι B ι' e hcomp i _ h₁ h₂, toB_ratio]

theorem restrictFun_app_eq {U V : Z.Opens} (hVU : V ≤ U) {W' : Z'.Opens} (h₁ : W' ≤ e ⁻¹ᵁ V) (h₂ : W' ≤ e ⁻¹ᵁ U)
    (x : Γ(Z, U)) :
    ProjSpace.restrictFun h₁ ((e.app V).hom (ProjSpace.restrictFun hVU x)) = ProjSpace.restrictFun h₂ ((e.app U).hom x) := by
  have := congrArg (fun ψ => ψ.hom x) (e.naturality (homOfLE hVU).op)
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at this
  erw [this]
  show (Z'.presheaf.map _ ≫ Z'.presheaf.map _).hom _ = (Z'.presheaf.map _).hom _
  rw [← Functor.map_comp]
  rfl

theorem appLE_top_top {X Y : Scheme.{u}} (g : X ⟶ Y) (h : (⊤ : X.Opens) ≤ g ⁻¹ᵁ ⊤) : g.appLE ⊤ ⊤ h = g.appTop := by
  rw [Scheme.Hom.appLE]
  have : (homOfLE h).op = 𝟙 _ := Subsingleton.elim _ _
  rw [this]
  erw [CategoryTheory.Functor.map_id, Category.comp_id]

theorem appLE_hom_apply {X Y : Scheme.{u}} (g : X ⟶ Y) (U : Y.Opens) (V : X.Opens) (h : V ≤ g ⁻¹ᵁ U) (x : Γ(Y, U)) :
    (g.appLE U V h).hom x = ProjSpace.restrictFun h ((g.app U).hom x) := rfl

end Setup

noncomputable def valAddHom {R : Type u} [CommRing R] {n : ℕ} {X : Scheme.{u}} (π : X ⟶ Spec (.of R))
    (φ : X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)) (m : ℕ) (U : X.Opens) :
    ProjSpace.twistObj π φ m U →+ (∀ j : Fin (n + 1), Γ(X, U ⊓ ProjSpace.pullbackChart φ j)) :=
  { toFun := ProjSpace.twistObj.val, map_zero' := ProjSpace.twistObj.zero_val, map_add' := ProjSpace.twistObj.add_val }

theorem val_sum {R : Type u} [CommRing R] {n : ℕ} {X : Scheme.{u}} (π : X ⟶ Spec (.of R))
    (φ : X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)) (m : ℕ) (U : X.Opens)
    {κ : Type*} (t : Finset κ) (f : κ → ProjSpace.twistObj π φ m U) :
    (∑ x ∈ t, f x).val = ∑ x ∈ t, (f x).val :=
  map_sum (valAddHom π φ m U) f t

theorem val_zsmul {R : Type u} [CommRing R] {n : ℕ} {X : Scheme.{u}} (π : X ⟶ Spec (.of R))
    (φ : X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)) (m : ℕ) (U : X.Opens)
    (z : ℤ) (g : ProjSpace.twistObj π φ m U) : (z • g).val = z • g.val :=
  map_zsmul (valAddHom π φ m U) z g

theorem val_sum' {R : Type u} [CommRing R] {n : ℕ} {X : Scheme.{u}} (π : X ⟶ Spec (.of R))
    (φ : X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)) [IsAffineHom φ] (m : ℕ) (U : X.Opens)
    {κ : Type*} (t : Finset κ) (f : κ → (ProjSpace.twist π φ m).obj U) :
    ((∑ x ∈ t, f x : (ProjSpace.twist π φ m).obj U) : ProjSpace.twistObj π φ m U).val
      = ∑ x ∈ t, (f x : ProjSpace.twistObj π φ m U).val :=
  map_sum (valAddHom π φ m U) f t

theorem val_zsmul' {R : Type u} [CommRing R] {n : ℕ} {X : Scheme.{u}} (π : X ⟶ Spec (.of R))
    (φ : X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)) [IsAffineHom φ] (m : ℕ) (U : X.Opens)
    (z : ℤ) (g : (ProjSpace.twist π φ m).obj U) :
    ((z • g : (ProjSpace.twist π φ m).obj U) : ProjSpace.twistObj π φ m U).val = z • (g : ProjSpace.twistObj π φ m U).val :=
  map_zsmul (valAddHom π φ m U) z g

end P2mWs6C3

set_option maxHeartbeats 3200000 in
open P2mWs6C3 in
theorem solution
    {A : Type u} [CommRing A] {n : ℕ} {Z : Scheme.{u}}
    (ι : Z ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A)) [IsAffineHom ι]
    (B : Type u) [CommRing B] [Algebra A B] {Z' : Scheme.{u}}
    (ι' : Z' ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) B)) [IsAffineHom ι']
    (e : Z' ⟶ Z)
    (hpb : IsPullback e (ι' ≫ ProjSpace.π B n) (ι ≫ ProjSpace.π A n) (Spec.map (CommRingCat.ofHom (algebraMap A B))))
    (hcomp : e ≫ ι = ι' ≫ ProjSpace.map A B n) (d : ℕ) :
    ∃ ε : ∀ i : ℕ,
        B ⊗[A] (ProjSpace.twist (ι ≫ ProjSpace.π A n) ι d).cochain (ProjSpace.stdCoverPullback ι) i ≃ₗ[B]
          (ProjSpace.twist (ι' ≫ ProjSpace.π B n) ι' d).cochain (ProjSpace.stdCoverPullback ι') i,
      (∀ i : ℕ,
        (ε (i + 1)).toLinearMap ∘ₗ ((ProjSpace.twist (ι ≫ ProjSpace.π A n) ι d).d (ProjSpace.stdCoverPullback ι) i).baseChange B =
          (ProjSpace.twist (ι' ≫ ProjSpace.π B n) ι' d).d (ProjSpace.stdCoverPullback ι') i ∘ₗ (ε i).toLinearMap) ∧
      (∀ (i : ℕ) (c : (ProjSpace.twist (ι ≫ ProjSpace.π A n) ι d).cochain (ProjSpace.stdCoverPullback ι) i)
        (s : (ProjSpace.stdCoverPullback ι).Idx i) (j : Fin (n + 1))
        (h : (ProjSpace.stdCoverPullback ι').inter s ⊓ ProjSpace.pullbackChart ι' j ≤
          e ⁻¹ᵁ ((ProjSpace.stdCoverPullback ι).inter s ⊓ ProjSpace.pullbackChart ι j)),
        (ε i ((1 : B) ⊗ₜ[A] c) s).val j =
          ProjSpace.restrictFun h ((e.app ((ProjSpace.stdCoverPullback ι).inter s ⊓ ProjSpace.pullbackChart ι j)) ((c s).val j))) := by
  classical

  have hU : ∀ (i : ℕ) (s : (ProjSpace.stdCoverPullback ι).Idx i), (ProjSpace.stdCoverPullback ι).inter s ≤ ProjSpace.pullbackChart ι (s.1 0).down :=
    fun i s => inter_le_pullbackChart ι s 0
  have hU' : ∀ (i : ℕ) (s : (ProjSpace.stdCoverPullback ι).Idx i), (ProjSpace.stdCoverPullback ι').inter s ≤ ProjSpace.pullbackChart ι' (s.1 0).down :=
    fun i s => inter_le_pullbackChart ι' s 0
  have hpre : ∀ (i : ℕ) (s : (ProjSpace.stdCoverPullback ι).Idx i), e ⁻¹ᵁ (ProjSpace.stdCoverPullback ι).inter s = (ProjSpace.stdCoverPullback ι').inter s :=
    fun i s => preimage_inter ι B ι' e hcomp s

  have tU : ∀ (i : ℕ) (s : (ProjSpace.stdCoverPullback ι).Idx i), ∃ f : ProjSpace.twistObj (ι ≫ ProjSpace.π A n) ι d ((ProjSpace.stdCoverPullback ι).inter s) ≃ₗ[Γ(Z, (ProjSpace.stdCoverPullback ι).inter s)] Γ(Z, (ProjSpace.stdCoverPullback ι).inter s),
      (∀ g, ProjSpace.restrictFun (inf_le_left : (ProjSpace.stdCoverPullback ι).inter s ⊓ ProjSpace.pullbackChart ι (s.1 0).down ≤ (ProjSpace.stdCoverPullback ι).inter s) (f g)
          = g.val (s.1 0).down) ∧
      (∀ (a : Γ(Z, (ProjSpace.stdCoverPullback ι).inter s)) (j : Fin (n + 1)), (f.symm a).val j =
          ProjSpace.restrictFun (inf_le_right : (ProjSpace.stdCoverPullback ι).inter s ⊓ ProjSpace.pullbackChart ι j ≤ ProjSpace.pullbackChart ι j)
              (ProjSpace.frameUnit ι j (s.1 0).down) ^ d *
            ProjSpace.restrictFun (inf_le_left : (ProjSpace.stdCoverPullback ι).inter s ⊓ ProjSpace.pullbackChart ι j ≤ (ProjSpace.stdCoverPullback ι).inter s) a) :=
    fun i s => AlgebraicGeometry.ProjSpace.exists_linearEquiv_twistObj_of_le_pullbackChart (ι ≫ ProjSpace.π A n) ι d (hU i s)
  have tU' : ∀ (i : ℕ) (s : (ProjSpace.stdCoverPullback ι).Idx i), ∃ f : ProjSpace.twistObj (ι' ≫ ProjSpace.π B n) ι' d ((ProjSpace.stdCoverPullback ι').inter s) ≃ₗ[Γ(Z', (ProjSpace.stdCoverPullback ι').inter s)] Γ(Z', (ProjSpace.stdCoverPullback ι').inter s),
      (∀ g, ProjSpace.restrictFun (inf_le_left : (ProjSpace.stdCoverPullback ι').inter s ⊓ ProjSpace.pullbackChart ι' (s.1 0).down ≤ (ProjSpace.stdCoverPullback ι').inter s) (f g)
          = g.val (s.1 0).down) ∧
      (∀ (a : Γ(Z', (ProjSpace.stdCoverPullback ι').inter s)) (j : Fin (n + 1)), (f.symm a).val j =
          ProjSpace.restrictFun (inf_le_right : (ProjSpace.stdCoverPullback ι').inter s ⊓ ProjSpace.pullbackChart ι' j ≤ ProjSpace.pullbackChart ι' j)
              (ProjSpace.frameUnit ι' j (s.1 0).down) ^ d *
            ProjSpace.restrictFun (inf_le_left : (ProjSpace.stdCoverPullback ι').inter s ⊓ ProjSpace.pullbackChart ι' j ≤ (ProjSpace.stdCoverPullback ι').inter s) a) :=
    fun i s => AlgebraicGeometry.ProjSpace.exists_linearEquiv_twistObj_of_le_pullbackChart (ι' ≫ ProjSpace.π B n) ι' d (hU' i s)
  choose fU hfU1 hfU2 using tU
  choose fU' hfU'1 hfU'2 using tU'

  letI instZ : ∀ U : Z.Opens, Algebra A Γ(Z, U) := fun U => Scheme.TwoAffineOpenCover.algebraOfHom (ι ≫ ProjSpace.π A n) U
  letI instS : ∀ V : (Spec (CommRingCat.of B)).Opens, Algebra A Γ(Spec (CommRingCat.of B), V) :=
    fun V => Scheme.TwoAffineOpenCover.algebraOfHom (Spec.map (CommRingCat.ofHom (algebraMap A B))) V
  letI instZ'A : ∀ W : Z'.Opens, Algebra A Γ(Z', W) := fun W => Scheme.TwoAffineOpenCover.algebraOfHom (e ≫ (ι ≫ ProjSpace.π A n)) W
  have hΦ : ∀ (i : ℕ) (s : (ProjSpace.stdCoverPullback ι).Idx i), ∃ Φ : Γ(Z, (ProjSpace.stdCoverPullback ι).inter s) ⊗[A] Γ(Spec (CommRingCat.of B), (⊤ : (Spec (CommRingCat.of B)).Opens))
        ≃ₗ[A] Γ(Z', e ⁻¹ᵁ (ProjSpace.stdCoverPullback ι).inter s ⊓ (ι' ≫ ProjSpace.π B n) ⁻¹ᵁ ⊤),
      ∀ (a : Γ(Z, (ProjSpace.stdCoverPullback ι).inter s)) (b : Γ(Spec (CommRingCat.of B), (⊤ : (Spec (CommRingCat.of B)).Opens))), Φ (a ⊗ₜ[A] b) =
        (e.appLE ((ProjSpace.stdCoverPullback ι).inter s) (e ⁻¹ᵁ (ProjSpace.stdCoverPullback ι).inter s ⊓ (ι' ≫ ProjSpace.π B n) ⁻¹ᵁ ⊤) inf_le_left).hom a *
          ((ι' ≫ ProjSpace.π B n).appLE ⊤ (e ⁻¹ᵁ (ProjSpace.stdCoverPullback ι).inter s ⊓ (ι' ≫ ProjSpace.π B n) ⁻¹ᵁ ⊤) inf_le_right).hom b :=
    fun i s => (AlgebraicGeometry.Scheme.isAffineOpen_and_exists_linearEquiv_tensor_sections_of_isPullback
      (ι ≫ ProjSpace.π A n) (Spec.map (CommRingCat.ofHom (algebraMap A B))) e (ι' ≫ ProjSpace.π B n) hpb ((ProjSpace.stdCoverPullback ι).inter s) (isAffineOpen_inter ι s) ⊤
      (isAffineOpen_top (Spec (CommRingCat.of B)))).2
  choose Φ hΦ using hΦ

  have hβalg : ∀ a : A, (Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom (algebraMap A B a)
      = (instS ⊤).algebraMap a := by
    intro a
    rw [Scheme.TwoAffineOpenCover.algebraMap_algebraOfHom, appLE_top_top]
    have nat := Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap A B))
    have := congrArg (fun ψ => ψ.hom a) nat
    simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at this
    exact this
  let β : B ≃ₗ[A] Γ(Spec (CommRingCat.of B), (⊤ : (Spec (CommRingCat.of B)).Opens)) :=
    AddEquiv.toLinearEquiv (Scheme.ΓSpecIso (CommRingCat.of B)).commRingCatIsoToRingEquiv.symm.toAddEquiv (by
      intro a b
      show (Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom (a • b) = a • (Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom b
      rw [Algebra.smul_def, map_mul, hβalg, Algebra.smul_def])
  have hβ : ∀ b : B, β b = (Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom b := fun _ => rfl

  have h1 : ∀ (i : ℕ) (s : (ProjSpace.stdCoverPullback ι).Idx i), (ProjSpace.stdCoverPullback ι').inter s ≤ e ⁻¹ᵁ (ProjSpace.stdCoverPullback ι).inter s ⊓ (ι' ≫ ProjSpace.π B n) ⁻¹ᵁ ⊤ :=
    fun i s => le_inf (hpre i s).ge le_top
  have h2 : ∀ (i : ℕ) (s : (ProjSpace.stdCoverPullback ι).Idx i), e ⁻¹ᵁ (ProjSpace.stdCoverPullback ι).inter s ⊓ (ι' ≫ ProjSpace.π B n) ⁻¹ᵁ ⊤ ≤ (ProjSpace.stdCoverPullback ι').inter s :=
    fun i s => inf_le_left.trans (hpre i s).le
  let ρ : ∀ (i : ℕ) (s : (ProjSpace.stdCoverPullback ι).Idx i), Γ(Z', e ⁻¹ᵁ (ProjSpace.stdCoverPullback ι).inter s ⊓ (ι' ≫ ProjSpace.π B n) ⁻¹ᵁ ⊤) ≃+ Γ(Z', (ProjSpace.stdCoverPullback ι').inter s) := fun i s =>
    { toFun := ProjSpace.restrictFun (h1 i s)
      invFun := ProjSpace.restrictFun (h2 i s)
      left_inv := fun x => by
        show ProjSpace.restrictFun (h2 i s) (ProjSpace.restrictFun (h1 i s) x) = x
        rw [ProjSpace.restrictFun_restrictFun]; exact ProjSpace.restrictFun_refl x
      right_inv := fun x => by
        show ProjSpace.restrictFun (h1 i s) (ProjSpace.restrictFun (h2 i s) x) = x
        rw [ProjSpace.restrictFun_restrictFun]; exact ProjSpace.restrictFun_refl x
      map_add' := fun x y => map_add _ x y }
  have hρ : ∀ (i : ℕ) (s : (ProjSpace.stdCoverPullback ι).Idx i) x, ρ i s x = ProjSpace.restrictFun (h1 i s) x := fun _ _ _ => rfl

  haveI hst : ∀ (i : ℕ) (s : (ProjSpace.stdCoverPullback ι).Idx i), IsScalarTower A Γ(Z, (ProjSpace.stdCoverPullback ι).inter s) (ProjSpace.twistObj (ι ≫ ProjSpace.π A n) ι d ((ProjSpace.stdCoverPullback ι).inter s)) :=
    fun i s => (ProjSpace.twist (ι ≫ ProjSpace.π A n) ι d).isScalarTower _
  let fUA : ∀ (i : ℕ) (s : (ProjSpace.stdCoverPullback ι).Idx i), ProjSpace.twistObj (ι ≫ ProjSpace.π A n) ι d ((ProjSpace.stdCoverPullback ι).inter s) ≃ₗ[A] Γ(Z, (ProjSpace.stdCoverPullback ι).inter s) :=
    fun i s => (fU i s).restrictScalars A
  have hfUA : ∀ (i : ℕ) (s : (ProjSpace.stdCoverPullback ι).Idx i) g, fUA i s g = fU i s g := fun _ _ _ => rfl

  let εs : ∀ (i : ℕ) (s : (ProjSpace.stdCoverPullback ι).Idx i), B ⊗[A] ProjSpace.twistObj (ι ≫ ProjSpace.π A n) ι d ((ProjSpace.stdCoverPullback ι).inter s) ≃+ ProjSpace.twistObj (ι' ≫ ProjSpace.π B n) ι' d ((ProjSpace.stdCoverPullback ι').inter s) := fun i s =>
    ((((((fUA i s).baseChange A B _ _).toAddEquiv.trans (TensorProduct.comm A B Γ(Z, (ProjSpace.stdCoverPullback ι).inter s)).toAddEquiv).trans
      (TensorProduct.congr (LinearEquiv.refl A Γ(Z, (ProjSpace.stdCoverPullback ι).inter s)) β).toAddEquiv).trans (Φ i s).toAddEquiv).trans
      (ρ i s)).trans (fU' i s).symm.toAddEquiv

  have keyform : ∀ (i : ℕ) (s : (ProjSpace.stdCoverPullback ι).Idx i) (c : B) (g : ProjSpace.twistObj (ι ≫ ProjSpace.π A n) ι d ((ProjSpace.stdCoverPullback ι).inter s)),
      εs i s (c ⊗ₜ[A] g) = c • (fU' i s).symm (ProjSpace.restrictFun ((h1 i s).trans inf_le_left)
        ((e.app ((ProjSpace.stdCoverPullback ι).inter s)).hom (fU i s g))) := by
    intro i s c g
    show (fU' i s).symm (ρ i s (Φ i s ((TensorProduct.congr (LinearEquiv.refl A Γ(Z, (ProjSpace.stdCoverPullback ι).inter s)) β)
      ((TensorProduct.comm A B Γ(Z, (ProjSpace.stdCoverPullback ι).inter s)) (((fUA i s).baseChange A B _ _) (c ⊗ₜ[A] g)))))) = _
    rw [LinearEquiv.baseChange_tmul, hfUA, TensorProduct.comm_tmul, TensorProduct.congr_tmul, LinearEquiv.refl_apply, hβ,
      hΦ, hρ, map_mul]
    have hc : ((ι' ≫ ProjSpace.π B n).appLE ⊤ (e ⁻¹ᵁ (ProjSpace.stdCoverPullback ι).inter s ⊓ (ι' ≫ ProjSpace.π B n) ⁻¹ᵁ ⊤) inf_le_right).hom
        ((Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom c)
        = (Scheme.TwoAffineOpenCover.algebraOfHom (ι' ≫ ProjSpace.π B n) (e ⁻¹ᵁ (ProjSpace.stdCoverPullback ι).inter s ⊓ (ι' ≫ ProjSpace.π B n) ⁻¹ᵁ ⊤)).algebraMap c := rfl
    rw [hc, ProjSpace.restrictFun_algebraMap' (ι' ≫ ProjSpace.π B n), appLE_hom_apply, ProjSpace.restrictFun_restrictFun, mul_comm,
      ← smul_eq_mul, LinearEquiv.map_smul]
    exact (ProjSpace.twistObj.algebraMap_smul c _).symm

  let ω : ∀ (i : ℕ) (s : (ProjSpace.stdCoverPullback ι).Idx i), ProjSpace.twistObj (ι ≫ ProjSpace.π A n) ι d ((ProjSpace.stdCoverPullback ι).inter s) → ProjSpace.twistObj (ι' ≫ ProjSpace.π B n) ι' d ((ProjSpace.stdCoverPullback ι').inter s) := fun i s g =>
    (fU' i s).symm (ProjSpace.restrictFun ((h1 i s).trans inf_le_left) ((e.app ((ProjSpace.stdCoverPullback ι).inter s)).hom (fU i s g)))
  have hεs : ∀ (i : ℕ) (s : (ProjSpace.stdCoverPullback ι).Idx i) (c : B) g, εs i s (c ⊗ₜ[A] g) = c • ω i s g := keyform
  let εB : ∀ (i : ℕ) (s : (ProjSpace.stdCoverPullback ι).Idx i), B ⊗[A] ProjSpace.twistObj (ι ≫ ProjSpace.π A n) ι d ((ProjSpace.stdCoverPullback ι).inter s) ≃ₗ[B] ProjSpace.twistObj (ι' ≫ ProjSpace.π B n) ι' d ((ProjSpace.stdCoverPullback ι').inter s) := fun i s =>
    (εs i s).toLinearEquiv (by
      intro b x
      induction x using TensorProduct.induction_on with
      | zero => rw [smul_zero, map_zero, smul_zero]
      | tmul c g => rw [TensorProduct.smul_tmul', smul_eq_mul, hεs, hεs, mul_smul]
      | add x y hx hy => rw [smul_add, map_add, map_add, smul_add, hx, hy])
  have hεB : ∀ (i : ℕ) (s : (ProjSpace.stdCoverPullback ι).Idx i) x, εB i s x = εs i s x := fun _ _ _ => rfl
  let ε : ∀ i : ℕ, B ⊗[A] (ProjSpace.twist (ι ≫ ProjSpace.π A n) ι d).cochain (ProjSpace.stdCoverPullback ι) i ≃ₗ[B] (ProjSpace.twist (ι' ≫ ProjSpace.π B n) ι' d).cochain (ProjSpace.stdCoverPullback ι') i :=
    fun i => (TensorProduct.piRight A B B (fun s : (ProjSpace.stdCoverPullback ι).Idx i => ProjSpace.twistObj (ι ≫ ProjSpace.π A n) ι d ((ProjSpace.stdCoverPullback ι).inter s))).trans
      (LinearEquiv.piCongrRight (fun s => εB i s))
  have hε1 : ∀ (i : ℕ) (c : (ProjSpace.twist (ι ≫ ProjSpace.π A n) ι d).cochain (ProjSpace.stdCoverPullback ι) i) (s : (ProjSpace.stdCoverPullback ι).Idx i),
      ε i ((1 : B) ⊗ₜ[A] c) s = ω i s (c s) := by
    intro i c s
    show εB i s ((TensorProduct.piRight A B B (fun s : (ProjSpace.stdCoverPullback ι).Idx i => ProjSpace.twistObj (ι ≫ ProjSpace.π A n) ι d ((ProjSpace.stdCoverPullback ι).inter s)) ((1 : B) ⊗ₜ[A] c)) s) = _
    rw [TensorProduct.piRight_apply, TensorProduct.piRightHom_tmul, hεB, hεs, one_smul]
  have hval : ∀ (i : ℕ) (c : (ProjSpace.twist (ι ≫ ProjSpace.π A n) ι d).cochain (ProjSpace.stdCoverPullback ι) i)
      (s : (ProjSpace.stdCoverPullback ι).Idx i) (j : Fin (n + 1))
      (h : (ProjSpace.stdCoverPullback ι').inter s ⊓ ProjSpace.pullbackChart ι' j ≤ e ⁻¹ᵁ ((ProjSpace.stdCoverPullback ι).inter s ⊓ ProjSpace.pullbackChart ι j)),
      (ε i ((1 : B) ⊗ₜ[A] c) s).val j =
        ProjSpace.restrictFun h ((e.app ((ProjSpace.stdCoverPullback ι).inter s ⊓ ProjSpace.pullbackChart ι j)) ((c s).val j)) := by
    intro i c s j h
    rw [hε1]
    show ((fU' i s).symm (ProjSpace.restrictFun ((h1 i s).trans inf_le_left) ((e.app ((ProjSpace.stdCoverPullback ι).inter s)).hom (fU i s (c s))))).val j = _
    rw [hfU'2, ProjSpace.restrictFun_restrictFun]

    have hVj : (ProjSpace.stdCoverPullback ι').inter s ⊓ ProjSpace.pullbackChart ι' j ≤ e ⁻¹ᵁ ProjSpace.pullbackChart ι j := by
      rw [preimage_pullbackChart ι B ι' e hcomp]; exact inf_le_right
    have hV0 : (ProjSpace.stdCoverPullback ι').inter s ⊓ ProjSpace.pullbackChart ι' j ≤ e ⁻¹ᵁ ProjSpace.pullbackChart ι (s.1 0).down :=
      inf_le_left.trans ((hpre i s).ge.trans (e.preimage_mono (hU i s)))
    have hVU : (ProjSpace.stdCoverPullback ι').inter s ⊓ ProjSpace.pullbackChart ι' j ≤ e ⁻¹ᵁ (ProjSpace.stdCoverPullback ι).inter s := inf_le_left.trans (hpre i s).ge
    have hVV : (ProjSpace.stdCoverPullback ι').inter s ⊓ ProjSpace.pullbackChart ι' j ≤ e ⁻¹ᵁ (((ProjSpace.stdCoverPullback ι).inter s ⊓ ProjSpace.pullbackChart ι j) ⊓ ProjSpace.pullbackChart ι (s.1 0).down) :=
      le_inf h hV0
    have hW : (ProjSpace.stdCoverPullback ι').inter s ⊓ ProjSpace.pullbackChart ι' j ≤ e ⁻¹ᵁ ((ProjSpace.stdCoverPullback ι).inter s ⊓ ProjSpace.pullbackChart ι (s.1 0).down) := le_inf hVU hV0

    rw [← restrictFun_app_eq e (inf_le_left : ((ProjSpace.stdCoverPullback ι).inter s ⊓ ProjSpace.pullbackChart ι j) ⊓ ProjSpace.pullbackChart ι (s.1 0).down ≤ (ProjSpace.stdCoverPullback ι).inter s ⊓ ProjSpace.pullbackChart ι j) hVV h
      ((c s).val j), (c s).compat j (s.1 0).down]
    let ψ := (ProjSpace.restrictFun hVV).comp (e.app (((ProjSpace.stdCoverPullback ι).inter s ⊓ ProjSpace.pullbackChart ι j) ⊓ ProjSpace.pullbackChart ι (s.1 0).down)).hom
    have hψ : ∀ x, ψ x = ProjSpace.restrictFun hVV ((e.app (((ProjSpace.stdCoverPullback ι).inter s ⊓ ProjSpace.pullbackChart ι j) ⊓ ProjSpace.pullbackChart ι (s.1 0).down)).hom x) :=
      fun _ => rfl
    rw [← hψ, map_mul, map_pow, hψ, hψ]
    rw [restrictFun_app_eq e _ hVV hVj, restrictFun_app_frameUnit ι B ι' e hcomp j (s.1 0).down hVj inf_le_right,
      restrictFun_app_eq e _ hVV hW, ← hfU1 i s (c s), restrictFun_app_eq e _ hW hVU]

  let V' : ∀ (W : Z'.Opens), ProjSpace.twistObj (ι' ≫ ProjSpace.π B n) ι' d W →+ (∀ j : Fin (n + 1), Γ(Z', W ⊓ ProjSpace.pullbackChart ι' j)) := fun W =>
    { toFun := ProjSpace.twistObj.val, map_zero' := ProjSpace.twistObj.zero_val, map_add' := ProjSpace.twistObj.add_val }
  have hV' : ∀ W (g : ProjSpace.twistObj (ι' ≫ ProjSpace.π B n) ι' d W), V' W g = g.val := fun _ _ => rfl
  let V : ∀ (W : Z.Opens), ProjSpace.twistObj (ι ≫ ProjSpace.π A n) ι d W →+ (∀ j : Fin (n + 1), Γ(Z, W ⊓ ProjSpace.pullbackChart ι j)) := fun W =>
    { toFun := ProjSpace.twistObj.val, map_zero' := ProjSpace.twistObj.zero_val, map_add' := ProjSpace.twistObj.add_val }
  have hV : ∀ W (g : ProjSpace.twistObj (ι ≫ ProjSpace.π A n) ι d W), V W g = g.val := fun _ _ => rfl
  refine ⟨ε, ?_, hval⟩
  intro i

  have key1 : ∀ c : (ProjSpace.twist (ι ≫ ProjSpace.π A n) ι d).cochain (ProjSpace.stdCoverPullback ι) i,
      ε (i + 1) ((1 : B) ⊗ₜ[A] ((ProjSpace.twist (ι ≫ ProjSpace.π A n) ι d).d (ProjSpace.stdCoverPullback ι) i c))
        = (ProjSpace.twist (ι' ≫ ProjSpace.π B n) ι' d).d (ProjSpace.stdCoverPullback ι') i (ε i ((1 : B) ⊗ₜ[A] c)) := by
    intro c
    funext s
    apply ProjSpace.twistObj.ext
    funext j
    have hj : ∀ (W : Z'.Opens), W ⊓ ProjSpace.pullbackChart ι' j ≤ e ⁻¹ᵁ ProjSpace.pullbackChart ι j := fun W => by
      rw [preimage_pullbackChart ι B ι' e hcomp]; exact inf_le_right
    have hL := hval (i + 1) ((ProjSpace.twist (ι ≫ ProjSpace.π A n) ι d).d (ProjSpace.stdCoverPullback ι) i c) s j
      (show _ ≤ e ⁻¹ᵁ ((ProjSpace.stdCoverPullback ι).inter s ⊓ ProjSpace.pullbackChart ι j) from
        le_inf (inf_le_left.trans (hpre (i + 1) s).ge) (hj _))
    rw [hL, OModulePresheaf.d_apply, OModulePresheaf.d_apply]
    erw [val_sum', val_sum']
    simp only [P2mWs6C3.val_zsmul', Finset.sum_apply, Pi.smul_apply, ProjSpace.twist_res_val, map_sum]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [map_zsmul, map_zsmul]
    congr 1
    have hface : (ProjSpace.stdCoverPullback ι').inter s ⊓ ProjSpace.pullbackChart ι' j ≤
        (ProjSpace.stdCoverPullback ι').inter ((ProjSpace.stdCoverPullback ι').face s t) ⊓ ProjSpace.pullbackChart ι' j :=
      inf_le_inf_right _ ((ProjSpace.stdCoverPullback ι').inter_le_inter_face s t)
    have hface' : (ProjSpace.stdCoverPullback ι').inter ((ProjSpace.stdCoverPullback ι').face s t) ⊓ ProjSpace.pullbackChart ι' j ≤
        e ⁻¹ᵁ ((ProjSpace.stdCoverPullback ι).inter ((ProjSpace.stdCoverPullback ι).face s t) ⊓ ProjSpace.pullbackChart ι j) :=
      show _ ≤ e ⁻¹ᵁ ((ProjSpace.stdCoverPullback ι).inter ((ProjSpace.stdCoverPullback ι).face s t) ⊓ ProjSpace.pullbackChart ι j) from
        le_inf (inf_le_left.trans (hpre i _).ge) (hj _)
    rw [hval i c ((ProjSpace.stdCoverPullback ι').face s t) j hface', ProjSpace.restrictFun_restrictFun]
    exact (restrictFun_app_eq e _ _ (hface.trans hface') _).trans rfl
  apply LinearMap.ext
  intro x
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul b c =>
    have hb : ∀ (M : Type u) [AddCommGroup M] [Module A M] (m : M), b ⊗ₜ[A] m = b • ((1 : B) ⊗ₜ[A] m) := by
      intro M _ _ m
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.baseChange_tmul, LinearEquiv.coe_coe, LinearEquiv.coe_coe,
      hb, hb, LinearEquiv.map_smul, LinearEquiv.map_smul, LinearMap.map_smul, key1]
  | add x y hx hy => rw [map_add, map_add, hx, hy]

end S_AlgebraicGeometry_ProjSpace_exists_linearEquiv_baseChange_cochain_twist_of_isPullback
end P2MW
export P2MW.S_AlgebraicGeometry_ProjSpace_exists_linearEquiv_baseChange_cochain_twist_of_isPullback (solution)
