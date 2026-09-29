-- Prove2me | solution 1 for AlgebraicGeometry.ProjSpace.ker_baseChange_le_range_and_finrank_ker_eq_of_point_of_isPullback
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/4b0e46bf-84b9-525b-89e8-04770c072b04

import Mathlib
import Definitions.Def_AlgebraicGeometry_ProjSpace
import Definitions.Def_AlgebraicGeometry_ProjSpaceCover
import Definitions.Def_AlgebraicGeometry_ProjTwistDatum
import Definitions.Def_AlgebraicGeometry_HilbertFunctor
import Theorems.Thm_AlgebraicGeometry_ProjSpace_exists_linearEquiv_baseChange_cochain_twist_of_isPullback
import Theorems.Thm_AlgebraicGeometry_ProjSpace_exists_linearMap_homogeneousSubmodule_twistObj_top_val_eq
import Theorems.Thm_AlgebraicGeometry_ProjSpace_map_preimage_basicOpen_X
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverComap
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_ProjSpace_ker_baseChange_le_range_and_finrank_ker_eq_of_point_of_isPullback

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MvPolynomial TensorProduct AlgebraicGeometry.HilbertFunctor

attribute [local instance] MvPolynomial.gradedAlgebra

namespace P2mWs6K4C

section Pull
variable {A : Type u} [CommRing A] {n : ℕ} {Z : Scheme.{u}}
  (ι : Z ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A)) [IsAffineHom ι]
  (B : Type u) [CommRing B] [Algebra A B] {Z' : Scheme.{u}}
  (ι' : Z' ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) B)) [IsAffineHom ι']
  (e : Z' ⟶ Z)

local notation "𝒜A" => MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A
local notation "𝒜B" => MvPolynomial.homogeneousSubmodule (Fin (n + 1)) B

open HomogeneousLocalization

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

theorem toB_mk (i : Fin (n + 1)) (d : ℕ) (F : MvPolynomial (Fin (n + 1)) A) (hF : F ∈ 𝒜A d) :
    toB (A := A) B i (HomogeneousLocalization.mk
      ({ deg := d, num := ⟨F, hF⟩,
         den := ⟨MvPolynomial.X i ^ d, (MvPolynomial.mem_homogeneousSubmodule d _).mpr (MvPolynomial.isHomogeneous_X_pow i d)⟩,
         den_mem := ⟨d, rfl⟩ } : NumDenSameDeg 𝒜A (Submonoid.powers (MvPolynomial.X i))))
    = HomogeneousLocalization.mk
      ({ deg := d, num := ⟨MvPolynomial.map (algebraMap A B) F, ((MvPolynomial.mem_homogeneousSubmodule d F).mp hF).map _⟩,
         den := ⟨MvPolynomial.X i ^ d, (MvPolynomial.mem_homogeneousSubmodule d _).mpr (MvPolynomial.isHomogeneous_X_pow i d)⟩,
         den_mem := ⟨d, rfl⟩ } : NumDenSameDeg 𝒜B (Submonoid.powers (MvPolynomial.X i))) := by
  have step : Away.map (ProjSpace.mvMapGraded A B n) (MvPolynomial.X i) (HomogeneousLocalization.mk
      ({ deg := d, num := ⟨F, hF⟩,
         den := ⟨MvPolynomial.X i ^ d, (MvPolynomial.mem_homogeneousSubmodule d _).mpr (MvPolynomial.isHomogeneous_X_pow i d)⟩,
         den_mem := ⟨d, rfl⟩ } : NumDenSameDeg 𝒜A (Submonoid.powers (MvPolynomial.X i))))
      = HomogeneousLocalization.mk
        ({ deg := d, num := ⟨(ProjSpace.mvMapGraded A B n) F, Graded.map_mem _ hF⟩,
           den := ⟨(ProjSpace.mvMapGraded A B n) (MvPolynomial.X i) ^ d, by
             rw [ProjSpace.mvMapGraded_X]
             exact (MvPolynomial.mem_homogeneousSubmodule d _).mpr (MvPolynomial.isHomogeneous_X_pow i d)⟩,
           den_mem := ⟨d, rfl⟩ } : NumDenSameDeg 𝒜B (Submonoid.powers ((ProjSpace.mvMapGraded A B n) (MvPolynomial.X i)))) := by
    apply HomogeneousLocalization.val_injective
    rw [Away.map, HomogeneousLocalization.map_mk, HomogeneousLocalization.val_mk, HomogeneousLocalization.val_mk,
      Localization.mk_eq_mk_iff, Localization.r_iff_exists]
    exact ⟨1, by simp [map_pow]⟩
  apply HomogeneousLocalization.val_injective
  rw [toB, RingHom.comp_apply, step, val_awayMap_mk, HomogeneousLocalization.val_mk]
  simp only [one_pow, mul_one]
  rfl

end Pull

theorem subsingleton_HSucc_iff {R : Type u} [CommRing R] {V : Scheme.{u}} {π : V ⟶ Spec (.of R)}
    (F : OModulePresheaf π) (K : V.OrderedAffineCover) (i : ℕ) :
    Subsingleton (F.HSucc K i) ↔ LinearMap.ker (F.d K (i + 1)) ≤ LinearMap.range (F.d K i) := by
  constructor
  · intro h x hx
    have : (Submodule.Quotient.mk ⟨x, hx⟩ : F.HSucc K i) = 0 := Subsingleton.elim _ _
    rw [Submodule.Quotient.mk_eq_zero] at this
    exact this
  · intro h
    refine ⟨fun a b => ?_⟩
    induction a using Submodule.Quotient.induction_on with | _ a =>
    induction b using Submodule.Quotient.induction_on with | _ b =>
    rw [Submodule.Quotient.eq]
    show (a - b).1 ∈ LinearMap.range (F.d K i)
    exact h (a - b).2

end P2mWs6K4C

open P2mWs6K4C in
set_option maxHeartbeats 3200000 in
theorem solution
    {A₀ : Type u} [CommRing A₀] {n : ℕ} {Z₀ : Scheme.{u}}
    (ι₀ : Z₀ ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A₀)) [IsClosedImmersion ι₀]
    (K : Type u) [Field K] [Algebra A₀ K] {ZK : Scheme.{u}}
    (ιK : ZK ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) K)) [IsClosedImmersion ιK]
    (e : ZK ⟶ Z₀)
    (hpb : IsPullback e (ιK ≫ ProjSpace.π K n) (ι₀ ≫ ProjSpace.π A₀ n) (Spec.map (CommRingCat.ofHom (algebraMap A₀ K))))
    (hcomp : e ≫ ι₀ = ιK ≫ ProjSpace.map A₀ K n) (d : ℕ)
    (Θ₀ : ↥(MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A₀ d) →ₗ[A₀] (ProjSpace.twist (ι₀ ≫ ProjSpace.π A₀ n) ι₀ d).cochain (ProjSpace.stdCoverPullback ι₀) 0)
    (hΘ₀ : ∀ (F : MvPolynomial (Fin (n + 1)) A₀) (hF : F.IsHomogeneous d) (s : (ProjSpace.stdCoverPullback ι₀).Idx 0) (i : Fin (n + 1)),
      (Θ₀ ⟨F, (MvPolynomial.mem_homogeneousSubmodule d F).mpr hF⟩ s).val i =
        ProjSpace.restrictFun
          (inf_le_right : (ProjSpace.stdCoverPullback ι₀).inter s ⊓ ProjSpace.pullbackChart ι₀ i ≤ ProjSpace.pullbackChart ι₀ i)
          ((ι₀.app (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A₀) (MvPolynomial.X i)))
                (Proj.awayToSection (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A₀) (MvPolynomial.X i)
                  (HomogeneousLocalization.mk
                    { deg := d
                      num := ⟨F, (MvPolynomial.mem_homogeneousSubmodule d F).mpr hF⟩
                      den := ⟨MvPolynomial.X i ^ d, (MvPolynomial.mem_homogeneousSubmodule d _).mpr
                        (MvPolynomial.isHomogeneous_X_pow i d)⟩
                      den_mem := ⟨d, rfl⟩ }))))
    (h : ℕ → ℕ) (q : Point K n h)
    (hq : ∀ (F : MvPolynomial (Fin (n + 1)) K) (hF : F.IsHomogeneous d),
      (F ∈ q.I ↔ ∀ i : Fin (n + 1), ((ιK.app (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) K) (MvPolynomial.X i)))
                (Proj.awayToSection (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) K) (MvPolynomial.X i)
                  (HomogeneousLocalization.mk
                    { deg := d
                      num := ⟨F, (MvPolynomial.mem_homogeneousSubmodule d F).mpr hF⟩
                      den := ⟨MvPolynomial.X i ^ d, (MvPolynomial.mem_homogeneousSubmodule d _).mpr
                        (MvPolynomial.isHomogeneous_X_pow i d)⟩
                      den_mem := ⟨d, rfl⟩ }))) = 0))
    (ha : ∀ i : ℕ, Subsingleton ((ProjSpace.twist (ιK ≫ ProjSpace.π K n) ιK d).HSucc (ProjSpace.stdCoverPullback ιK) i))
    (hb : ∀ c ∈ (ProjSpace.twist (ιK ≫ ProjSpace.π K n) ιK d).H0 (ProjSpace.stdCoverPullback ιK),
      ∃ (F : MvPolynomial (Fin (n + 1)) K) (hF : F.IsHomogeneous d),
        ∀ (s : (ProjSpace.stdCoverPullback ιK).Idx 0) (i : Fin (n + 1)),
          (c s).val i =
            ProjSpace.restrictFun
              (inf_le_right : (ProjSpace.stdCoverPullback ιK).inter s ⊓ ProjSpace.pullbackChart ιK i ≤ ProjSpace.pullbackChart ιK i)
              ((ιK.app (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) K) (MvPolynomial.X i)))
                (Proj.awayToSection (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) K) (MvPolynomial.X i)
                  (HomogeneousLocalization.mk
                    { deg := d
                      num := ⟨F, (MvPolynomial.mem_homogeneousSubmodule d F).mpr hF⟩
                      den := ⟨MvPolynomial.X i ^ d, (MvPolynomial.mem_homogeneousSubmodule d _).mpr
                        (MvPolynomial.isHomogeneous_X_pow i d)⟩
                      den_mem := ⟨d, rfl⟩ })))) :
    (∀ i : ℕ, LinearMap.ker (((ProjSpace.twist (ι₀ ≫ ProjSpace.π A₀ n) ι₀ d).d (ProjSpace.stdCoverPullback ι₀) (i + 1)).baseChange K) ≤
      LinearMap.range (((ProjSpace.twist (ι₀ ≫ ProjSpace.π A₀ n) ι₀ d).d (ProjSpace.stdCoverPullback ι₀) i).baseChange K)) ∧
    LinearMap.ker (((ProjSpace.twist (ι₀ ≫ ProjSpace.π A₀ n) ι₀ d).d (ProjSpace.stdCoverPullback ι₀) 0).baseChange K) ≤ LinearMap.range (Θ₀.baseChange K) ∧
    Module.finrank K (LinearMap.ker (((ProjSpace.twist (ι₀ ≫ ProjSpace.π A₀ n) ι₀ d).d (ProjSpace.stdCoverPullback ι₀) 0).baseChange K)) = h d := by
  classical
  obtain ⟨ε, hεd, hεval⟩ := AlgebraicGeometry.ProjSpace.exists_linearEquiv_baseChange_cochain_twist_of_isPullback ι₀ K ιK e hpb hcomp d
  have hεd' : ∀ (i : ℕ) (y), ε (i + 1) (((ProjSpace.twist (ι₀ ≫ ProjSpace.π A₀ n) ι₀ d).d (ProjSpace.stdCoverPullback ι₀) i).baseChange K y) = (ProjSpace.twist (ιK ≫ ProjSpace.π K n) ιK d).d (ProjSpace.stdCoverPullback ιK) i (ε i y) :=
    fun i y => LinearMap.congr_fun (hεd i) y

  have hi : ∀ i : ℕ, LinearMap.ker (((ProjSpace.twist (ι₀ ≫ ProjSpace.π A₀ n) ι₀ d).d (ProjSpace.stdCoverPullback ι₀) (i + 1)).baseChange K) ≤ LinearMap.range (((ProjSpace.twist (ι₀ ≫ ProjSpace.π A₀ n) ι₀ d).d (ProjSpace.stdCoverPullback ι₀) i).baseChange K) := by
    intro i x hx
    have hx' : ε (i + 1) x ∈ LinearMap.ker ((ProjSpace.twist (ιK ≫ ProjSpace.π K n) ιK d).d (ProjSpace.stdCoverPullback ιK) (i + 1)) := by
      rw [LinearMap.mem_ker, ← hεd', show ((ProjSpace.twist (ι₀ ≫ ProjSpace.π A₀ n) ι₀ d).d (ProjSpace.stdCoverPullback ι₀) (i + 1)).baseChange K x = 0 from hx, map_zero]
    obtain ⟨w, hw⟩ := (subsingleton_HSucc_iff _ _ i).1 (ha i) hx'
    obtain ⟨z, rfl⟩ := (ε i).surjective w
    refine ⟨z, (ε (i + 1)).injective ?_⟩
    rw [hεd', hw]

  obtain ⟨θK, hθKval, hθKiff⟩ := AlgebraicGeometry.ProjSpace.exists_linearMap_homogeneousSubmodule_twistObj_top_val_eq ιK d (k := K)
  let r0K : ProjSpace.twistObj (ιK ≫ ProjSpace.π K n) ιK d ⊤ →ₗ[K] (ProjSpace.twist (ιK ≫ ProjSpace.π K n) ιK d).cochain (ProjSpace.stdCoverPullback ιK) 0 :=
    LinearMap.pi (fun s => (ProjSpace.twist (ιK ≫ ProjSpace.π K n) ιK d).res (le_top : (ProjSpace.stdCoverPullback ιK).inter s ≤ ⊤))
  let cK : ↥(MvPolynomial.homogeneousSubmodule (Fin (n + 1)) K d) →ₗ[K] (ProjSpace.twist (ιK ≫ ProjSpace.π K n) ιK d).cochain (ProjSpace.stdCoverPullback ιK) 0 := r0K ∘ₗ θK
  have hcK : ∀ p s, cK p s = (ProjSpace.twist (ιK ≫ ProjSpace.π K n) ιK d).res (le_top : (ProjSpace.stdCoverPullback ιK).inter s ≤ ⊤) (θK p) := fun _ _ => rfl
  have hsingle : ∀ j : Fin (n + 1), ∃ s : (ProjSpace.stdCoverPullback ιK).Idx 0, ProjSpace.pullbackChart ιK j ≤ (ProjSpace.stdCoverPullback ιK).inter s := by
    intro j
    refine ⟨⟨fun _ => ⟨j⟩, fun a b h => absurd h (by omega)⟩, ?_⟩
    refine le_iInf fun t => ?_
    rw [ProjSpace.stdCoverPullback_U, ProjSpace.stdCover_U, ProjSpace.pullbackChart_eq]
  have hr0K_inj : ∀ g, r0K g = 0 → g = 0 := by
    intro g hg
    apply ProjSpace.twistObj.ext
    funext j
    obtain ⟨s, hs⟩ := hsingle j
    have hs0 : (ProjSpace.twist (ιK ≫ ProjSpace.π K n) ιK d).res (le_top : (ProjSpace.stdCoverPullback ιK).inter s ≤ ⊤) g = 0 := congr_fun hg s
    have h1 : ((ProjSpace.twist (ιK ≫ ProjSpace.π K n) ιK d).res (le_top : (ProjSpace.stdCoverPullback ιK).inter s ≤ ⊤) g).val j = 0 := by
      rw [hs0]; rfl
    rw [ProjSpace.twist_res_val] at h1
    have h2 : (⊤ : ZK.Opens) ⊓ ProjSpace.pullbackChart ιK j ≤ (ProjSpace.stdCoverPullback ιK).inter s ⊓ ProjSpace.pullbackChart ιK j :=
      le_inf (inf_le_right.trans hs) inf_le_right
    have := congrArg (ProjSpace.restrictFun h2) h1
    rw [ProjSpace.restrictFun_restrictFun, map_zero] at this
    rw [ProjSpace.twistObj.zero_val, Pi.zero_apply, ← this]
    exact (ProjSpace.restrictFun_refl _).symm

  have hker : LinearMap.ker cK = Submodule.comap (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) K d).subtype (q.I.restrictScalars K) := by
    ext p
    obtain ⟨F, hFmem⟩ := p
    have hF : F.IsHomogeneous d := (MvPolynomial.mem_homogeneousSubmodule d F).mp hFmem
    rw [LinearMap.mem_ker, Submodule.mem_comap, Submodule.subtype_apply, Submodule.restrictScalars_mem]
    change cK ⟨F, (MvPolynomial.mem_homogeneousSubmodule d F).mpr hF⟩ = 0 ↔ F ∈ q.I
    rw [hq F hF, ← (hθKiff F hF)]
    constructor
    · intro h0; exact hr0K_inj _ h0
    · intro h0; show r0K (θK _) = 0; rw [h0, map_zero]

  have hrange_le : LinearMap.range cK ≤ (ProjSpace.twist (ιK ≫ ProjSpace.π K n) ιK d).H0 (ProjSpace.stdCoverPullback ιK) := by
    rintro _ ⟨p, rfl⟩
    show (ProjSpace.twist (ιK ≫ ProjSpace.π K n) ιK d).d (ProjSpace.stdCoverPullback ιK) 0 (cK p) = 0
    funext s
    rw [OModulePresheaf.d_apply, Fin.sum_univ_two]
    simp only [Fin.val_zero, pow_zero, one_smul, Fin.val_one, pow_one, neg_smul, hcK, OModulePresheaf.res_res]
    exact add_neg_cancel _
  have hrange_ge : (ProjSpace.twist (ιK ≫ ProjSpace.π K n) ιK d).H0 (ProjSpace.stdCoverPullback ιK) ≤ LinearMap.range cK := by
    intro c hc
    obtain ⟨F, hF, hcF⟩ := hb c hc
    refine ⟨⟨F, (MvPolynomial.mem_homogeneousSubmodule d F).mpr hF⟩, ?_⟩
    funext s
    apply ProjSpace.twistObj.ext
    funext j
    show ((ProjSpace.twist (ιK ≫ ProjSpace.π K n) ιK d).res (le_top : (ProjSpace.stdCoverPullback ιK).inter s ≤ ⊤) (θK ⟨F, _⟩)).val j = (c s).val j
    rw [ProjSpace.twist_res_val, hθKval F hF j, ProjSpace.restrictFun_restrictFun, hcF s j]
  have hrange : LinearMap.range cK = (ProjSpace.twist (ιK ≫ ProjSpace.π K n) ιK d).H0 (ProjSpace.stdCoverPullback ιK) := le_antisymm hrange_le hrange_ge

  have hkerε : ∀ y, y ∈ LinearMap.ker (((ProjSpace.twist (ι₀ ≫ ProjSpace.π A₀ n) ι₀ d).d (ProjSpace.stdCoverPullback ι₀) 0).baseChange K) ↔ ε 0 y ∈ (ProjSpace.twist (ιK ≫ ProjSpace.π K n) ιK d).H0 (ProjSpace.stdCoverPullback ιK) := by
    intro y
    rw [LinearMap.mem_ker]
    constructor
    · intro hy; show (ProjSpace.twist (ιK ≫ ProjSpace.π K n) ιK d).d (ProjSpace.stdCoverPullback ιK) 0 (ε 0 y) = 0; rw [← hεd', hy, map_zero]
    · intro hy; apply (ε 1).injective; rw [hεd', map_zero]; exact hy

  have hnat : ∀ (G : MvPolynomial (Fin (n + 1)) A₀) (hG : G.IsHomogeneous d),
      ε 0 ((1 : K) ⊗ₜ[A₀] Θ₀ ⟨G, (MvPolynomial.mem_homogeneousSubmodule d G).mpr hG⟩)
        = cK ⟨MvPolynomial.map (algebraMap A₀ K) G, (MvPolynomial.mem_homogeneousSubmodule d _).mpr (hG.map _)⟩ := by
    intro G hG
    funext s
    apply ProjSpace.twistObj.ext
    funext j
    have hj : (ProjSpace.stdCoverPullback ιK).inter s ⊓ ProjSpace.pullbackChart ιK j ≤ e ⁻¹ᵁ ProjSpace.pullbackChart ι₀ j := by
      rw [preimage_pullbackChart ι₀ K ιK e hcomp]; exact inf_le_right
    have h : (ProjSpace.stdCoverPullback ιK).inter s ⊓ ProjSpace.pullbackChart ιK j ≤ e ⁻¹ᵁ ((ProjSpace.stdCoverPullback ι₀).inter s ⊓ ProjSpace.pullbackChart ι₀ j) :=
      show _ ≤ e ⁻¹ᵁ ((ProjSpace.stdCoverPullback ι₀).inter s ⊓ ProjSpace.pullbackChart ι₀ j) from
        le_inf (inf_le_left.trans (preimage_inter ι₀ K ιK e hcomp s).ge) hj
    rw [hεval 0 _ s j h, hcK, hΘ₀ G hG s j]
    show ProjSpace.restrictFun h ((e.app _) (ProjSpace.restrictFun _ _)) =
      ((ProjSpace.twist (ιK ≫ ProjSpace.π K n) ιK d).res (le_top : (ProjSpace.stdCoverPullback ιK).inter s ≤ ⊤) (θK ⟨MvPolynomial.map (algebraMap A₀ K) G, _⟩)).val j
    rw [ProjSpace.twist_res_val, hθKval (MvPolynomial.map (algebraMap A₀ K) G) (hG.map _) j,
      ProjSpace.restrictFun_restrictFun, restrictFun_app_eq e _ h hj]
    exact (restrictFun_app_pullAway ι₀ K ιK e hcomp j _ hj inf_le_right).trans (by rw [toB_mk])

  have hii : LinearMap.ker (((ProjSpace.twist (ι₀ ≫ ProjSpace.π A₀ n) ι₀ d).d (ProjSpace.stdCoverPullback ι₀) 0).baseChange K) ≤ LinearMap.range (Θ₀.baseChange K) := by
    intro y hy
    have hy' := (hkerε y).1 hy
    rw [← hrange] at hy'
    obtain ⟨p, hp⟩ := hy'

    obtain ⟨F, hFmem⟩ := p
    have hF : F.IsHomogeneous d := (MvPolynomial.mem_homogeneousSubmodule d F).mp hFmem

    have key : ∀ (α : Fin (n + 1) →₀ ℕ) (hα : α ∈ F.support), ∃ t : K ⊗[A₀] ↥(MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A₀ d),
        ε 0 ((Θ₀.baseChange K) t) = cK ⟨MvPolynomial.monomial α (MvPolynomial.coeff α F), by
          rw [MvPolynomial.mem_homogeneousSubmodule]
          exact (MvPolynomial.isHomogeneous_monomial _ (by
            rw [Finsupp.degree_eq_weight_one]; exact hF (MvPolynomial.mem_support_iff.mp hα)))⟩ := by
      intro α hα
      have hdeg : (MvPolynomial.monomial α (1 : A₀)).IsHomogeneous d :=
        MvPolynomial.isHomogeneous_monomial _ (by
          rw [Finsupp.degree_eq_weight_one]; exact hF (MvPolynomial.mem_support_iff.mp hα))
      refine ⟨MvPolynomial.coeff α F ⊗ₜ[A₀] ⟨MvPolynomial.monomial α 1, (MvPolynomial.mem_homogeneousSubmodule d _).mpr hdeg⟩, ?_⟩
      have hc : MvPolynomial.coeff α F ⊗ₜ[A₀] (⟨MvPolynomial.monomial α 1, (MvPolynomial.mem_homogeneousSubmodule d _).mpr hdeg⟩ :
            ↥(MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A₀ d))
          = MvPolynomial.coeff α F • ((1 : K) ⊗ₜ[A₀] ⟨MvPolynomial.monomial α 1, (MvPolynomial.mem_homogeneousSubmodule d _).mpr hdeg⟩) := by
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      rw [hc, LinearMap.map_smul, LinearEquiv.map_smul, LinearMap.baseChange_tmul, hnat _ hdeg, ← LinearMap.map_smul]
      congr 1
      apply Subtype.ext
      show MvPolynomial.coeff α F • MvPolynomial.map (algebraMap A₀ K) (MvPolynomial.monomial α 1) = MvPolynomial.monomial α (MvPolynomial.coeff α F)
      rw [MvPolynomial.map_monomial, map_one, MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
    choose tα htα using key
    refine ⟨∑ α ∈ F.support.attach, tα α.1 α.2, ?_⟩
    apply (ε 0).injective
    rw [map_sum, map_sum, ← hp]
    rw [Finset.sum_congr rfl (fun α _ => htα α.1 α.2), ← map_sum]
    congr 1
    apply Subtype.ext
    rw [Submodule.coe_sum]
    show ∑ α ∈ F.support.attach, MvPolynomial.monomial α.1 (MvPolynomial.coeff α.1 F) = F
    rw [Finset.sum_attach F.support (fun α => MvPolynomial.monomial α (MvPolynomial.coeff α F))]
    exact (MvPolynomial.as_sum F).symm

  have hiii : Module.finrank K ↥(LinearMap.ker (((ProjSpace.twist (ι₀ ≫ ProjSpace.π A₀ n) ι₀ d).d (ProjSpace.stdCoverPullback ι₀) 0).baseChange K)) = h d := by
    have eK : ↥(LinearMap.ker (((ProjSpace.twist (ι₀ ≫ ProjSpace.π A₀ n) ι₀ d).d (ProjSpace.stdCoverPullback ι₀) 0).baseChange K)) ≃ₗ[K] ↥((ProjSpace.twist (ιK ≫ ProjSpace.π K n) ιK d).H0 (ProjSpace.stdCoverPullback ιK)) := by
      refine LinearEquiv.ofSubmodules (ε 0) _ _ ?_
      apply le_antisymm
      · rintro _ ⟨y, hy, rfl⟩; exact (hkerε y).1 hy
      · intro x hx
        refine ⟨(ε 0).symm x, (hkerε _).2 (by rw [LinearEquiv.apply_symm_apply]; exact hx), (ε 0).apply_symm_apply x⟩
    rw [eK.finrank_eq, ← (LinearEquiv.ofEq _ _ hrange).finrank_eq, ← cK.quotKerEquivRange.finrank_eq,
      ← (Submodule.quotEquivOfEq _ _ hker.symm).finrank_eq]

    haveI := q.finite_piece d
    haveI := q.projective_piece d
    have hr := q.rankAtStalk_piece d ⟨(⊥ : Ideal K), Ideal.isPrime_bot⟩
    rw [Module.rankAtStalk_eq_finrank_of_free] at hr
    exact hr
  exact ⟨hi, hii, hiii⟩

end S_AlgebraicGeometry_ProjSpace_ker_baseChange_le_range_and_finrank_ker_eq_of_point_of_isPullback
end P2MW
export P2MW.S_AlgebraicGeometry_ProjSpace_ker_baseChange_le_range_and_finrank_ker_eq_of_point_of_isPullback (solution)
