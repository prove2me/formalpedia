-- Prove2me | solution 1 for AlgebraicGeometry.ProjSpace.forall_H0_twist_exists_isHomogeneous_of_baseChange_field
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/a916ca39-621a-5dfb-a89b-edb823334271

import Mathlib
import Definitions.Def_AlgebraicGeometry_ProjSpace
import Definitions.Def_AlgebraicGeometry_ProjSpaceCover
import Definitions.Def_AlgebraicGeometry_ProjTwistDatum
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverComap
import Theorems.Thm_AlgebraicGeometry_ProjSpace_map_preimage_basicOpen_X
import Theorems.Thm_AlgebraicGeometry_ProjSpace_exists_linearEquiv_baseChange_cochain_twist_of_isPullback
import Theorems.Thm_AlgebraicGeometry_ProjSpace_exists_linearMap_homogeneousSubmodule_twistObj_top_val_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_ProjSpace_forall_H0_twist_exists_isHomogeneous_of_baseChange_field

set_option autoImplicit false
set_option linter.unusedSectionVars false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MvPolynomial TensorProduct

attribute [local instance] MvPolynomial.gradedAlgebra

open HomogeneousLocalization

namespace RM6Sol

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

theorem toB_mkDeg (i : Fin (n + 1)) (d : ℕ) (F : MvPolynomial (Fin (n + 1)) A) (hF : F.IsHomogeneous d) :
    toB (A := A) B i (HomogeneousLocalization.mk
        { deg := d
          num := ⟨F, (MvPolynomial.mem_homogeneousSubmodule d F).mpr hF⟩
          den := ⟨MvPolynomial.X i ^ d, (MvPolynomial.mem_homogeneousSubmodule d _).mpr (MvPolynomial.isHomogeneous_X_pow i d)⟩
          den_mem := ⟨d, rfl⟩ } : Away 𝒜A (MvPolynomial.X i)) =
      (HomogeneousLocalization.mk
        { deg := d
          num := ⟨MvPolynomial.map (algebraMap A B) F,
            (MvPolynomial.mem_homogeneousSubmodule d _).mpr (hF.map (algebraMap A B))⟩
          den := ⟨MvPolynomial.X i ^ d, (MvPolynomial.mem_homogeneousSubmodule d _).mpr (MvPolynomial.isHomogeneous_X_pow i d)⟩
          den_mem := ⟨d, rfl⟩ } : Away 𝒜B (MvPolynomial.X i)) := by
  have hg : ∀ G : MvPolynomial (Fin (n + 1)) A, (ProjSpace.mvMapGraded A B n) G = MvPolynomial.map (algebraMap A B) G :=
    fun G => rfl
  have e1 : (HomogeneousLocalization.mk
        { deg := d
          num := ⟨F, (MvPolynomial.mem_homogeneousSubmodule d F).mpr hF⟩
          den := ⟨MvPolynomial.X i ^ d, (MvPolynomial.mem_homogeneousSubmodule d _).mpr (MvPolynomial.isHomogeneous_X_pow i d)⟩
          den_mem := ⟨d, rfl⟩ } : Away 𝒜A (MvPolynomial.X i)) =
      Away.mk 𝒜A (ProjSpace.X_mem_one A n i) d F
        (by simpa using (MvPolynomial.mem_homogeneousSubmodule d F).mpr hF) := by
    apply HomogeneousLocalization.val_injective
    rw [Away.val_mk, HomogeneousLocalization.val_mk]
  rw [e1, toB, RingHom.comp_apply, Away.map_mk, awayMap_mk]
  apply HomogeneousLocalization.val_injective
  rw [Away.val_mk, HomogeneousLocalization.val_mk, Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  refine ⟨1, ?_⟩
  simp [hg]

end Setup

section Theta

variable {n : ℕ} {k : Type u} [Field k] {Zk : Scheme.{u}}
  (ιk : Zk ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k)) [IsAffineHom ιk] (d : ℕ)

noncomputable def chartVal (F : MvPolynomial (Fin (n + 1)) k) (hF : F.IsHomogeneous d) (i : Fin (n + 1)) :
    Γ(Zk, ProjSpace.pullbackChart ιk i) :=
  (ιk.app (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k) (MvPolynomial.X i)))
    (Proj.awayToSection (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k) (MvPolynomial.X i)
      (HomogeneousLocalization.mk
        { deg := d
          num := ⟨F, (MvPolynomial.mem_homogeneousSubmodule d F).mpr hF⟩
          den := ⟨MvPolynomial.X i ^ d, (MvPolynomial.mem_homogeneousSubmodule d _).mpr
            (MvPolynomial.isHomogeneous_X_pow i d)⟩
          den_mem := ⟨d, rfl⟩ }))

theorem isHomogeneous_of_mem (F : ↥(MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k d)) :
    (F : MvPolynomial (Fin (n + 1)) k).IsHomogeneous d :=
  (MvPolynomial.mem_homogeneousSubmodule d _).mp F.2

def vertex (i : Fin (n + 1)) : (ProjSpace.stdCoverPullback ιk).Idx 0 :=
  ⟨fun _ => ULift.up i, fun a b hab => absurd (Fin.lt_def.mp hab) (by have := a.isLt; have := b.isLt; omega)⟩

theorem chart_le_inter_vertex (i : Fin (n + 1)) :
    ProjSpace.pullbackChart ιk i ≤ (ProjSpace.stdCoverPullback ιk).inter (vertex ιk i) ⊓ ProjSpace.pullbackChart ιk i :=
  le_inf (le_iInf fun _ => le_rfl) le_rfl

theorem exists_theta :
    ∃ Θ : ↥(MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k d) →ₗ[k]
        ↥((ProjSpace.twist (ιk ≫ ProjSpace.π k n) ιk d).H0 (ProjSpace.stdCoverPullback ιk)),
      ∀ (F : ↥(MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k d))
        (s : (ProjSpace.stdCoverPullback ιk).Idx 0) (i : Fin (n + 1)),
        ((Θ F : (ProjSpace.twist (ιk ≫ ProjSpace.π k n) ιk d).cochain (ProjSpace.stdCoverPullback ιk) 0) s).val i =
          ProjSpace.restrictFun
            (inf_le_right : (ProjSpace.stdCoverPullback ιk).inter s ⊓ ProjSpace.pullbackChart ιk i ≤ ProjSpace.pullbackChart ιk i)
            (chartVal ιk d F (isHomogeneous_of_mem d F) i) := by
  obtain ⟨θ, hθ, -⟩ := ProjSpace.exists_linearMap_homogeneousSubmodule_twistObj_top_val_eq ιk d

  let T := ProjSpace.twist (ιk ≫ ProjSpace.π k n) ιk d
  let K := ProjSpace.stdCoverPullback ιk
  let Θ₀ : ↥(MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k d) →ₗ[k] T.cochain K 0 :=
    LinearMap.pi fun s => (T.res (le_top : K.inter s ≤ ⊤)).comp θ
  have hΘ₀ : ∀ F s, Θ₀ F s = T.res (le_top : K.inter s ≤ ⊤) (θ F) := fun F s => rfl
  have hcoc : ∀ F, Θ₀ F ∈ T.H0 K := by
    intro F
    rw [LinearMap.mem_ker]
    funext s
    rw [OModulePresheaf.d_apply, Fin.sum_univ_two]
    simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one, one_smul, neg_smul, hΘ₀, OModulePresheaf.res_res]
    exact add_neg_cancel _
  refine ⟨LinearMap.codRestrict (T.H0 K) Θ₀ hcoc, fun F s i => ?_⟩
  rw [LinearMap.codRestrict_apply, hΘ₀]
  show (ProjSpace.twistRes (ιk ≫ ProjSpace.π k n) ιk d (le_top : K.inter s ≤ ⊤) (θ F)).val i = _
  rw [ProjSpace.twistRes_val]
  have hF := hθ F.1 (isHomogeneous_of_mem d F) i
  rw [show (⟨F.1, (MvPolynomial.mem_homogeneousSubmodule d F.1).mpr (isHomogeneous_of_mem d F)⟩ :
      ↥(MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k d)) = F from Subtype.ext rfl] at hF
  rw [hF, ProjSpace.restrictFun_restrictFun]
  rfl

end Theta

section LinAlg

variable {k : Type u} [Field k] (K : Type u) [Field K] [Algebra k K] {V : Type u} [AddCommGroup V] [Module k V]

theorem eq_zero_of_one_tmul_eq_zero (v : V) (h : (1 : K) ⊗ₜ[k] v = 0) : v = 0 := by
  obtain ⟨ψ, hψ⟩ := LinearMap.exists_leftInverse_of_injective (Algebra.linearMap k K)
    (by rw [LinearMap.ker_eq_bot]; exact (algebraMap k K).injective)
  have h1 : TensorProduct.lid k V (TensorProduct.map ψ LinearMap.id ((1 : K) ⊗ₜ[k] v)) = v := by
    rw [TensorProduct.map_tmul, LinearMap.id_apply, TensorProduct.lid_tmul]
    have : ψ 1 = 1 := by
      have := LinearMap.congr_fun hψ (1 : k)
      simpa using this
    rw [this, one_smul]
  rw [← h1, h, map_zero, map_zero]

theorem mem_of_one_tmul_mem_baseChange (W : Submodule k V) (v : V)
    (h : (1 : K) ⊗ₜ[k] v ∈ W.baseChange K) : v ∈ W := by
  refine (Submodule.Quotient.mk_eq_zero W).mp (eq_zero_of_one_tmul_eq_zero (k := k) K (Submodule.Quotient.mk v) ?_)
  have key : ∀ x ∈ W.baseChange K, (W.mkQ.baseChange K) x = 0 := by
    intro x hx
    rw [Submodule.baseChange_eq_span] at hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
        obtain ⟨w, hw, rfl⟩ := Submodule.mem_map.mp hx
        show (W.mkQ.baseChange K) ((1 : K) ⊗ₜ[k] w) = 0
        rw [LinearMap.baseChange_tmul, Submodule.mkQ_apply, (Submodule.Quotient.mk_eq_zero W).mpr hw, tmul_zero]
    | zero => exact map_zero _
    | add x y _ _ hx hy => rw [map_add, hx, hy, add_zero]
    | smul a x _ hx => rw [map_smul, hx, smul_zero]
  have := key _ h
  rw [LinearMap.baseChange_tmul] at this
  exact this

end LinAlg

end RM6Sol

theorem solution
    {k : Type u} [Field k] {n : ℕ} {Z : Scheme.{u}}
    (ι : Z ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k)) [IsAffineHom ι]
    (K : Type u) [Field K] [Algebra k K] {Z' : Scheme.{u}}
    (ι' : Z' ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) K)) [IsAffineHom ι']
    (e : Z' ⟶ Z)
    (hpb : IsPullback e (ι' ≫ ProjSpace.π K n) (ι ≫ ProjSpace.π k n) (Spec.map (CommRingCat.ofHom (algebraMap k K))))
    (hcomp : e ≫ ι = ι' ≫ ProjSpace.map k K n) (d : ℕ)
    (hK : ∀ c ∈ (ProjSpace.twist (ι' ≫ ProjSpace.π K n) ι' d).H0 (ProjSpace.stdCoverPullback ι'),
        ∃ (F : MvPolynomial (Fin (n + 1)) K) (hF : F.IsHomogeneous d),
          ∀ (s : (ProjSpace.stdCoverPullback ι').Idx 0) (i : Fin (n + 1)),
            (c s).val i =
              ProjSpace.restrictFun
                  (inf_le_right : (ProjSpace.stdCoverPullback ι').inter s ⊓ ProjSpace.pullbackChart ι' i ≤
                    ProjSpace.pullbackChart ι' i)
                  (ι'.app (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) K) (MvPolynomial.X i))
              (Proj.awayToSection (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) K) (MvPolynomial.X i)
                (HomogeneousLocalization.mk
                  { deg := d
                    num := ⟨F, (MvPolynomial.mem_homogeneousSubmodule d F).mpr hF⟩
                    den := ⟨MvPolynomial.X i ^ d, (MvPolynomial.mem_homogeneousSubmodule d _).mpr
                      (MvPolynomial.isHomogeneous_X_pow i d)⟩
                    den_mem := ⟨d, rfl⟩ })))) :
    ∀ c ∈ (ProjSpace.twist (ι ≫ ProjSpace.π k n) ι d).H0 (ProjSpace.stdCoverPullback ι),
        ∃ (F : MvPolynomial (Fin (n + 1)) k) (hF : F.IsHomogeneous d),
          ∀ (s : (ProjSpace.stdCoverPullback ι).Idx 0) (i : Fin (n + 1)),
            (c s).val i =
              ProjSpace.restrictFun
                  (inf_le_right : (ProjSpace.stdCoverPullback ι).inter s ⊓ ProjSpace.pullbackChart ι i ≤
                    ProjSpace.pullbackChart ι i)
                  (ι.app (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k) (MvPolynomial.X i))
              (Proj.awayToSection (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k) (MvPolynomial.X i)
                (HomogeneousLocalization.mk
                  { deg := d
                    num := ⟨F, (MvPolynomial.mem_homogeneousSubmodule d F).mpr hF⟩
                    den := ⟨MvPolynomial.X i ^ d, (MvPolynomial.mem_homogeneousSubmodule d _).mpr
                      (MvPolynomial.isHomogeneous_X_pow i d)⟩
                    den_mem := ⟨d, rfl⟩ }))) := by
  classical
  intro c hc
  obtain ⟨ε, hεd, hεval⟩ :=
    ProjSpace.exists_linearEquiv_baseChange_cochain_twist_of_isPullback ι K ι' e hpb hcomp d
  obtain ⟨Θ, hΘ⟩ := RM6Sol.exists_theta ι d
  obtain ⟨Θ', hΘ'⟩ := RM6Sol.exists_theta ι' d

  have hle : ∀ (s : (ProjSpace.stdCoverPullback ι).Idx 0) (j : Fin (n + 1)),
      (ProjSpace.stdCoverPullback ι').inter s ⊓ ProjSpace.pullbackChart ι' j ≤
        e ⁻¹ᵁ ((ProjSpace.stdCoverPullback ι).inter s ⊓ ProjSpace.pullbackChart ι j) := by
    intro s j
    rw [← RM6Sol.preimage_inter ι K ι' e hcomp s, ← RM6Sol.preimage_pullbackChart ι K ι' e hcomp j]
    exact le_rfl
  have hle' : ∀ (s : (ProjSpace.stdCoverPullback ι).Idx 0) (j : Fin (n + 1)),
      (ProjSpace.stdCoverPullback ι').inter s ⊓ ProjSpace.pullbackChart ι' j ≤ e ⁻¹ᵁ ProjSpace.pullbackChart ι j := by
    intro s j
    rw [RM6Sol.preimage_pullbackChart ι K ι' e hcomp j]
    exact inf_le_right

  have hmapmem : ∀ F : ↥(MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k d),
      MvPolynomial.map (algebraMap k K) (F : MvPolynomial (Fin (n + 1)) k) ∈
        MvPolynomial.homogeneousSubmodule (Fin (n + 1)) K d :=
    fun F => (MvPolynomial.mem_homogeneousSubmodule d _).mpr ((RM6Sol.isHomogeneous_of_mem d F).map _)

  have hnat : ∀ F : ↥(MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k d),
      ε 0 ((1 : K) ⊗ₜ[k] ((Θ F : ↥((ProjSpace.twist (ι ≫ ProjSpace.π k n) ι d).H0 (ProjSpace.stdCoverPullback ι))) :
          (ProjSpace.twist (ι ≫ ProjSpace.π k n) ι d).cochain (ProjSpace.stdCoverPullback ι) 0)) =
        ((Θ' ⟨_, hmapmem F⟩ : ↥((ProjSpace.twist (ι' ≫ ProjSpace.π K n) ι' d).H0 (ProjSpace.stdCoverPullback ι'))) :
          (ProjSpace.twist (ι' ≫ ProjSpace.π K n) ι' d).cochain (ProjSpace.stdCoverPullback ι') 0) := by
    intro F
    funext s
    refine ProjSpace.twistObj.ext (funext fun j => ?_)
    rw [hεval 0 _ s j (hle s j), hΘ F s j, hΘ' _ s j]
    unfold RM6Sol.chartVal
    refine (RM6Sol.restrictFun_app_eq e _ (hle s j) (hle' s j) _).trans ?_
    refine (RM6Sol.restrictFun_app_pullAway ι K ι' e hcomp j _ (hle' s j) inf_le_right).trans ?_
    rw [RM6Sol.toB_mkDeg K j d F.1 (RM6Sol.isHomogeneous_of_mem d F)]

  have hc' : ε 0 ((1 : K) ⊗ₜ[k] c) ∈
      (ProjSpace.twist (ι' ≫ ProjSpace.π K n) ι' d).H0 (ProjSpace.stdCoverPullback ι') := by
    rw [LinearMap.mem_ker]
    have h1 := LinearMap.congr_fun (hεd 0) ((1 : K) ⊗ₜ[k] c)
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearMap.baseChange_tmul] at h1
    rw [← h1, LinearMap.mem_ker.mp hc, tmul_zero, map_zero]
  obtain ⟨G, hG, hGform⟩ := hK _ hc'
  have hGmem : G ∈ MvPolynomial.homogeneousSubmodule (Fin (n + 1)) K d := (MvPolynomial.mem_homogeneousSubmodule d G).mpr hG

  have hcG : ε 0 ((1 : K) ⊗ₜ[k] c) =
      ((Θ' ⟨G, hGmem⟩ : ↥((ProjSpace.twist (ι' ≫ ProjSpace.π K n) ι' d).H0 (ProjSpace.stdCoverPullback ι'))) :
        (ProjSpace.twist (ι' ≫ ProjSpace.π K n) ι' d).cochain (ProjSpace.stdCoverPullback ι') 0) := by
    funext s
    refine ProjSpace.twistObj.ext (funext fun j => ?_)
    rw [hGform s j, hΘ' _ s j]
    rfl

  let W : Submodule k ((ProjSpace.twist (ι ≫ ProjSpace.π k n) ι d).cochain (ProjSpace.stdCoverPullback ι) 0) :=
    LinearMap.range (((ProjSpace.twist (ι ≫ ProjSpace.π k n) ι d).H0 (ProjSpace.stdCoverPullback ι)).subtype ∘ₗ Θ)
  have hmon : ∀ μ ∈ G.support, (MvPolynomial.monomial μ (1 : k)) ∈ MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k d := by
    intro μ hμ
    rw [MvPolynomial.mem_homogeneousSubmodule]
    have hdeg : μ.degree = d := by
      rw [Finsupp.degree_eq_weight_one]; exact hG (MvPolynomial.mem_support_iff.mp hμ)
    exact MvPolynomial.isHomogeneous_monomial _ hdeg

  have hGsum : (⟨G, hGmem⟩ : ↥(MvPolynomial.homogeneousSubmodule (Fin (n + 1)) K d)) =
      ∑ μ ∈ G.support.attach, G.coeff μ.1 • ⟨MvPolynomial.map (algebraMap k K) (MvPolynomial.monomial μ.1 (1 : k)),
        hmapmem ⟨_, hmon μ.1 μ.2⟩⟩ := by
    apply Subtype.ext
    rw [Submodule.coe_sum]
    simp only [Submodule.coe_smul, MvPolynomial.map_monomial, map_one]
    conv_lhs => rw [G.as_sum]
    rw [← Finset.sum_attach]
    refine Finset.sum_congr rfl fun μ _ => ?_
    rw [MvPolynomial.smul_monomial, smul_eq_mul, mul_one]

  let M : Submodule K ((ProjSpace.twist (ι' ≫ ProjSpace.π K n) ι' d).cochain (ProjSpace.stdCoverPullback ι') 0) :=
    (W.baseChange K).map (ε 0).toLinearMap
  have hspan' : Θ' ⟨G, hGmem⟩ ∈
      M.comap ((ProjSpace.twist (ι' ≫ ProjSpace.π K n) ι' d).H0 (ProjSpace.stdCoverPullback ι')).subtype := by
    rw [hGsum, map_sum]
    refine Submodule.sum_mem _ fun μ _ => ?_
    rw [map_smul]
    refine Submodule.smul_mem _ _ ?_
    rw [Submodule.mem_comap, Submodule.subtype_apply, ← hnat ⟨_, hmon μ.1 μ.2⟩]
    exact Submodule.mem_map_of_mem (Submodule.tmul_mem_baseChange_of_mem 1
      (LinearMap.mem_range.mpr ⟨⟨_, hmon μ.1 μ.2⟩, rfl⟩))
  have hspan : ((Θ' ⟨G, hGmem⟩ : ↥((ProjSpace.twist (ι' ≫ ProjSpace.π K n) ι' d).H0 (ProjSpace.stdCoverPullback ι'))) :
        (ProjSpace.twist (ι' ≫ ProjSpace.π K n) ι' d).cochain (ProjSpace.stdCoverPullback ι') 0) ∈
      (W.baseChange K).map (ε 0).toLinearMap := hspan'

  have h1c : (1 : K) ⊗ₜ[k] c ∈ W.baseChange K := by
    obtain ⟨y, hy, hyeq⟩ := Submodule.mem_map.mp hspan
    have : y = (1 : K) ⊗ₜ[k] c := (ε 0).injective (hyeq.trans hcG.symm)
    rw [← this]; exact hy
  have hcW : c ∈ W := RM6Sol.mem_of_one_tmul_mem_baseChange K W c h1c
  obtain ⟨F, hF⟩ := LinearMap.mem_range.mp hcW
  refine ⟨F.1, RM6Sol.isHomogeneous_of_mem d F, fun s i => ?_⟩
  have := hΘ F s i
  rw [show ((Θ F : ↥((ProjSpace.twist (ι ≫ ProjSpace.π k n) ι d).H0 (ProjSpace.stdCoverPullback ι))) :
      (ProjSpace.twist (ι ≫ ProjSpace.π k n) ι d).cochain (ProjSpace.stdCoverPullback ι) 0) = c from hF] at this
  exact this

end S_AlgebraicGeometry_ProjSpace_forall_H0_twist_exists_isHomogeneous_of_baseChange_field
end P2MW
export P2MW.S_AlgebraicGeometry_ProjSpace_forall_H0_twist_exists_isHomogeneous_of_baseChange_field (solution)
