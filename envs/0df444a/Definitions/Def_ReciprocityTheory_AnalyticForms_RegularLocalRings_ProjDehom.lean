-- Prove2me | Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ProjDehom
-- name    : ReciprocityTheory_AnalyticForms_RegularLocalRings_ProjDehom
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-25T12:58:57.399978+00:00
-- url     : https://prove2.me/theorems/83ca17c0-0b60-4edc-970c-800c9a8ef2b8
-- title:
--   Proj Dehom
-- statement:
--   Definitions and structural lemmas for Proj Dehom, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/ProjDehom.lean

import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_SegreIdealIsHomogeneous
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_FromSpecResidueFieldAppTopIso
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ProjDehomA
import Theorems.Thm_P2M_ReciprocityTheory_AnForm_R_eval__mk_one_83d5260a9710
import Theorems.Thm_P2M_ReciprocityTheory_AnForm_R_eval__mul_const_of_isHomogeneous_b3d59a203a6a
import Theorems.Thm_ReciprocityTheory_AnForm_R_isHomogeneous_of_isMultiHomog
import Theorems.Thm_ReciprocityTheory_AnForm_R_mk_one_mul_invW
import Theorems.Thm_ReciprocityTheory_AnForm_R_mk_pow_eq_mul_invW
import Theorems.Thm_ReciprocityTheory_AnForm_R_mul_pow_inv_eq
import Theorems.Thm_ReciprocityTheory_AnForm_R_prod_update_eq
import Theorems.Thm_ReciprocityTheory_AnForm_R_segreGrading_algebraMap_surjective
import Theorems.Thm_ReciprocityTheory_AnForm_R_segreMap_X
import Theorems.Thm_ReciprocityTheory_AnForm_R_segreMap_aeval_update
import Theorems.Thm_ReciprocityTheory_AnForm_R_segreRing_finiteType
import Theorems.Thm_ReciprocityTheory_AnForm_R_segreW_prod_update

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.AnForm.R
open MvPolynomial AlgebraicGeometry CategoryTheory
noncomputable section
variable {K : Type} [Fintype K] [Nonempty K] {ι : K → Type} [∀ k, Fintype (ι k)]
theorem segreW_mem_one_smul (P : Ideal (MvPolynomial (Σ k, ι k) ℂ)) (p : (k : K) → ι k) :
    segreW P p ∈ segreGrading P (1 • 1) := by
  simpa using segreW_mem P p
def toSpecC {P : Ideal (MvPolynomial (Σ k, ι k) ℂ)} (hP : IsMultiHomogIdeal P) :
    projX P hP ⟶ Spec (CommRingCat.of ℂ) :=
  letI := segreGraded hP
  Proj.toSpecZero (segreGrading P) ≫ Spec.map (CommRingCat.ofHom (algebraMap ℂ (segreGrading P 0)))
instance locallyOfFiniteType_toSpecC {P : Ideal (MvPolynomial (Σ k, ι k) ℂ)} (hP : IsMultiHomogIdeal P) :
    LocallyOfFiniteType (toSpecC hP) := by
  classical
  letI := segreGraded hP
  have hsurj := segreGrading_algebraMap_surjective hP
  haveI := segreRing_finiteType hP
  have h2 : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap ℂ (segreGrading P 0)))) := by
    rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
    exact RingHom.FiniteType.of_surjective _ hsurj
  have h1 : LocallyOfFiniteType (Proj.toSpecZero (segreGrading P)) := inferInstance
  exact @locallyOfFiniteType_comp _ _ _ (Proj.toSpecZero (segreGrading P)) _ h1 h2
open Classical in

def chartUpd (p : (k : K) → ι k) (q : Σ k, ι k) : (k : K) → ι k :=
  Function.update p q.1 q.2
def awayCoord {P : Ideal (MvPolynomial (Σ k, ι k) ℂ)} (hP : IsMultiHomogIdeal P) (p : (k : K) → ι k)
    (q : Σ k, ι k) :
    letI := segreGraded hP
    HomogeneousLocalization.Away (segreGrading P) (segreW P p) :=
  letI := segreGraded hP
  HomogeneousLocalization.Away.mk (segreGrading P) (segreW_mem P p) 1 (segreW P (chartUpd p q))
    (segreW_mem_one_smul P (chartUpd p q))
def polyToAway {P : Ideal (MvPolynomial (Σ k, ι k) ℂ)} (hP : IsMultiHomogIdeal P) (p : (k : K) → ι k) :
    letI := segreGraded hP
    MvPolynomial (Σ k, ι k) ℂ →+* HomogeneousLocalization.Away (segreGrading P) (segreW P p) :=
  letI := segreGraded hP
  eval₂Hom ((algebraMap (segreGrading P 0) _).comp (algebraMap ℂ (segreGrading P 0))) (awayCoord hP p)
theorem val_polyToAway {P : Ideal (MvPolynomial (Σ k, ι k) ℂ)} (hP : IsMultiHomogIdeal P)
    (p : (k : K) → ι k) (f : MvPolynomial (Σ k, ι k) ℂ) :
    letI := segreGraded hP
    (polyToAway hP p f).val = eval₂ (algebraMap ℂ (Localization.Away (segreW P p)))
      (fun q => Localization.mk (segreW P (chartUpd p q)) 1 * invW P p) f := by
  letI := segreGraded hP
  induction f using MvPolynomial.induction_on with
  | C c =>
    simp only [polyToAway, coe_eval₂Hom, eval₂_C, RingHom.coe_comp, Function.comp_apply]
    rw [HomogeneousLocalization.algebraMap_eq]
    rw [IsScalarTower.algebraMap_apply ℂ (MvPolynomial ((k : K) → ι k) ℂ ⧸ segreIdeal P)
      (Localization.Away (segreW P p)), ← Localization.mk_one_eq_algebraMap]
    rfl
  | add f g hf hg =>
    simp only [map_add, HomogeneousLocalization.val_add, hf, hg, eval₂_add]
  | mul_X f q hf =>
    rw [map_mul, HomogeneousLocalization.val_mul, hf, eval₂_mul, eval₂_X]
    congr 1
    simp only [polyToAway, coe_eval₂Hom, eval₂_X, awayCoord, HomogeneousLocalization.Away.val_mk]
    rw [mk_pow_eq_mul_invW, pow_one]
theorem chartIdeal_le_ker_polyToAway {P : Ideal (MvPolynomial (Σ k, ι k) ℂ)} (hP : IsMultiHomogIdeal P)
    (p : (k : K) → ι k) :
    letI := segreGraded hP
    chartIdeal P p ≤ RingHom.ker (polyToAway hP p) := by
  classical
  letI := segreGraded hP
  refine sup_le ?_ ?_
  · obtain ⟨S, hS, hPS⟩ := id hP
    refine hPS.le.trans (Ideal.span_le.mpr fun s hs => ?_)
    obtain ⟨a, ha⟩ := hS s hs
    have hsP : s ∈ P := hPS ▸ Ideal.subset_span hs
    show polyToAway hP p s = 0
    apply HomogeneousLocalization.val_injective
    rw [val_polyToAway, HomogeneousLocalization.val_zero,
      eval₂_mul_const_of_isHomogeneous _ _ _ (isHomogeneous_of_isMultiHomog ha)]
    have hmem : aeval (fun q => (X (chartUpd p q) : MvPolynomial ((k : K) → ι k) ℂ)) s ∈ segreIdeal P := by
      show segreMap _ ∈ P
      simp only [chartUpd]
      rw [segreMap_aeval_update p ha]
      exact Ideal.mul_mem_left _ _ hsP
    rw [eval₂_mk_one (segreIdeal P) _ (fun q => (X (chartUpd p q) : MvPolynomial ((k : K) → ι k) ℂ)),
      Ideal.Quotient.eq_zero_iff_mem.mpr hmem, Localization.mk_zero, zero_mul]
  · rw [Ideal.span_le]
    rintro _ ⟨k, rfl⟩
    show polyToAway hP p _ = 0
    apply HomogeneousLocalization.val_injective
    have hu : chartUpd p ⟨k, p k⟩ = p := by simp [chartUpd]
    rw [val_polyToAway, HomogeneousLocalization.val_zero, eval₂_sub, eval₂_X, eval₂_one, hu,
      mk_one_mul_invW, sub_self]
def chartToAway {P : Ideal (MvPolynomial (Σ k, ι k) ℂ)} (hP : IsMultiHomogIdeal P) (p : (k : K) → ι k) :
    letI := segreGraded hP
    chartRing P p →+* HomogeneousLocalization.Away (segreGrading P) (segreW P p) :=
  letI := segreGraded hP
  Ideal.Quotient.lift _ (polyToAway hP p) (chartIdeal_le_ker_polyToAway hP p)
theorem chartToAway_mk {P : Ideal (MvPolynomial (Σ k, ι k) ℂ)} (hP : IsMultiHomogIdeal P)
    (p : (k : K) → ι k) (f : MvPolynomial (Σ k, ι k) ℂ) :
    chartToAway hP p (Ideal.Quotient.mk _ f) = polyToAway hP p f :=
  rfl
theorem chartToAway_bijective {P : Ideal (MvPolynomial (Σ k, ι k) ℂ)} (hP : IsMultiHomogIdeal P)
    (p : (k : K) → ι k) :
    letI := segreGraded hP
    Function.Bijective (chartToAway hP p) := by
  classical
  letI := segreGraded hP
  have hX1 : ∀ k, Ideal.Quotient.mk (chartIdeal P p) (X ⟨k, p k⟩) = 1 := fun k => by
    rw [← map_one (Ideal.Quotient.mk (chartIdeal P p)), Ideal.Quotient.eq]
    exact Ideal.mem_sup_right (Ideal.subset_span ⟨k, rfl⟩)
  let ψA : (MvPolynomial ((k : K) → ι k) ℂ ⧸ segreIdeal P) →+* chartRing P p :=
    Ideal.Quotient.lift _ ((Ideal.Quotient.mk (chartIdeal P p)).comp segreMap.toRingHom)
      (fun a ha => Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_sup_left ha))
  have hψA : ∀ g, ψA (Ideal.Quotient.mk _ g) = Ideal.Quotient.mk _ (segreMap g) := fun g => rfl
  have hψAW : ∀ p', ψA (segreW P p') = ∏ k, Ideal.Quotient.mk (chartIdeal P p) (X ⟨k, p' k⟩) := by
    intro p'
    rw [hψA, segreMap_X, map_prod]
  have hw : ψA (segreW P p) = 1 := by
    rw [hψAW]
    exact Finset.prod_eq_one fun k _ => hX1 k
  have hu : IsUnit (ψA (segreW P p)) := hw ▸ isUnit_one
  let ψL : Localization.Away (segreW P p) →+* chartRing P p := IsLocalization.Away.lift (segreW P p) hu
  have hψL : ∀ a (s : Submonoid.powers (segreW P p)), ψL (Localization.mk a s) = ψA a := by
    intro a s
    have hs : ψA (s : MvPolynomial ((k : K) → ι k) ℂ ⧸ segreIdeal P) = 1 := by
      obtain ⟨_, n, rfl⟩ := s
      rw [map_pow, hw, one_pow]
    calc ψL (Localization.mk a s)
        = ψL (Localization.mk a s) * ψA (s : MvPolynomial ((k : K) → ι k) ℂ ⧸ segreIdeal P) := by
          rw [hs, mul_one]
      _ = ψL (Localization.mk a s * algebraMap _ (Localization.Away (segreW P p))
            (s : MvPolynomial ((k : K) → ι k) ℂ ⧸ segreIdeal P)) := by
          rw [map_mul, IsLocalization.Away.lift_eq]
      _ = ψL (algebraMap _ (Localization.Away (segreW P p)) a) := by
          congr 1
          rw [Localization.mk_eq_mk']
          exact IsLocalization.mk'_spec _ a s
      _ = ψA a := IsLocalization.Away.lift_eq _ _ _
  let ψ : HomogeneousLocalization.Away (segreGrading P) (segreW P p) →+* chartRing P p :=
    ψL.comp (algebraMap _ (Localization.Away (segreW P p)))
  have hψ : ∀ z, ψ z = ψL z.val := fun z => rfl
  have hleft : ∀ x, ψ (chartToAway hP p x) = x := by
    have h : ψ.comp (chartToAway hP p) = RingHom.id _ := by
      apply Ideal.Quotient.ringHom_ext
      apply MvPolynomial.ringHom_ext
      · intro c
        simp only [RingHom.comp_apply, RingHom.id_apply, chartToAway_mk, hψ,
          val_polyToAway, eval₂_C]
        rw [IsScalarTower.algebraMap_apply ℂ (MvPolynomial ((k : K) → ι k) ℂ ⧸ segreIdeal P),
          IsLocalization.Away.lift_eq]
        show Ideal.Quotient.mk _ (segreMap (C c)) = _
        rw [← MvPolynomial.algebraMap_eq, AlgHom.commutes]
        rfl
      · intro q
        simp only [RingHom.comp_apply, RingHom.id_apply, chartToAway_mk, hψ,
          val_polyToAway, eval₂_X, map_mul, hψL, map_one, mul_one, hψAW, chartUpd]
        rw [prod_update_eq (fun q => Ideal.Quotient.mk (chartIdeal P p) (X q)) p q.1 q.2,
          Finset.prod_eq_one fun k _ => hX1 k, mul_one]
    exact fun x => RingHom.congr_fun h x
  have hright : ∀ z, chartToAway hP p (ψ z) = z := by
    intro z
    obtain ⟨n, a, ha, rfl⟩ := HomogeneousLocalization.Away.mk_surjective (segreGrading P) (segreW_mem P p) z
    obtain ⟨h, hh, rfl⟩ := Submodule.mem_map.mp ha
    have hhom : h.IsHomogeneous n := by
      simpa [smul_eq_mul, mul_one] using (mem_homogeneousSubmodule _ h).mp hh
    apply HomogeneousLocalization.val_injective
    rw [hψ, HomogeneousLocalization.Away.val_mk, hψL]
    simp only [AlgHom.toLinearMap_apply, Ideal.Quotient.mkₐ_eq_mk]
    rw [hψA, chartToAway_mk, val_polyToAway, mk_pow_eq_mul_invW]
    have hseg : ∀ p' : (k : K) → ι k, eval₂ (algebraMap ℂ (Localization.Away (segreW P p)))
        (fun q => Localization.mk (segreW P (chartUpd p q)) 1 * invW P p)
        (segreMap (X p' : MvPolynomial ((k : K) → ι k) ℂ)) =
        Localization.mk (segreW P p') 1 * invW P p := by
      intro p'
      have E := congrArg (algebraMap (MvPolynomial ((k : K) → ι k) ℂ ⧸ segreIdeal P)
        (Localization.Away (segreW P p))) (segreW_prod_update P p p')
      simp only [map_mul, map_prod, map_pow] at E
      have ht := mk_one_mul_invW P p
      simp only [Localization.mk_one_eq_algebraMap] at ht ⊢
      rw [segreMap_X, eval₂_prod]
      simp only [eval₂_X, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ]
      exact mul_pow_inv_eq _ _ _ _ _ E ht
    have hc : (aeval (fun q => Localization.mk (segreW P (chartUpd p q)) 1 * invW P p)).comp segreMap =
        aeval (fun p' => Localization.mk (segreW P p') 1 * invW P p) :=
      MvPolynomial.algHom_ext fun p' => by
        rw [AlgHom.comp_apply, aeval_X, aeval_def]
        exact hseg p'
    have hc' := congrArg (fun φ => φ h) hc
    simp only [AlgHom.comp_apply] at hc'
    rw [← aeval_def, hc', aeval_def, eval₂_mul_const_of_isHomogeneous _ _ _ hhom]
    congr 1
    rw [eval₂_mk_one (segreIdeal P) _ X h, aeval_X_left_apply]
  exact ⟨fun x y hxy => by rw [← hleft x, ← hleft y, hxy], fun z => ⟨ψ z, hright z⟩⟩
def awayEquiv {P : Ideal (MvPolynomial (Σ k, ι k) ℂ)} (hP : IsMultiHomogIdeal P) (p : (k : K) → ι k) :
    letI := segreGraded hP
    chartRing P p ≃+* HomogeneousLocalization.Away (segreGrading P) (segreW P p) :=
  letI := segreGraded hP
  RingEquiv.ofBijective _ (chartToAway_bijective hP p)
def gammaChart {P : Ideal (MvPolynomial (Σ k, ι k) ℂ)} (hP : IsMultiHomogIdeal P) (p : (k : K) → ι k) :
    Γ(projX P hP, (chartOpen hP p).1) ≃+* chartRing P p :=
  letI := segreGraded hP
  (Proj.basicOpenIsoAway (segreGrading P) (segreW P p) (segreW_mem P p) one_pos).commRingCatIsoToRingEquiv.symm.trans
    (awayEquiv hP p).symm
def chartCoord {P : Ideal (MvPolynomial (Σ k, ι k) ℂ)} (hP : IsMultiHomogIdeal P) (p : (k : K) → ι k)
    (q : Σ k, ι k) : Γ(projX P hP, (chartOpen hP p).1) :=
  (gammaChart hP p).symm (Ideal.Quotient.mk _ (X q))
end
end ReciprocityTheory.AnForm.R


