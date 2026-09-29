-- Prove2me | solution 1 for AlgebraicCurve.RegularProlongation.coeff_mem_of_sum_aeval_mul_mem_of_unique_pi_residue_repr
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/ebaea7e9-8f28-5a9b-85f2-efc7d808b023

import Mathlib
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_RegularProlongation_coeff_mem_of_sum_aeval_mul_mem_of_unique_pi_residue_repr

set_option autoImplicit false
set_option maxHeartbeats 12800000

open AlgebraicCurve IsLocalRing Polynomial

theorem solution
    {L : Type*} [Field L] (A : ValuationSubring L)
    {F : Type*} [Field F] [Algebra L F]
    {ι : Type*} [Fintype ι] [Nonempty ι] (Fb : ι → Type*) [∀ i, Field (Fb i)]
    [∀ i, Algebra (IsLocalRing.ResidueField A) (Fb i)]
    (R : ∀ i, RegularProlongation A F (Fb i))
    (f : F) (hf : ∀ i, f ∈ (R i).integers)
    (d : ℕ) (z : Fin d → F) (hzO : ∀ τ i, z τ ∈ (R i).integers)
    (huniqres : ∀ q q' : Fin d → Polynomial (IsLocalRing.ResidueField A),
      (∀ i, ∑ τ, Polynomial.aeval ((R i).residue ⟨f, hf i⟩) (q τ)
          * (R i).residue ⟨z τ, hzO τ i⟩
        = ∑ τ, Polynomial.aeval ((R i).residue ⟨f, hf i⟩) (q' τ)
          * (R i).residue ⟨z τ, hzO τ i⟩) →
      q = q')
    (r : Fin d → Polynomial L)
    (hsum : ∀ i, ∑ τ, Polynomial.aeval f (r τ) * z τ ∈ (R i).integers) :
    ∀ τ j, (r τ).coeff j ∈ A := by
  classical
  by_contra hcon
  push_neg at hcon
  obtain ⟨τ₁, j₁, hτj₁⟩ := hcon

  set S : Finset (Σ _ : Fin d, ℕ) := Finset.univ.sigma fun τ => (r τ).support with hSdef
  have hS_mem : ∀ τ j, (⟨τ, j⟩ : Σ _ : Fin d, ℕ) ∈ S ↔ (r τ).coeff j ≠ 0 := fun τ j => by
    simp only [hSdef, Finset.mem_sigma, Finset.mem_univ, true_and, mem_support_iff]
  have hτj₁ne : (r τ₁).coeff j₁ ≠ 0 := fun h => hτj₁ (h ▸ A.zero_mem)
  have hSne : S.Nonempty := ⟨⟨τ₁, j₁⟩, (hS_mem τ₁ j₁).mpr hτj₁ne⟩

  obtain ⟨s₀, hs₀S, hs₀max⟩ :=
    S.exists_max_image (fun s => A.valuation ((r s.1).coeff s.2)) hSne
  set c₀ : L := (r s₀.1).coeff s₀.2 with hc₀def
  have hc₀ne : c₀ ≠ 0 := (hS_mem s₀.1 s₀.2).mp (by simpa using hs₀S)

  have hscale : ∀ τ j, (r τ).coeff j * c₀⁻¹ ∈ A := by
    intro τ j
    by_cases hj : (r τ).coeff j = 0
    · simp [hj, A.zero_mem]
    · have hle := hs₀max ⟨τ, j⟩ ((hS_mem τ j).mpr hj)
      simp only at hle

      have hvc₀ : A.valuation c₀ ≠ 0 := by
        simp only [ne_eq, map_eq_zero]; exact hc₀ne
      rw [← A.valuation_le_one_iff, map_mul, map_inv₀]
      calc A.valuation ((r τ).coeff j) * (A.valuation c₀)⁻¹
          ≤ A.valuation c₀ * (A.valuation c₀)⁻¹ := by gcongr
        _ = 1 := mul_inv_cancel₀ hvc₀

  have hc₀notA : c₀ ∉ A := by
    intro hA
    exact hτj₁ (by
      have h := mul_mem (hscale τ₁ j₁) hA
      rwa [inv_mul_cancel_right₀ hc₀ne] at h)
  have hc₀invA : c₀⁻¹ ∈ A := (A.mem_or_inv_mem c₀).resolve_left hc₀notA
  have hc₀invM : (⟨c₀⁻¹, hc₀invA⟩ : A) ∈ maximalIdeal A := by
    rw [mem_maximalIdeal, mem_nonunits_iff, isUnit_iff_exists_inv]
    push_neg
    intro b hb
    refine absurd ?_ hc₀notA
    have hbL : c₀⁻¹ * (b : L) = 1 := by exact_mod_cast congrArg A.subtype hb
    have hcb : c₀ = (b : L) := (inv_mul_eq_one₀ hc₀ne).mp hbL
    exact hcb ▸ b.2

  have hpscale : ∀ τ j, (C c₀⁻¹ * r τ).coeff j ∈ A := by
    intro τ j; rw [coeff_C_mul, mul_comm]; exact hscale τ j

  set p : Fin d → Polynomial A := fun τ =>
    ∑ j ∈ (C c₀⁻¹ * r τ).support, C (⟨(C c₀⁻¹ * r τ).coeff j, hpscale τ j⟩ : A) * X ^ j
    with hpdef
  have hpmap : ∀ τ, (p τ).map A.subtype = C c₀⁻¹ * r τ := by
    intro τ
    rw [hpdef]
    simp only [Polynomial.map_sum, Polynomial.map_mul, Polynomial.map_pow, map_C, map_X,
      ValuationSubring.coe_subtype]
    exact ((C c₀⁻¹ * r τ).as_sum_support_C_mul_X_pow).symm

  set u' : F := algebraMap L F c₀⁻¹ * ∑ τ, aeval f (r τ) * z τ with hu'def

  have hu'eq : u' = ∑ τ, aeval f ((p τ).map A.subtype) * z τ := by
    simp only [hpmap, hu'def, Finset.mul_sum]
    refine Finset.sum_congr rfl fun τ _ => ?_
    rw [map_mul, aeval_C, ← mul_assoc]

  have hc₀invO : ∀ i, algebraMap L F c₀⁻¹ ∈ (R i).integers :=
    fun i => ((R i).algebraMap_mem_iff c₀⁻¹).mpr hc₀invA
  have hu'O : ∀ i, u' ∈ (R i).integers := fun i =>
    hu'def ▸ mul_mem (hc₀invO i) (hsum i)
  have hu'res0 : ∀ i, (R i).residue ⟨u', hu'O i⟩ = 0 := by
    intro i
    have hlift : (⟨u', hu'O i⟩ : (R i).integers)
        = ⟨algebraMap L F c₀⁻¹, hc₀invO i⟩ * ⟨_, hsum i⟩ := Subtype.ext hu'def
    rw [hlift, map_mul, (R i).residue_algebraMap ⟨c₀⁻¹, hc₀invA⟩]
    have hres0 : IsLocalRing.residue A ⟨c₀⁻¹, hc₀invA⟩ = 0 :=
      (Ideal.Quotient.eq_zero_iff_mem).mpr hc₀invM
    rw [hres0, map_zero, zero_mul]

  set pbar : Fin d → Polynomial (ResidueField A) :=
    fun τ => (p τ).map (IsLocalRing.residue A) with hpbar

  have hφ : ∀ i, ∃ φ : A →+* (R i).integers,
      (R i).integers.subtype.comp φ = (algebraMap L F).comp A.subtype ∧
      (R i).residue.comp φ =
        (algebraMap (ResidueField A) (Fb i)).comp (IsLocalRing.residue A) := by
    intro i
    refine ⟨{ toFun := fun a => ⟨algebraMap L F a, ((R i).algebraMap_mem_iff a).mpr a.2⟩
              map_one' := Subtype.ext (map_one _)
              map_mul' := fun _ _ => Subtype.ext (map_mul _ _ _)
              map_zero' := Subtype.ext (map_zero _)
              map_add' := fun _ _ => Subtype.ext (map_add _ _ _) }, ?_, ?_⟩
    · exact RingHom.ext fun _ => rfl
    · exact RingHom.ext fun a => (R i).residue_algebraMap a
  have hterm : ∀ i τ, ∃ t : (R i).integers,
      (t : F) = aeval f ((p τ).map A.subtype) ∧
      (R i).residue t = aeval ((R i).residue ⟨f, hf i⟩) (pbar τ) := by
    intro i τ
    obtain ⟨φ, hsub, hres'⟩ := hφ i
    refine ⟨Polynomial.eval₂ φ ⟨f, hf i⟩ (p τ), ?_, ?_⟩
    · calc ((Polynomial.eval₂ φ ⟨f, hf i⟩ (p τ) : (R i).integers) : F)
          = Polynomial.eval₂ ((R i).integers.subtype.comp φ) f (p τ) :=
            Polynomial.hom_eval₂ (p τ) φ (R i).integers.subtype ⟨f, hf i⟩
        _ = Polynomial.eval₂ ((algebraMap L F).comp A.subtype) f (p τ) := by rw [hsub]
        _ = Polynomial.eval₂ (algebraMap L F) f ((p τ).map A.subtype) :=
            (Polynomial.eval₂_map A.subtype (algebraMap L F) f).symm
        _ = aeval f ((p τ).map A.subtype) := by rw [aeval_def]
    · calc (R i).residue (Polynomial.eval₂ φ ⟨f, hf i⟩ (p τ))
          = Polynomial.eval₂ ((R i).residue.comp φ) ((R i).residue ⟨f, hf i⟩) (p τ) :=
            Polynomial.hom_eval₂ (p τ) φ (R i).residue ⟨f, hf i⟩
        _ = Polynomial.eval₂ ((algebraMap (ResidueField A) (Fb i)).comp
              (IsLocalRing.residue A)) ((R i).residue ⟨f, hf i⟩) (p τ) := by rw [hres']
        _ = Polynomial.eval₂ (algebraMap (ResidueField A) (Fb i))
              ((R i).residue ⟨f, hf i⟩) ((p τ).map (IsLocalRing.residue A)) :=
            (Polynomial.eval₂_map (IsLocalRing.residue A)
              (algebraMap (ResidueField A) (Fb i)) ((R i).residue ⟨f, hf i⟩)).symm
        _ = aeval ((R i).residue ⟨f, hf i⟩) (pbar τ) := by rw [aeval_def, hpbar]
  have hu'red : ∀ i, (R i).residue ⟨u', hu'O i⟩
      = ∑ τ, aeval ((R i).residue ⟨f, hf i⟩) (pbar τ) * (R i).residue ⟨z τ, hzO τ i⟩ := by
    intro i
    choose t ht htres using hterm i
    have hlift : (⟨u', hu'O i⟩ : (R i).integers) = ∑ τ, t τ * ⟨z τ, hzO τ i⟩ := by
      refine Subtype.ext ?_; push_cast; simp only [ht]; exact hu'eq
    calc (R i).residue ⟨u', hu'O i⟩ = (R i).residue (∑ τ, t τ * ⟨z τ, hzO τ i⟩) := by rw [hlift]
      _ = ∑ τ, (R i).residue (t τ) * (R i).residue ⟨z τ, hzO τ i⟩ := by
          simp only [map_sum, map_mul]
      _ = ∑ τ, aeval ((R i).residue ⟨f, hf i⟩) (pbar τ) * (R i).residue ⟨z τ, hzO τ i⟩ := by
          simp only [htres]

  have hpbar0 : pbar = 0 := by
    apply huniqres pbar 0
    intro i
    simp only [Pi.zero_apply, map_zero, zero_mul, Finset.sum_const_zero]
    rw [← hu'red i, hu'res0 i]

  have hcontra : (pbar s₀.1).coeff s₀.2 = 1 := by
    rw [hpbar, coeff_map]

    have h1 : A.subtype ((p s₀.1).coeff s₀.2) = 1 := by
      rw [← coeff_map, hpmap, coeff_C_mul, ← hc₀def, inv_mul_cancel₀ hc₀ne]
    have h2 : (p s₀.1).coeff s₀.2 = 1 :=
      A.subtype_injective (h1.trans (map_one A.subtype).symm)
    rw [h2, map_one]
  rw [hpbar0] at hcontra
  exact one_ne_zero hcontra.symm

end S_AlgebraicCurve_RegularProlongation_coeff_mem_of_sum_aeval_mul_mem_of_unique_pi_residue_repr
end P2MW
export P2MW.S_AlgebraicCurve_RegularProlongation_coeff_mem_of_sum_aeval_mul_mem_of_unique_pi_residue_repr (solution)
