-- Prove2me | solution 1 for AlgebraicCurve.RegularProlongation.exists_residue_trace_eq_trace_residue_of_finrank_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/132886e5-f8a1-5995-9567-30a8ae612fdb

import Mathlib
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Theorems.Thm_AlgebraicCurve_RegularProlongation_exists_gaussBasis_mem_integralClosure_piResidue_uniqueRepr_of_sum_finrank_eq
import Theorems.Thm_AlgebraicCurve_RegularProlongation_eq_integers_of_forall_mem_adjoin_iff
import Theorems.Thm_AlgebraicCurve_RegularProlongation_transcendental_of_residue_transcendental
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_RegularProlongation_exists_residue_trace_eq_trace_residue_of_finrank_eq

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000

noncomputable section

p2m_open "AlgebraicCurve P2MW.S_AlgebraicCurve_RegularProlongation_exists_residue_trace_eq_trace_residue_of_finrank_eq.AlgebraicCurve IsLocalRing Polynomial"

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "RegularProlongation RegularProlongation.exists_gaussBasis_mem_integralClosure_piResidue_uniqueRepr_of_sum_finrank_eq"
namespace TraceReductionProof
p2m_open "AlgebraicCurve"

section Gauss

variable {L : Type*} [Field L] (A : ValuationSubring L)

theorem exists_scale {ι : Type*} (s : Finset ι) (a : ι → L) (h : ∃ i ∈ s, a i ≠ 0) :
    ∃ c : L, c ≠ 0 ∧ (∀ i ∈ s, c * a i ∈ A) ∧ ∃ i ∈ s, c * a i = 1 := by
  classical
  obtain ⟨i₁, hi₁, hne⟩ := h
  set s' := s.filter fun i => a i ≠ 0 with hs'
  have hs'ne : s'.Nonempty := ⟨i₁, Finset.mem_filter.mpr ⟨hi₁, hne⟩⟩
  obtain ⟨i₀, hi₀, hmax⟩ := s'.exists_max_image (fun i => A.valuation (a i)) hs'ne
  have hi₀s : i₀ ∈ s := (Finset.mem_filter.mp hi₀).1
  have ha₀ : a i₀ ≠ 0 := (Finset.mem_filter.mp hi₀).2
  refine ⟨(a i₀)⁻¹, inv_ne_zero ha₀, fun i hi => ?_, i₀, hi₀s, inv_mul_cancel₀ ha₀⟩
  by_cases hai : a i = 0
  · rw [hai, mul_zero]; exact zero_mem _
  rw [← A.valuation_le_one_iff, map_mul, map_inv₀]
  have hle := hmax i (Finset.mem_filter.mpr ⟨hi, hai⟩)
  have hpos : A.valuation (a i₀) ≠ 0 := (_root_.map_ne_zero _).mpr ha₀
  calc (A.valuation (a i₀))⁻¹ * A.valuation (a i)
      ≤ (A.valuation (a i₀))⁻¹ * A.valuation (a i₀) := mul_le_mul_right hle _
    _ = 1 := inv_mul_cancel₀ hpos

end Gauss

section Eval

variable {L : Type*} [Field L] {A : ValuationSubring L}
variable {F : Type*} [Field F] [Algebra L F]
variable {Fbar : Type*} [Field Fbar] [Algebra (ResidueField A) Fbar]
variable (R : RegularProlongation A F Fbar)

def constToIntegers : A →+* R.integers where
  toFun a := ⟨algebraMap L F a, (R.algebraMap_mem_iff _).mpr a.2⟩
  map_one' := Subtype.ext (by simp)
  map_mul' a b := Subtype.ext (by simp)
  map_zero' := Subtype.ext (by simp)
  map_add' a b := Subtype.ext (by simp)

theorem coe_constToIntegers (a : A) :
    ((constToIntegers R a : R.integers) : F) = algebraMap L F a := rfl

theorem residue_constToIntegers (a : A) :
    R.residue (constToIntegers R a) = algebraMap (ResidueField A) Fbar (residue A a) :=
  R.residue_algebraMap a

theorem coe_eval₂_constToIntegers (P : Polynomial A) (t : R.integers) :
    ((P.eval₂ (constToIntegers R) t : R.integers) : F) = aeval (t : F) (P.map A.subtype) := by
  rw [show ((P.eval₂ (constToIntegers R) t : R.integers) : F) =
      R.integers.subtype (P.eval₂ (constToIntegers R) t) from rfl,
    Polynomial.hom_eval₂, aeval_def, eval₂_map]
  congr 1

theorem residue_eval₂_constToIntegers (P : Polynomial A) (t : R.integers) :
    R.residue (P.eval₂ (constToIntegers R) t) =
      aeval (R.residue t) (P.map (residue A)) := by
  rw [Polynomial.hom_eval₂, aeval_def, eval₂_map]
  congr 1
  exact RingHom.ext fun a => residue_constToIntegers R a

theorem exists_lift_of_coeff_mem (P : Polynomial L) (hP : ∀ i, P.coeff i ∈ A) :
    ∃ PA : Polynomial A, PA.map A.subtype = P := by
  have hlift : P ∈ Polynomial.lifts (algebraMap A L) := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    exact fun i => ⟨⟨P.coeff i, hP i⟩, rfl⟩
  exact (Polynomial.mem_lifts _).mp hlift

end Eval

section Main

variable {L : Type*} [Field L] (A : ValuationSubring L)
variable {F : Type*} [Field F] [Algebra L F]
variable {Fbar : Type*} [Field Fbar] [Algebra (ResidueField A) Fbar]
variable (R : RegularProlongation A F Fbar)
variable (x : R.integers) (hx : Transcendental (ResidueField A) (R.residue x))
variable (hfin : 0 < Module.finrank
  (IntermediateField.adjoin (ResidueField A) ({R.residue x} : Set Fbar)) Fbar)
variable (hdeg : Module.finrank (IntermediateField.adjoin L ({(x : F)} : Set F)) F =
  Module.finrank (IntermediateField.adjoin (ResidueField A) ({R.residue x} : Set Fbar)) Fbar)

local notation "κ" => ResidueField A
local notation "K₀" => IntermediateField.adjoin L ({(x : F)} : Set F)
local notation "k₀" => IntermediateField.adjoin (ResidueField A) ({R.residue x} : Set Fbar)

theorem exists_eq_aeval_div_aeval (a : F) (ha : a ∈ K₀) :
    ∃ P Q : Polynomial L, a = aeval (x : F) P / aeval (x : F) Q := by
  rw [IntermediateField.mem_adjoin_iff_div] at ha
  obtain ⟨r, hr, s, hs, rfl⟩ := ha
  rw [Algebra.adjoin_singleton_eq_range_aeval] at hr hs
  obtain ⟨P, rfl⟩ := hr
  obtain ⟨Q, rfl⟩ := hs
  exact ⟨P, Q, rfl⟩

theorem aeval_div_aeval_mem (P Q : Polynomial κ) :
    aeval (R.residue x) P / aeval (R.residue x) Q ∈ k₀ := by
  refine div_mem ?_ ?_ <;>
  · rw [IntermediateField.mem_adjoin_iff_div]
    refine ⟨_, ?_, 1, one_mem _, (div_one _).symm⟩
    rw [Algebra.adjoin_singleton_eq_range_aeval]
    exact ⟨_, rfl⟩

include hx in

theorem exists_residue_eq_of_mem_adjoin (a : F) (ha : a ∈ K₀) (haO : a ∈ R.integers) :
    ∃ e : k₀, (e : Fbar) = R.residue ⟨a, haO⟩ := by
  classical
  obtain ⟨P, Q, hPQ⟩ := exists_eq_aeval_div_aeval A R x a ha
  by_cases hQ0 : aeval (x : F) Q = 0
  · refine ⟨0, ?_⟩
    have : (⟨a, haO⟩ : R.integers) = 0 := Subtype.ext (show a = _ by rw [hPQ, hQ0, div_zero]; rfl)
    rw [this, map_zero]; rfl
  have hQne : Q ≠ 0 := by rintro rfl; exact hQ0 (map_zero _)

  obtain ⟨n₀, hn₀⟩ : ∃ n, Q.coeff n ≠ 0 := by
    by_contra h; push Not at h; exact hQne (Polynomial.ext fun n => by simpa using h n)
  let fam : Bool × ℕ → L := fun bn => if bn.1 then P.coeff bn.2 else Q.coeff bn.2
  let s : Finset (Bool × ℕ) := (Finset.univ : Finset Bool) ×ˢ (P.support ∪ Q.support)
  have hmemQ : (false, n₀) ∈ s := by
    simp only [s, Finset.mem_product, Finset.mem_univ, true_and, Finset.mem_union]
    exact Or.inr (Polynomial.mem_support_iff.mpr hn₀)
  obtain ⟨c, hc0, hcA, i₀, hi₀s, hi₀⟩ :=
    exists_scale A s fam ⟨(false, n₀), hmemQ, by simpa [fam] using hn₀⟩

  have hcoefP : ∀ i, (C c * P).coeff i ∈ A := by
    intro i
    rw [coeff_C_mul]
    by_cases hi : i ∈ P.support
    · have := hcA (true, i) (by simp [s, hi])
      simpa [fam] using this
    · rw [Polynomial.notMem_support_iff.mp hi, mul_zero]; exact zero_mem _
  have hcoefQ : ∀ i, (C c * Q).coeff i ∈ A := by
    intro i
    rw [coeff_C_mul]
    by_cases hi : i ∈ Q.support
    · have := hcA (false, i) (by simp [s, hi])
      simpa [fam] using this
    · rw [Polynomial.notMem_support_iff.mp hi, mul_zero]; exact zero_mem _
  obtain ⟨PA, hPA⟩ := exists_lift_of_coeff_mem (C c * P) hcoefP
  obtain ⟨QA, hQA⟩ := exists_lift_of_coeff_mem (C c * Q) hcoefQ

  have hunit : (∃ i, PA.coeff i = 1) ∨ ∃ i, QA.coeff i = 1 := by
    obtain ⟨b, i⟩ := i₀
    cases b
    · right; refine ⟨i, Subtype.ext ?_⟩
      have h1 : ((QA.coeff i : A) : L) = (C c * Q).coeff i := by
        rw [← hQA, coeff_map]; rfl
      rw [h1, coeff_C_mul]; simpa [fam] using hi₀
    · left; refine ⟨i, Subtype.ext ?_⟩
      have h1 : ((PA.coeff i : A) : L) = (C c * P).coeff i := by
        rw [← hPA, coeff_map]; rfl
      rw [h1, coeff_C_mul]; simpa [fam] using hi₀

  set Pr : R.integers := PA.eval₂ (constToIntegers R) x with hPr
  set Qr : R.integers := QA.eval₂ (constToIntegers R) x with hQr
  have hPF : (Pr : F) = algebraMap L F c * aeval (x : F) P := by
    rw [hPr, coe_eval₂_constToIntegers, hPA, map_mul, aeval_C]
  have hQF : (Qr : F) = algebraMap L F c * aeval (x : F) Q := by
    rw [hQr, coe_eval₂_constToIntegers, hQA, map_mul, aeval_C]
  have heq : Qr * ⟨a, haO⟩ = Pr := by
    apply Subtype.ext
    change (Qr : F) * a = Pr
    rw [hQF, hPF, hPQ, mul_assoc, mul_div_cancel₀ _ hQ0]
  have hres := congrArg R.residue heq
  rw [map_mul, hPr, hQr, residue_eval₂_constToIntegers, residue_eval₂_constToIntegers] at hres
  set Pb := PA.map (residue A) with hPb
  set Qb := QA.map (residue A) with hQb
  have hinj : Function.Injective (aeval (R := κ) (R.residue x)) := transcendental_iff_injective.mp hx
  by_cases hQb0 : Qb = 0
  ·
    exfalso
    have hP0 : aeval (R.residue x) Pb = 0 := by rw [← hres, hQb0, map_zero, zero_mul]
    have hPb0 : Pb = 0 := hinj (by rw [hP0, map_zero])
    rcases hunit with ⟨i, hi⟩ | ⟨i, hi⟩
    · have := congrArg (fun p : Polynomial κ => p.coeff i) hPb0
      simp only [hPb, coeff_map, hi, map_one, coeff_zero] at this
      exact one_ne_zero this
    · have := congrArg (fun p : Polynomial κ => p.coeff i) hQb0
      simp only [hQb, coeff_map, hi, map_one, coeff_zero] at this
      exact one_ne_zero this
  · have hQbx : aeval (R.residue x) Qb ≠ 0 := fun h => hQb0 (hinj (by rw [h, map_zero]))
    refine ⟨⟨aeval (R.residue x) Pb / aeval (R.residue x) Qb, aeval_div_aeval_mem A R x Pb Qb⟩, ?_⟩
    change aeval (R.residue x) Pb / aeval (R.residue x) Qb = R.residue ⟨a, haO⟩
    rw [← hres, mul_div_cancel_left₀ _ hQbx]

include hx hfin hdeg in

theorem exists_gaussBasis [IsAlgClosed L] :
    ∃ (d : ℕ) (z : Fin d → F) (hzO : ∀ σ, z σ ∈ R.integers),
      (∀ q q' : Fin d → Polynomial κ,
        (∑ σ, aeval (R.residue x) (q σ) * R.residue ⟨z σ, hzO σ⟩ =
          ∑ σ, aeval (R.residue x) (q' σ) * R.residue ⟨z σ, hzO σ⟩) → q = q') ∧
      (∀ b : F, b ∈ R.integers →
        ∃ c : Fin d → K₀, (∀ σ, (c σ : F) ∈ R.integers) ∧ b = ∑ σ, (c σ : F) * z σ) := by
  haveI : FiniteDimensional K₀ F := by
    apply FiniteDimensional.of_finrank_pos; rw [hdeg]; exact hfin
  have htrL : Transcendental L (x : F) := R.transcendental_of_residue_transcendental A x hx
  obtain ⟨d, z, hzO, -, huniq, hcoord⟩ :=
    RegularProlongation.exists_gaussBasis_mem_integralClosure_piResidue_uniqueRepr_of_sum_finrank_eq
      A (ι := Unit) (fun _ => Fbar) (fun _ => R) (fun _ _ _ => Subsingleton.elim _ _)
      (x : F) (fun _ => x.2) htrL ‹_› (fun _ => by simpa using hx) ()
      (fun W hW => ⟨(), R.eq_integers_of_forall_mem_adjoin_iff A x hx hfin hdeg W
        (fun e he => hW e he)⟩)
      (by simp [hdeg])
  refine ⟨d, z, fun σ => hzO σ (), fun q q' h => huniq q q' (fun _ => ?_), fun b hb => ?_⟩
  · simpa using h
  · obtain ⟨c, hcO, hb⟩ := hcoord b (fun _ => hb)
    exact ⟨c, hcO, hb⟩

theorem exists_mul_aeval_eq_aeval {K E : Type*} [Field K] [Field E] [Algebra K E] (t : E)
    (a : E) (ha : a ∈ IntermediateField.adjoin K ({t} : Set E)) :
    ∃ P Q : Polynomial K, aeval t Q ≠ 0 ∧ a * aeval t Q = aeval t P := by
  rw [IntermediateField.mem_adjoin_iff_div] at ha
  obtain ⟨r, hr, s, hs, rfl⟩ := ha
  rw [Algebra.adjoin_singleton_eq_range_aeval] at hr hs
  obtain ⟨P, rfl⟩ := hr
  obtain ⟨Q, rfl⟩ := hs
  by_cases hQ : aeval t Q = 0
  · exact ⟨0, 1, by simp, by simp [hQ]⟩
  · exact ⟨P, Q, hQ, div_mul_cancel₀ _ hQ⟩

theorem exists_polynomial_relation {K E : Type*} [Field K] [Field E] [Algebra K E] (t : E)
    {d : ℕ} (v : Fin d → E) (g : Fin d → IntermediateField.adjoin K ({t} : Set E))
    (hg : ∑ σ, (g σ : E) * v σ = 0) (σ₀ : Fin d) (hσ₀ : g σ₀ ≠ 0) :
    ∃ r : Fin d → Polynomial K, (∑ σ, aeval t (r σ) * v σ = 0) ∧ r σ₀ ≠ 0 := by
  classical
  have h := fun σ => exists_mul_aeval_eq_aeval t (g σ : E) (g σ).2
  choose P Q hQ hPQ using h
  refine ⟨fun σ => P σ * ∏ τ ∈ Finset.univ.erase σ, Q τ, ?_, ?_⟩
  · have hD : ∀ σ, aeval t (P σ * ∏ τ ∈ Finset.univ.erase σ, Q τ) =
        (g σ : E) * aeval t (∏ τ, Q τ) := by
      intro σ
      rw [map_mul, ← hPQ σ, mul_assoc, ← map_mul, Finset.mul_prod_erase _ _ (Finset.mem_univ σ)]
    simp_rw [hD]
    have : ∑ σ, (g σ : E) * aeval t (∏ τ, Q τ) * v σ = aeval t (∏ τ, Q τ) * ∑ σ, (g σ : E) * v σ := by
      rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun σ _ => by ring
    rw [this, hg, mul_zero]
  · refine mul_ne_zero ?_ (Finset.prod_ne_zero_iff.mpr fun τ _ => ?_)
    · intro hP
      apply hσ₀
      have h1 := hPQ σ₀
      rw [hP, map_zero, mul_eq_zero] at h1
      rcases h1 with h1 | h1
      · exact Subtype.ext h1
      · exact absurd h1 (hQ σ₀)
    · intro h; exact hQ τ (by rw [h, map_zero])

set_option maxHeartbeats 6400000 in
include hx hfin hdeg in

theorem main [IsAlgClosed L] (zO : R.integers) :
    ∃ h : ((Algebra.trace K₀ F (zO : F) : K₀) : F) ∈ R.integers,
      R.residue ⟨_, h⟩ = ((Algebra.trace k₀ Fbar (R.residue zO) : k₀) : Fbar) := by
  classical
  haveI : FiniteDimensional K₀ F := by
    apply FiniteDimensional.of_finrank_pos; rw [hdeg]; exact hfin
  haveI : FiniteDimensional k₀ Fbar := FiniteDimensional.of_finrank_pos hfin
  obtain ⟨d, z, hzO, huniq, hcoord⟩ := exists_gaussBasis A R x hx hfin hdeg
  set zb : Fin d → Fbar := fun σ => R.residue ⟨z σ, hzO σ⟩ with hzbdef
  have hxinj : Function.Injective (aeval (R := κ) (R.residue x)) :=
    transcendental_iff_injective.mp hx

  have hpolyrel : ∀ r : Fin d → Polynomial L, (∑ σ, aeval (x : F) (r σ) * z σ = 0) → r = 0 := by
    intro r hr
    by_contra hne
    obtain ⟨σ₁, hσ₁⟩ : ∃ σ, r σ ≠ 0 := by
      by_contra h; push Not at h; exact hne (funext h)
    obtain ⟨i₁, hi₁⟩ : ∃ i, (r σ₁).coeff i ≠ 0 := by
      by_contra h; push Not at h; exact hσ₁ (Polynomial.ext fun n => by simpa using h n)
    let S : Finset ℕ := Finset.univ.biUnion fun σ => (r σ).support
    let s : Finset (Fin d × ℕ) := Finset.univ ×ˢ S
    let fam : Fin d × ℕ → L := fun p => (r p.1).coeff p.2
    have hmem₁ : (σ₁, i₁) ∈ s := by
      simp only [s, S, Finset.mem_product, Finset.mem_univ, true_and, Finset.mem_biUnion]
      exact ⟨σ₁, Polynomial.mem_support_iff.mpr hi₁⟩
    obtain ⟨c, hc0, hcA, ⟨σ₀, i₀⟩, hi₀s, hi₀⟩ := exists_scale A s fam ⟨(σ₁, i₁), hmem₁, hi₁⟩
    have hcoef : ∀ σ i, (C c * r σ).coeff i ∈ A := by
      intro σ i
      rw [coeff_C_mul]
      by_cases hi : i ∈ (r σ).support
      · exact hcA (σ, i) (by
          simp only [s, S, Finset.mem_product, Finset.mem_univ, true_and, Finset.mem_biUnion]
          exact ⟨σ, hi⟩)
      · rw [Polynomial.notMem_support_iff.mp hi, mul_zero]; exact zero_mem _
    have hlift := fun σ => exists_lift_of_coeff_mem (C c * r σ) (hcoef σ)
    choose rA hrA using hlift

    have hzero : (∑ σ, (rA σ).eval₂ (constToIntegers R) x * ⟨z σ, hzO σ⟩ : R.integers) = 0 := by
      apply Subtype.ext
      rw [AddSubmonoidClass.coe_finsetSum]
      simp only [MulMemClass.coe_mul, coe_eval₂_constToIntegers, hrA, map_mul, aeval_C, mul_assoc]
      rw [← Finset.mul_sum, hr, mul_zero]; rfl
    have hres := congrArg R.residue hzero
    rw [map_sum, map_zero] at hres
    simp only [map_mul, residue_eval₂_constToIntegers] at hres
    have h0 : (∑ σ, aeval (R.residue x) ((rA σ).map (residue A)) * R.residue ⟨z σ, hzO σ⟩) =
        ∑ σ, aeval (R.residue x) ((0 : Fin d → Polynomial κ) σ) * R.residue ⟨z σ, hzO σ⟩ := by
      rw [hres]; simp
    have hall := huniq (fun σ => (rA σ).map (residue A)) 0 h0
    have hσ₀ := congrArg (fun q : Fin d → Polynomial κ => (q σ₀).coeff i₀) hall
    simp only [coeff_map, Pi.zero_apply, coeff_zero] at hσ₀
    have hone : (rA σ₀).coeff i₀ = 1 := by
      apply Subtype.ext
      have h1 : (((rA σ₀).coeff i₀ : A) : L) = (C c * r σ₀).coeff i₀ := by
        rw [← hrA σ₀, coeff_map]; rfl
      rw [h1, coeff_C_mul]; exact hi₀
    rw [hone, map_one] at hσ₀
    exact one_ne_zero hσ₀

  have hli : LinearIndependent K₀ z := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    by_contra hne
    push Not at hne
    obtain ⟨σ₀, hσ₀⟩ := hne
    have hg' : ∑ σ, (g σ : F) * z σ = 0 := by
      rw [← hg]; refine Finset.sum_congr rfl fun σ _ => ?_; rfl
    obtain ⟨r, hr, hr0⟩ := exists_polynomial_relation (x : F) z g hg' σ₀ hσ₀
    exact hr0 (congrFun (hpolyrel r hr) σ₀)

  have hspan : ⊤ ≤ Submodule.span K₀ (Set.range z) := by
    rintro b -
    by_cases hb0 : b = 0
    · rw [hb0]; exact zero_mem _
    obtain ⟨c, hcO, hres⟩ := R.exists_smul_mem b hb0
    have hc0 := R.smul_const_ne_zero hcO hres
    obtain ⟨e, -, hbe⟩ := hcoord (c • b) hcO
    have hb : b = ∑ σ, (algebraMap L K₀ c⁻¹ * e σ) • z σ := by
      calc b = c⁻¹ • (c • b) := by rw [smul_smul, inv_mul_cancel₀ hc0, one_smul]
        _ = c⁻¹ • ∑ σ, (e σ : F) * z σ := by rw [hbe]
        _ = ∑ σ, (algebraMap L K₀ c⁻¹ * e σ) • z σ := by
          rw [Finset.smul_sum]
          refine Finset.sum_congr rfl fun σ _ => ?_
          rw [Algebra.smul_def, Algebra.smul_def, IsScalarTower.algebraMap_apply L K₀ F, map_mul,
            mul_assoc]
          rfl
    rw [hb]
    exact Submodule.sum_mem _ fun σ _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨σ, rfl⟩)
  let bF : Module.Basis (Fin d) K₀ F := Module.Basis.mk hli hspan
  have hbF : ∀ σ, bF σ = z σ := fun σ => Module.Basis.mk_apply hli hspan σ
  have hd : Fintype.card (Fin d) = Module.finrank K₀ F := (Module.finrank_eq_card_basis bF).symm

  have hlib : LinearIndependent k₀ zb := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    by_contra hne
    push Not at hne
    obtain ⟨σ₀, hσ₀⟩ := hne
    have hg' : ∑ σ, (g σ : Fbar) * zb σ = 0 := by
      rw [← hg]; refine Finset.sum_congr rfl fun σ _ => ?_; rfl
    obtain ⟨r, hr, hr0⟩ := exists_polynomial_relation (R.residue x) zb g hg' σ₀ hσ₀
    have h0 : (∑ σ, aeval (R.residue x) (r σ) * R.residue ⟨z σ, hzO σ⟩) =
        ∑ σ, aeval (R.residue x) ((0 : Fin d → Polynomial κ) σ) * R.residue ⟨z σ, hzO σ⟩ := by
      rw [show (∑ σ, aeval (R.residue x) (r σ) * R.residue ⟨z σ, hzO σ⟩) = 0 from hr]; simp
    exact hr0 (congrFun (huniq r 0 h0) σ₀)
  have hspanb : Submodule.span k₀ (Set.range zb) = ⊤ :=
    hlib.span_eq_top_of_card_eq_finrank' (by rw [hd, hdeg])
  let bFb : Module.Basis (Fin d) k₀ Fbar := Module.Basis.mk hlib hspanb.ge
  have hbFb : ∀ σ, bFb σ = zb σ := fun σ => Module.Basis.mk_apply hlib hspanb.ge σ

  have hrow : ∀ σ, ∃ e : Fin d → K₀, (∀ τ, (e τ : F) ∈ R.integers) ∧
      (zO : F) * z σ = ∑ τ, (e τ : F) * z τ := fun σ => hcoord _ (mul_mem zO.2 (hzO σ))
  choose e heO he using hrow
  have hrepr : ∀ σ τ, bF.repr ((zO : F) * z σ) τ = e σ τ := by
    intro σ τ
    have h1 : (zO : F) * z σ = ∑ τ, e σ τ • bF τ := by
      rw [he σ]; refine Finset.sum_congr rfl fun τ _ => ?_; rw [hbF]; rfl
    rw [h1, bF.repr_sum_self]
  have htrF : Algebra.trace K₀ F (zO : F) = ∑ σ, e σ σ := by
    rw [Algebra.trace_eq_matrix_trace bF, Matrix.trace]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [Matrix.diag_apply, Algebra.leftMulMatrix_eq_repr_mul, hbF, hrepr]

  have hebar : ∀ σ τ, ∃ eb : k₀, (eb : Fbar) = R.residue ⟨e σ τ, heO σ τ⟩ := fun σ τ =>
    exists_residue_eq_of_mem_adjoin A R x hx _ (e σ τ).2 (heO σ τ)
  choose eb heb using hebar
  have hreprb : ∀ σ τ, bFb.repr (R.residue zO * zb σ) τ = eb σ τ := by
    intro σ τ
    have h1 : R.residue zO * zb σ = ∑ τ, eb σ τ • bFb τ := by
      have h2 : (zO * ⟨z σ, hzO σ⟩ : R.integers) = ∑ τ, ⟨(e σ τ : F), heO σ τ⟩ * ⟨z τ, hzO τ⟩ :=
        Subtype.ext (by
          rw [AddSubmonoidClass.coe_finsetSum]
          simp only [MulMemClass.coe_mul]
          exact he σ)
      have h3 : R.residue zO * zb σ = R.residue (zO * ⟨z σ, hzO σ⟩) := by rw [map_mul]
      rw [h3, h2, map_sum]
      refine Finset.sum_congr rfl fun τ _ => ?_
      rw [map_mul, hbFb, ← heb]; rfl
    rw [h1, bFb.repr_sum_self]
  have htrFb : Algebra.trace k₀ Fbar (R.residue zO) = ∑ σ, eb σ σ := by
    rw [Algebra.trace_eq_matrix_trace bFb, Matrix.trace]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [Matrix.diag_apply, Algebra.leftMulMatrix_eq_repr_mul, hbFb, hreprb]

  have hmem : ((Algebra.trace K₀ F (zO : F) : K₀) : F) ∈ R.integers := by
    rw [htrF, AddSubmonoidClass.coe_finsetSum]
    exact sum_mem fun σ _ => heO σ σ
  refine ⟨hmem, ?_⟩
  have hel : (⟨_, hmem⟩ : R.integers) = ∑ σ, ⟨(e σ σ : F), heO σ σ⟩ :=
    Subtype.ext (by
      rw [AddSubmonoidClass.coe_finsetSum]
      change ((Algebra.trace K₀ F (zO : F) : K₀) : F) = _
      rw [htrF, AddSubmonoidClass.coe_finsetSum])
  rw [hel, map_sum, htrFb, AddSubmonoidClass.coe_finsetSum]
  exact Finset.sum_congr rfl fun σ _ => (heb σ σ).symm

end Main

end AlgebraicCurve.TraceReductionProof

open _root_.AlgebraicCurve _root_.P2MW.S_AlgebraicCurve_RegularProlongation_exists_residue_trace_eq_trace_residue_of_finrank_eq.AlgebraicCurve in
theorem solution
    {L : Type*} [Field L] [IsAlgClosed L] (A : ValuationSubring L)
    {F : Type*} [Field F] [Algebra L F]
    {Fbar : Type*} [Field Fbar] [Algebra (IsLocalRing.ResidueField A) Fbar]
    (R : AlgebraicCurve.RegularProlongation A F Fbar)
    (x : R.integers) (hx : Transcendental (IsLocalRing.ResidueField A) (R.residue x))
    (hfin : 0 < Module.finrank
      (IntermediateField.adjoin (IsLocalRing.ResidueField A) ({R.residue x} : Set Fbar)) Fbar)
    (hdeg : Module.finrank (IntermediateField.adjoin L ({(x : F)} : Set F)) F =
      Module.finrank
        (IntermediateField.adjoin (IsLocalRing.ResidueField A) ({R.residue x} : Set Fbar)) Fbar)
    (z : R.integers) :
    ∃ h : ((Algebra.trace (IntermediateField.adjoin L ({(x : F)} : Set F)) F (z : F) :
        IntermediateField.adjoin L ({(x : F)} : Set F)) : F) ∈ R.integers,
      R.residue ⟨_, h⟩ =
        ((Algebra.trace (IntermediateField.adjoin (IsLocalRing.ResidueField A)
            ({R.residue x} : Set Fbar)) Fbar (R.residue z) :
          IntermediateField.adjoin (IsLocalRing.ResidueField A) ({R.residue x} : Set Fbar)) :
            Fbar) :=
  AlgebraicCurve.TraceReductionProof.main A R x hx hfin hdeg z

end
end S_AlgebraicCurve_RegularProlongation_exists_residue_trace_eq_trace_residue_of_finrank_eq
end P2MW
export P2MW.S_AlgebraicCurve_RegularProlongation_exists_residue_trace_eq_trace_residue_of_finrank_eq (solution)
