-- Prove2me | solution 1 for AlgebraicCurve.Annulus.exists_twoEnd_of_modulus_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/19fa9a7b-312f-529a-9047-efc74140bd4a

import Definitions.Def_AlgebraicCurve_SemistableCharts
import Definitions.Def_AlgebraicCurve_PlaceEvaluation
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_Annulus_exists_twoEnd_of_modulus_ne_zero

set_option autoImplicit false

open AlgebraicCurve IsLocalRing

namespace H2Sol

variable {K : Type*} [Field K] {A : ValuationSubring K} {F : Type*} [Field F] [Algebra K F]

private def constUnit (v : Place K F) {c : K} (hc : c ≠ 0) : v.toValuationSubringˣ where
  val := ⟨algebraMap K F c, v.algebraMap_mem' c⟩
  inv := ⟨algebraMap K F c⁻¹, v.algebraMap_mem' c⁻¹⟩
  val_inv := by
    apply Subtype.ext
    show algebraMap K F c * algebraMap K F c⁻¹ = 1
    rw [← map_mul, mul_inv_cancel₀ hc, map_one]
  inv_val := by
    apply Subtype.ext
    show algebraMap K F c⁻¹ * algebraMap K F c = 1
    rw [← map_mul, inv_mul_cancel₀ hc, map_one]

private theorem ord_const (v : Place K F) {c : K} (hc : c ≠ 0) :
    v.ord (algebraMap K F c) = 0 :=
  v.ord_coe_unit (constUnit v hc)

private theorem residueInv_zero (v : Place K F) : v.residueInv (0 : v.ResidueField) = 0 := by
  have h := v.residueInv_algebraMap (0 : K)
  rwa [map_zero] at h

private theorem isUnit_of_evalAt_ne_zero (v : Place K F) {f : F}
    (hf : f ∈ v.toValuationSubring) (h0 : v.evalAt f ≠ 0) :
    IsUnit (⟨f, hf⟩ : v.toValuationSubring) := by
  by_contra hnu
  have hm : (⟨f, hf⟩ : v.toValuationSubring) ∈ maximalIdeal v.toValuationSubring :=
    (IsLocalRing.mem_maximalIdeal _).mpr (mem_nonunits_iff.mpr hnu)
  have hres : residue v.toValuationSubring ⟨f, hf⟩ = 0 := by
    rwa [← RingHom.mem_ker, IsLocalRing.ker_residue]
  rw [v.evalAt_of_mem hf, hres, residueInv_zero] at h0
  exact h0 rfl

private theorem inv_mem_of_evalAt_ne_zero (v : Place K F) {f : F}
    (hf : f ∈ v.toValuationSubring) (h0 : v.evalAt f ≠ 0) :
    f⁻¹ ∈ v.toValuationSubring := by
  obtain ⟨u, hu⟩ := isUnit_of_evalAt_ne_zero v hf h0
  have hf_eq : ((u : v.toValuationSubring) : F) = f := by rw [hu]
  have h2 : f * (((u⁻¹ : v.toValuationSubringˣ) : v.toValuationSubring) : F) = 1 := by
    rw [← hf_eq, ← MulMemClass.coe_mul, u.mul_inv, OneMemClass.coe_one]
  rw [inv_eq_of_mul_eq_one_right h2]
  exact (((u⁻¹ : v.toValuationSubringˣ) : v.toValuationSubring)).2

private theorem ord_of_evalAt_ne_zero (v : Place K F) {f : F}
    (hf : f ∈ v.toValuationSubring) (h0 : v.evalAt f ≠ 0) : v.ord f = 0 := by
  obtain ⟨u, hu⟩ := isUnit_of_evalAt_ne_zero v hf h0
  have : ((u : v.toValuationSubring) : F) = f := by rw [hu]
  rw [← this]
  exact v.ord_coe_unit u

private theorem residue_const (v : Place K F) (c : K) :
    residue v.toValuationSubring ⟨algebraMap K F c, v.algebraMap_mem' c⟩
      = algebraMap K v.ResidueField c := rfl

private theorem evalAt_const (v : Place K F) (hv : v.IsRational) (c : K) :
    v.evalAt (algebraMap K F c) = c := by
  apply v.algebraMap_residueField_injective
  rw [v.algebraMap_evalAt hv (v.algebraMap_mem' c), residue_const]

private theorem evalAt_mul (v : Place K F) (hv : v.IsRational) {f g : F}
    (hf : f ∈ v.toValuationSubring) (hg : g ∈ v.toValuationSubring) :
    v.evalAt (f * g) = v.evalAt f * v.evalAt g := by
  apply v.algebraMap_residueField_injective
  rw [map_mul, v.algebraMap_evalAt hv (mul_mem hf hg), v.algebraMap_evalAt hv hf,
    v.algebraMap_evalAt hv hg, ← map_mul]
  rfl

private theorem evalAt_inv (v : Place K F) (hv : v.IsRational) {f : F}
    (hf : f ∈ v.toValuationSubring) (h0 : v.evalAt f ≠ 0) :
    v.evalAt f⁻¹ = (v.evalAt f)⁻¹ := by
  have hfi := inv_mem_of_evalAt_ne_zero v hf h0
  have hf0 : f ≠ 0 := by
    rintro rfl
    rw [v.evalAt_of_mem (zero_mem _)] at h0
    have : residue v.toValuationSubring ⟨(0 : F), zero_mem _⟩ = 0 := map_zero _
    rw [this, residueInv_zero] at h0
    exact h0 rfl
  have h1 : v.evalAt f * v.evalAt f⁻¹ = 1 := by
    rw [← evalAt_mul v hv hf hfi, mul_inv_cancel₀ hf0]
    exact v.evalAt_one
  exact eq_inv_of_mul_eq_one_right h1

end H2Sol

theorem solution {K : Type*} [Field K] {A : ValuationSubring K} {F : Type*} [Field F]
    [Algebra K F] (An : Annulus A F) (hmod : ((An.modulus : K)) ≠ 0)
    (hz : An.param ≠ 0) :
    ∃ An' : Annulus A F, An'.dom = An.dom ∧ An'.modulus = An.modulus ∧
      An'.param * An.param = algebraMap K F ((An.modulus : K)) := by
  classical
  set w : F := algebraMap K F ((An.modulus : K)) * (An.param)⁻¹ with hwdef

  have hval : ∀ P ∈ An.dom, w ∈ P.toValuationSubring ∧
      P.evalAt w = (An.modulus : K) * (P.evalAt An.param)⁻¹ := by
    intro P hP
    obtain ⟨hrat, hreg, ⟨hmem, hmax⟩, hne, m, hm, hfact⟩ := An.mem_dom P hP
    have hinv := H2Sol.inv_mem_of_evalAt_ne_zero P hreg hne
    refine ⟨mul_mem (P.algebraMap_mem' _) hinv, ?_⟩
    rw [hwdef, H2Sol.evalAt_mul P hrat (P.algebraMap_mem' _) hinv, H2Sol.evalAt_const P hrat,
      H2Sol.evalAt_inv P hrat hreg hne]
  refine ⟨{ dom := An.dom
            param := w
            modulus := An.modulus
            modulus_mem := An.modulus_mem
            mem_dom := ?_
            existsUnique_evalAt_eq := ?_
            ord_param_sub := ?_
            unit_principle := ?_ }, rfl, rfl, ?_⟩
  ·
    intro P hP
    obtain ⟨hrat, hreg, ⟨hmem, hmax⟩, hne, m, hm, hfact⟩ := An.mem_dom P hP
    obtain ⟨hwmem, hweval⟩ := hval P hP
    have hm0 : (m : K) ≠ 0 := by
      intro h0; rw [h0, mul_zero] at hfact; exact hmod hfact
    have hmval : P.evalAt w = (m : K) := by
      rw [hweval, hfact]
      field_simp
    have hwA : P.evalAt w ∈ A := by rw [hmval]; exact m.2
    have hsame : (⟨P.evalAt w, hwA⟩ : A) = m := Subtype.ext hmval
    refine ⟨hrat, hwmem, ⟨hwA, by rw [hsame]; exact hm⟩, by rw [hmval]; exact hm0,
      ⟨P.evalAt An.param, hmem⟩, hmax, ?_⟩
    show (An.modulus : K) = P.evalAt w * ((⟨P.evalAt An.param, hmem⟩ : A) : K)
    rw [hmval, hfact]
    ring
  ·
    rintro c hc hc0 ⟨m', hm', hfact'⟩
    have hm'0 : (m' : K) ≠ 0 := by
      intro h0; rw [h0, mul_zero] at hfact'; exact hmod hfact'
    obtain ⟨P, ⟨hPdom, hPval⟩, huniq⟩ :=
      An.existsUnique_evalAt_eq m' hm' hm'0 ⟨c, hc, by rw [hfact']; ring⟩
    have hc0' : (c : K) ≠ 0 := hc0
    refine ⟨P, ⟨hPdom, ?_⟩, ?_⟩
    · obtain ⟨-, hweval⟩ := hval P hPdom
      rw [hweval, hPval, hfact']
      field_simp
    · rintro Q ⟨hQdom, hQval⟩
      obtain ⟨hratQ, hregQ, -, hneQ, -⟩ := An.mem_dom Q hQdom
      obtain ⟨-, hwevalQ⟩ := hval Q hQdom
      apply huniq
      refine ⟨hQdom, ?_⟩
      rw [hwevalQ] at hQval

      have hzQ : Q.evalAt An.param ≠ 0 := hneQ
      show Q.evalAt An.param = (m' : K)
      have h1 : (An.modulus : K) = (c : K) * Q.evalAt An.param := by
        rw [← hQval]
        field_simp
      rw [hfact'] at h1
      exact (mul_left_cancel₀ hc0' h1.symm)
  ·
    intro P hP
    obtain ⟨hrat, hreg, ⟨hmem, hmax⟩, hne, m, hm, hfact⟩ := An.mem_dom P hP
    obtain ⟨hwmem, hweval⟩ := hval P hP
    have hm0 : (m : K) ≠ 0 := by
      intro h0; rw [h0, mul_zero] at hfact; exact hmod hfact
    have hmval : P.evalAt w = (m : K) := by
      rw [hweval, hfact]; field_simp
    have hord1 := An.ord_param_sub P hP
    have hsubne : An.param - algebraMap K F (P.evalAt An.param) ≠ 0 := by
      intro h0
      rw [h0, P.ord_zero] at hord1
      exact one_ne_zero hord1.symm
    have hfactor : w - algebraMap K F (P.evalAt w)
        = algebraMap K F (-(m : K)) * (An.param - algebraMap K F (P.evalAt An.param))
            * (An.param)⁻¹ := by
      rw [hmval, hwdef, hfact]
      push_cast
      field_simp
      ring
    rw [hfactor]
    have h1 : algebraMap K F (-(m : K)) ≠ 0 :=
      fun h => hm0 (neg_eq_zero.mp ((map_eq_zero _).mp h))
    have h2 : algebraMap K F (-(m : K)) * (An.param - algebraMap K F (P.evalAt An.param)) ≠ 0 :=
      mul_ne_zero h1 hsubne
    rw [P.ord_mul h2 (inv_ne_zero hz), P.ord_mul h1 hsubne, P.ord_inv,
      H2Sol.ord_const P (neg_ne_zero.mpr hm0), hord1,
      H2Sol.ord_of_evalAt_ne_zero P hreg hne]
    ring
  ·
    intro f hf hford
    obtain ⟨m, c, hc0, hall⟩ := An.unit_principle f hf hford
    refine ⟨-m, c * (An.modulus : K) ^ m, mul_ne_zero hc0 (zpow_ne_zero m hmod), ?_⟩
    intro P hP
    obtain ⟨hrat, hreg, hadm, hne, mA, hmA, hfact⟩ := An.mem_dom P hP
    obtain ⟨hwmem, hweval⟩ := hval P hP
    obtain ⟨h, hu⟩ := hall P hP
    have hz0 : P.evalAt An.param ≠ 0 := hne
    have hexpr : P.evalAt f * (c * (An.modulus : K) ^ m)⁻¹ * (P.evalAt w) ^ (-(-m))
        = P.evalAt f * c⁻¹ * (P.evalAt An.param) ^ (-m) := by
      rw [hweval, neg_neg, mul_zpow, mul_inv, inv_zpow, zpow_neg (P.evalAt An.param) m]
      field_simp
    rw [hexpr]
    exact ⟨h, hu⟩
  ·
    show w * An.param = algebraMap K F ((An.modulus : K))
    rw [hwdef]
    field_simp

end S_AlgebraicCurve_Annulus_exists_twoEnd_of_modulus_ne_zero
end P2MW
export P2MW.S_AlgebraicCurve_Annulus_exists_twoEnd_of_modulus_ne_zero (solution)
