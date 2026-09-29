-- Prove2me | solution 1 for AlgebraicCurve.SemistableCovering.ord_eq_single_sub_single_of_forall_residue_evalAt_ne_zero_of_rankOne
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/6cc40020-5d81-55ed-9ed3-e105c5c8859a

import Definitions.Def_AlgebraicCurve_SemistableCharts
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Theorems.Thm_AlgebraicCurve_Annulus_sum_eq_ord_add_ord_and_prod_valuation_evalAt_zpow_eq_of_regularProlongation
import Theorems.Thm_AlgebraicCurve_Annulus_ord_sub_div_sub_and_residue_src_eq_one_and_residue_tgt_eq_of_depth_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_SemistableCovering_ord_eq_single_sub_single_of_forall_residue_evalAt_ne_zero_of_rankOne

set_option autoImplicit false

p2m_open "AlgebraicCurve P2MW.S_AlgebraicCurve_SemistableCovering_ord_eq_single_sub_single_of_forall_residue_evalAt_ne_zero_of_rankOne.AlgebraicCurve"

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "ComponentChart Annulus Place Divisor Divisor.degree HasPrincipalDivisors HasPrincipalDivisors.exists_divisor genusFF IsCurveOver RegularProlongation Annulus.sum_eq_ord_add_ord_and_prod_valuation_evalAt_zpow_eq_of_regularProlongation Annulus.ord_sub_div_sub_and_residue_src_eq_one_and_residue_tgt_eq_of_depth_eq"
p2m_open "AlgebraicCurve"

namespace Place
p2m_export "AlgebraicCurve.Place" "ext ResidueField deg ord ord_mul ord_coe_unit algebraMap_mem' toValuationSubring IsRational algebraMap_residueField_injective residueInv_algebraMap evalAt evalAt_of_mem algebraMap_evalAt"
p2m_open "AlgebraicCurve.Place"

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

private theorem _root_.AlgebraicCurve.Place.ord_eq_zero_of_evalAt_ne_zero (v : Place K F) {f : F} (hf : f ∈ v.toValuationSubring)
    (h : v.evalAt f ≠ 0) : v.ord f = 0 := by
  have hres : IsLocalRing.residue v.toValuationSubring ⟨f, hf⟩ ≠ 0 := by
    intro h0
    apply h
    rw [v.evalAt_of_mem hf, h0, ← map_zero (algebraMap K v.ResidueField), v.residueInv_algebraMap]
  have hu : IsUnit (⟨f, hf⟩ : v.toValuationSubring) := by
    by_contra hnu
    apply hres
    rwa [IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  obtain ⟨u, hu⟩ := hu
  have := v.ord_coe_unit u
  rwa [hu] at this

p2m_export "AlgebraicCurve.Place" "ord_eq_zero_of_evalAt_ne_zero"

private theorem _root_.AlgebraicCurve.Place.ne_zero_of_evalAt_ne_zero (v : Place K F) {f : F} (h : v.evalAt f ≠ 0) : f ≠ 0 := by
  rintro rfl
  apply h
  rw [v.evalAt_of_mem (zero_mem _)]
  have : (⟨(0 : F), zero_mem _⟩ : v.toValuationSubring) = 0 := rfl
  rw [this, map_zero, ← map_zero (algebraMap K v.ResidueField), v.residueInv_algebraMap]

p2m_export "AlgebraicCurve.Place" "ne_zero_of_evalAt_ne_zero"

private theorem _root_.AlgebraicCurve.Place.evalAt_mul_of_mem' (v : Place K F) (hv : v.IsRational) {f g : F}
    (hf : f ∈ v.toValuationSubring) (hg : g ∈ v.toValuationSubring) :
    v.evalAt (f * g) = v.evalAt f * v.evalAt g := by
  apply v.algebraMap_residueField_injective
  rw [map_mul, v.algebraMap_evalAt hv hf, v.algebraMap_evalAt hv hg, v.algebraMap_evalAt hv (mul_mem hf hg),
    ← map_mul]
  rfl

p2m_export "AlgebraicCurve.Place" "evalAt_mul_of_mem'"

private theorem _root_.AlgebraicCurve.Place.evalAt_algebraMap' (v : Place K F) (a : K) : v.evalAt (algebraMap K F a) = a := by
  rw [v.evalAt_of_mem (v.algebraMap_mem' a)]
  have : IsLocalRing.residue v.toValuationSubring ⟨algebraMap K F a, v.algebraMap_mem' a⟩ =
      algebraMap K v.ResidueField a := rfl
  rw [this, v.residueInv_algebraMap]

p2m_export "AlgebraicCurve.Place" "evalAt_algebraMap'"

private theorem deg_eq_one_of_isRational' {v : Place K F} (hv : v.IsRational) : v.deg = 1 := by
  have hbij : Function.Bijective (algebraMap K v.ResidueField) :=
    ⟨v.algebraMap_residueField_injective, hv⟩
  show Module.finrank K v.ResidueField = 1
  rw [← Module.finrank_self K]
  exact ((AlgEquiv.ofBijective (Algebra.ofId K v.ResidueField) hbij).toLinearEquiv.finrank_eq).symm

end Place

namespace ComponentChart
p2m_export "AlgebraicCurve.ComponentChart" "integers algebraMap_mem_iff residue_surjective placeMap residue nodes exists_smul_mem residue_algebraMap ker_residue mapDomain_placeMap placeMap_not_mem_nodes dom"
p2m_open "AlgebraicCurve.ComponentChart"

variable {L : Type*} [Field L] {A : ValuationSubring L} {F : Type*} [Field F] [Algebra L F]
variable {Fbar : Type*} [Field Fbar] [Algebra (IsLocalRing.ResidueField A) Fbar]

@[reducible] private def _root_.AlgebraicCurve.ComponentChart.toRegularProlongation (C : ComponentChart A F Fbar) : RegularProlongation A F Fbar where
  integers := C.integers
  residue := C.residue
  algebraMap_mem_iff := C.algebraMap_mem_iff
  residue_surjective := C.residue_surjective
  ker_residue := C.ker_residue
  residue_algebraMap := C.residue_algebraMap
  exists_smul_mem := C.exists_smul_mem

p2m_export "AlgebraicCurve.ComponentChart" "toRegularProlongation"
end ComponentChart

namespace Annulus
p2m_export "AlgebraicCurve.Annulus" "IsAttached existsUnique_evalAt_eq modulus modulus_mem dom mem_dom param sum_eq_ord_add_ord_and_prod_valuation_evalAt_zpow_eq_of_regularProlongation ord_sub_div_sub_and_residue_src_eq_one_and_residue_tgt_eq_of_depth_eq"
p2m_open "AlgebraicCurve.Annulus"

variable {L : Type*} [Field L] [IsAlgClosed L] {A : ValuationSubring L} {F : Type*} [Field F] [Algebra L F]

private theorem _root_.AlgebraicCurve.Annulus.exists_two_radii (An : Annulus A F) (hmod0 : ((An.modulus : A) : L) ≠ 0) :
    ∃ Q₁ ∈ An.dom, ∃ Q₂ ∈ An.dom, A.valuation (Q₁.evalAt An.param) ≠ A.valuation (Q₂.evalAt An.param) := by
  set M : L := ((An.modulus : A) : L) with hM
  have hMm : An.modulus ∈ IsLocalRing.maximalIdeal A := An.modulus_mem

  have memA : ∀ (x : L) (k : ℕ) (y : A), 0 < k → x ^ k = (y : L) → x ∈ A := by
    intro x k y hk hxy
    by_contra hx
    have hxi : x⁻¹ ∈ A := (A.mem_or_inv_mem x).resolve_left hx
    have hx0 : x ≠ 0 := by rintro rfl; exact hx A.zero_mem
    have hximax : (⟨x⁻¹, hxi⟩ : A) ∈ IsLocalRing.maximalIdeal A := by
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
      intro hu
      obtain ⟨w, hw⟩ := hu
      apply hx
      have : ((w⁻¹ : Aˣ) : A).1 = x := by
        have h1 : ((w⁻¹ : Aˣ) : A).1 * x⁻¹ = 1 := by
          have := congrArg (fun t : A => (t : L)) w.inv_mul
          simpa [hw] using this
        have := eq_inv_of_mul_eq_one_left h1
        rw [this, inv_inv]
      rw [← this]; exact ((w⁻¹ : Aˣ) : A).2

    have hone : (1 : A) = y * ⟨x⁻¹, hxi⟩ ^ k := by
      apply Subtype.ext
      simp only [OneMemClass.coe_one, MulMemClass.coe_mul, SubmonoidClass.coe_pow]
      rw [← hxy, ← mul_pow, mul_inv_cancel₀ hx0, one_pow]
    have : (1 : A) ∈ IsLocalRing.maximalIdeal A := by
      rw [hone]; exact Ideal.mul_mem_left _ _ (Ideal.pow_mem_of_mem _ hximax _ hk)
    exact (IsLocalRing.maximalIdeal.isMaximal A).ne_top (Ideal.eq_top_of_isUnit_mem _ this isUnit_one)

  have memMax : ∀ (x : L) (k : ℕ) (y : A) (hx : x ∈ A), y ∈ IsLocalRing.maximalIdeal A → x ^ k = (y : L) →
      (⟨x, hx⟩ : A) ∈ IsLocalRing.maximalIdeal A := by
    intro x k y hx hy hxy
    have : (⟨x, hx⟩ : A) ^ k = y := Subtype.ext (by simpa using hxy)
    have hmem : (⟨x, hx⟩ : A) ^ k ∈ IsLocalRing.maximalIdeal A := this ▸ hy
    exact (IsLocalRing.maximalIdeal.isMaximal A).isPrime.mem_of_pow_mem _ hmem

  obtain ⟨c, hc⟩ := IsAlgClosed.exists_pow_nat_eq M (by norm_num : 0 < 2)
  obtain ⟨c₂, hc₂⟩ := IsAlgClosed.exists_pow_nat_eq (M ^ 2) (by norm_num : 0 < 3)
  have hcA : c ∈ A := memA c 2 An.modulus (by norm_num) hc
  have hc₂A : c₂ ∈ A := memA c₂ 3 (An.modulus ^ 2) (by norm_num) (by rw [hc₂]; simp [hM])
  have hcm : (⟨c, hcA⟩ : A) ∈ IsLocalRing.maximalIdeal A := memMax c 2 An.modulus hcA hMm hc
  have hc₂m : (⟨c₂, hc₂A⟩ : A) ∈ IsLocalRing.maximalIdeal A :=
    memMax c₂ 3 (An.modulus ^ 2) hc₂A (Ideal.pow_mem_of_mem _ hMm _ (by norm_num)) (by rw [hc₂]; simp [hM])
  have hc0 : c ≠ 0 := by rintro rfl; apply hmod0; rw [← hc]; norm_num
  have hc₂0 : c₂ ≠ 0 := by
    rintro rfl; apply hmod0
    have : M ^ 2 = 0 := by rw [← hc₂]; norm_num
    exact pow_eq_zero_iff (by norm_num) |>.mp this

  have hadm : ∃ m ∈ IsLocalRing.maximalIdeal A, M = c * (m : L) := ⟨⟨c, hcA⟩, hcm, by rw [← hc]; ring⟩
  have ht : (M / c₂) ^ 3 = M := by
    rw [div_pow, hc₂]; field_simp
  have htA : M / c₂ ∈ A := memA (M / c₂) 3 An.modulus (by norm_num) ht
  have htm : (⟨M / c₂, htA⟩ : A) ∈ IsLocalRing.maximalIdeal A := memMax _ 3 An.modulus htA hMm ht
  have hadm₂ : ∃ m ∈ IsLocalRing.maximalIdeal A, M = c₂ * (m : L) :=
    ⟨⟨M / c₂, htA⟩, htm, by simp only; rw [mul_div_cancel₀ _ hc₂0]⟩
  obtain ⟨Q₁, ⟨hQ₁, hQ₁v⟩, -⟩ := An.existsUnique_evalAt_eq ⟨c, hcA⟩ hcm hc0 hadm
  obtain ⟨Q₂, ⟨hQ₂, hQ₂v⟩, -⟩ := An.existsUnique_evalAt_eq ⟨c₂, hc₂A⟩ hc₂m hc₂0 hadm₂
  refine ⟨Q₁, hQ₁, Q₂, hQ₂, ?_⟩
  rw [hQ₁v, hQ₂v]

  intro hv

  have hvM : A.valuation M < 1 := by
    rw [hM]; exact (A.valuation_lt_one_iff _).mp hMm
  have h1 : A.valuation M = A.valuation c ^ 2 := by rw [← hc, map_pow]
  have h2 : A.valuation M ^ 2 = A.valuation c₂ ^ 3 := by rw [← map_pow, ← hc₂, map_pow]
  rw [hv] at h1

  have hM0 : A.valuation M ≠ 0 := (Valuation.ne_zero_iff _).mpr hmod0
  have h3 : A.valuation M ^ 3 = A.valuation M ^ 4 := by
    calc A.valuation M ^ 3 = (A.valuation c₂ ^ 2) ^ 3 := by rw [h1]
      _ = (A.valuation c₂ ^ 3) ^ 2 := by rw [← pow_mul, ← pow_mul]
      _ = (A.valuation M ^ 2) ^ 2 := by rw [h2]
      _ = A.valuation M ^ 4 := by rw [← pow_mul]
  have : A.valuation M = 1 := by
    have h4 : A.valuation M ^ 3 * 1 = A.valuation M ^ 3 * A.valuation M := by rw [mul_one, ← pow_succ, h3]
    exact (mul_left_cancel₀ (pow_ne_zero 3 hM0) h4).symm
  exact absurd this (ne_of_lt hvM)

p2m_export "AlgebraicCurve.Annulus" "exists_two_radii"
end Annulus

end AlgebraicCurve

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "ComponentChart Annulus Place Divisor Divisor.degree HasPrincipalDivisors HasPrincipalDivisors.exists_divisor genusFF IsCurveOver RegularProlongation Annulus.sum_eq_ord_add_ord_and_prod_valuation_evalAt_zpow_eq_of_regularProlongation Annulus.ord_sub_div_sub_and_residue_src_eq_one_and_residue_tgt_eq_of_depth_eq"
namespace Annulus
p2m_export "AlgebraicCurve.Annulus" "IsAttached existsUnique_evalAt_eq modulus modulus_mem dom mem_dom param sum_eq_ord_add_ord_and_prod_valuation_evalAt_zpow_eq_of_regularProlongation ord_sub_div_sub_and_residue_src_eq_one_and_residue_tgt_eq_of_depth_eq"
p2m_open "AlgebraicCurve.Annulus AlgebraicCurve"

variable {L : Type*} [Field L] [IsAlgClosed L] {A : ValuationSubring L} {F : Type*} [Field F] [Algebra L F]
variable {Fs : Type*} [Field Fs] [Algebra (IsLocalRing.ResidueField A) Fs]
variable {Ft : Type*} [Field Ft] [Algebra (IsLocalRing.ResidueField A) Ft]

private theorem forall_ord_eq_zero_of_units_at_ends [HasPrincipalDivisors L F]
    (An An' : Annulus A F)
    (hpairE : An'.dom = An.dom ∧ An'.modulus = An.modulus ∧ ((An.modulus : A) : L) ≠ 0 ∧
      An'.param * An.param = algebraMap L F ((An.modulus : A) : L))
    (Cs : ComponentChart A F Fs) (Ct : ComponentChart A F Ft)
    (xs : Place (IsLocalRing.ResidueField A) Fs) (xt : Place (IsLocalRing.ResidueField A) Ft)
    (hatts : An.IsAttached Cs xs) (hattt : An'.IsAttached Ct xt)
    (k : F) (hk0 : k ≠ 0) (hkpole : ∀ Q ∈ An.dom, 0 ≤ Q.ord k)
    (hks : k ∈ Cs.integers) (hksreg : Cs.residue ⟨k, hks⟩ ∈ xs.toValuationSubring)
    (hksval : xs.evalAt (Cs.residue ⟨k, hks⟩) ≠ 0)
    (hkt : k ∈ Ct.integers) (hktreg : Ct.residue ⟨k, hkt⟩ ∈ xt.toValuationSubring)
    (hktval : xt.evalAt (Ct.residue ⟨k, hkt⟩) ≠ 0) :
    ∀ Q ∈ An.dom, Q.ord k = 0 := by
  classical
  obtain ⟨hdom, -, hmod0, hzz'⟩ := hpairE
  set M : L := ((An.modulus : A) : L) with hM

  obtain ⟨Dk, hDk, -⟩ := HasPrincipalDivisors.exists_divisor (K := L) k hk0
  set D : Divisor L F := Dk.filter fun Q => Q ∈ An.dom with hD
  have hDsupp : ∀ Q ∈ D.support, Q ∈ An.dom := by
    intro Q hQ; rw [hD, Finsupp.support_filter, Finset.mem_filter] at hQ; exact hQ.2
  have hDval : ∀ Q ∈ An.dom, D Q = Q.ord k := by
    intro Q hQ; rw [hD, Finsupp.filter_apply, if_pos hQ, hDk]

  obtain ⟨Q₁, hQ₁, Q₂, hQ₂, hwide⟩ := An.exists_two_radii hmod0
  have hz0 : An.param ≠ 0 := by
    obtain ⟨-, -, -, hne, -⟩ := An.mem_dom Q₁ hQ₁
    exact Q₁.ne_zero_of_evalAt_ne_zero hne
  have hpeq : An'.param = algebraMap L F M * An.param⁻¹ := by
    rw [← hzz', mul_assoc, mul_inv_cancel₀ hz0, mul_one]

  obtain ⟨-, hza, hxa, hsla⟩ := hatts
  obtain ⟨-, hz', hx', hsl'⟩ := hattt
  have hzb : algebraMap L F M * An.param⁻¹ ∈ Ct.integers := by rw [← hpeq]; exact hz'
  have hsub : (⟨algebraMap L F M * An.param⁻¹, hzb⟩ : Ct.integers) = ⟨An'.param, hz'⟩ := Subtype.ext hpeq.symm
  have hxb : xt.ord (Ct.residue ⟨algebraMap L F M * An.param⁻¹, hzb⟩) = 1 := by rw [hsub]; exact hx'
  have hslb : ∀ (f : F) (hf : f ∈ Ct.integers), Ct.residue ⟨f, hf⟩ ≠ 0 → (∀ P ∈ An.dom, P.ord f = 0) →
      ∀ P ∈ An.dom, ∃ h : P.evalAt f * (P.evalAt (algebraMap L F M * An.param⁻¹)) ^
        (-(xt.ord (Ct.residue ⟨f, hf⟩))) ∈ A, IsUnit (⟨_, h⟩ : A) := by
    intro f hf hres hcl Q hQ
    have hcl' : ∀ P ∈ An'.dom, P.ord f = 0 := fun P hP => hcl P (by rw [← hdom]; exact hP)
    have := hsl' f hf hres hcl' Q (by rw [hdom]; exact hQ)
    rw [hpeq] at this
    exact this

  have hresa : Cs.residue ⟨k, hks⟩ ≠ 0 := xs.ne_zero_of_evalAt_ne_zero hksval
  have hkt' : (algebraMap L F (1 : L))⁻¹ * k ∈ Ct.integers := by simpa using hkt
  have hsub' : (⟨(algebraMap L F (1 : L))⁻¹ * k, hkt'⟩ : Ct.integers) = ⟨k, hkt⟩ := Subtype.ext (by simp)
  have hresb : Ct.residue ⟨(algebraMap L F (1 : L))⁻¹ * k, hkt'⟩ ≠ 0 := by
    rw [hsub']; exact xt.ne_zero_of_evalAt_ne_zero hktval

  obtain ⟨hmass, -⟩ :=
    AlgebraicCurve.Annulus.sum_eq_ord_add_ord_and_prod_valuation_evalAt_zpow_eq_of_regularProlongation
      An hmod0 Cs.toRegularProlongation xs hza hxa hsla Ct.toRegularProlongation xt hzb hxb hslb
      ⟨Q₁, hQ₁, Q₂, hQ₂, hwide⟩ k hk0 hks hresa 1 one_ne_zero hkt' hresb D hDsupp hDval
  have hzero : (D.sum fun _ n => n) = 0 := by
    rw [hmass, hsub', xs.ord_eq_zero_of_evalAt_ne_zero hksreg hksval,
      xt.ord_eq_zero_of_evalAt_ne_zero hktreg hktval, add_zero]

  have hnonneg : ∀ Q ∈ D.support, 0 ≤ D Q := fun Q hQ => by
    rw [hDval Q (hDsupp Q hQ)]; exact hkpole Q (hDsupp Q hQ)
  have hall : ∀ Q ∈ D.support, D Q = 0 := (Finset.sum_eq_zero_iff_of_nonneg hnonneg).mp hzero
  intro Q hQ
  rw [← hDval Q hQ]
  by_cases hs : Q ∈ D.support
  · exact hall Q hs
  · exact Finsupp.notMem_support_iff.mp hs

end AlgebraicCurve.Annulus

theorem solution
    {L : Type*} [Field L] [IsAlgClosed L] (A : ValuationSubring L)
    (π : A) (hπ : π ∈ IsLocalRing.maximalIdeal A) (hπ0 : π ≠ 0)
    (hrk : ∀ x : L, x ≠ 0 → ∀ y : A, y ∈ IsLocalRing.maximalIdeal A →
      ∃ n : ℕ, A.valuation ((y : L) ^ n) ≤ A.valuation x)
    (F : Type*) [Field F] [Algebra L F]
    (n m : ℕ) (Fbar : Fin n → Type*) [∀ i, Field (Fbar i)]
    [∀ i, Algebra (IsLocalRing.ResidueField A) (Fbar i)]
    (hratBar : ∀ i, ∀ Q : Place (IsLocalRing.ResidueField A) (Fbar i), Q.IsRational)
    (C : ∀ i, ComponentChart A F (Fbar i))
    (hratF : ∀ i, ∀ P ∈ (C i).dom, P.IsRational)
    (An An' : Fin m → Annulus A F) (src tgt : Fin m → Fin n)
    (xs : ∀ e, Place (IsLocalRing.ResidueField A) (Fbar (src e)))
    (xt : ∀ e, Place (IsLocalRing.ResidueField A) (Fbar (tgt e)))
    (w : Fin m → ℕ)
    (hpair : ∀ e, (An' e).dom = (An e).dom ∧ (An' e).modulus = (An e).modulus ∧
      ((An e).modulus : L) ≠ 0 ∧
      (An' e).param * (An e).param = algebraMap L F ((An e).modulus : L))
    (hw : ∀ e, ∃ u : Aˣ, (An e).modulus = u * π ^ w e)
    (hatt : ∀ e, (An e).IsAttached (C (src e)) (xs e) ∧ (An' e).IsAttached (C (tgt e)) (xt e))
    (hnodes : (∀ i, ∀ x ∈ (C i).nodes, ∃ e,
        (⟨src e, xs e⟩ : Σ j, Place (IsLocalRing.ResidueField A) (Fbar j)) = ⟨i, x⟩ ∨
        (⟨tgt e, xt e⟩ : Σ j, Place (IsLocalRing.ResidueField A) (Fbar j)) = ⟨i, x⟩) ∧
      (∀ i, ∀ x ∈ (C i).nodes, ∀ E E' : Fin m ⊕ Fin m,
        Sum.elim (fun e => (⟨src e, xs e⟩ : Σ j, Place (IsLocalRing.ResidueField A) (Fbar j)))
          (fun e => ⟨tgt e, xt e⟩) E = ⟨i, x⟩ →
        Sum.elim (fun e => (⟨src e, xs e⟩ : Σ j, Place (IsLocalRing.ResidueField A) (Fbar j)))
          (fun e => ⟨tgt e, xt e⟩) E' = ⟨i, x⟩ → E = E'))
    (hcover : ∀ P : Place L F,
      (∃ i, P ∈ (C i).dom ∧ (∀ j, P ∈ (C j).dom → j = i) ∧ ∀ e, P ∉ (An e).dom) ∨
      (∃ e, P ∈ (An e).dom ∧ (∀ e', P ∈ (An e').dom → e' = e) ∧ ∀ i, P ∉ (C i).dom))
    (hdisc : ∀ i, ∀ Q : Place (IsLocalRing.ResidueField A) (Fbar i), Q ∉ (C i).nodes →
      ∃ (T : F) (hT : T ∈ (C i).integers), (C i).residue ⟨T, hT⟩ ≠ 0 ∧ Q.ord ((C i).residue ⟨T, hT⟩) = 1 ∧
        (∀ P ∈ (C i).dom, (C i).placeMap P = Q → T ∈ P.toValuationSubring ∧
          ∃ h : P.evalAt T ∈ A, (⟨P.evalAt T, h⟩ : A) ∈ IsLocalRing.maximalIdeal A) ∧
        ∀ c : A, c ∈ IsLocalRing.maximalIdeal A →
          ∃! P : Place L F, P ∈ (C i).dom ∧ (C i).placeMap P = Q ∧ P.evalAt T = c)
    (hgenus : genusFF L F + n = (∑ i, genusFF (IsLocalRing.ResidueField A) (Fbar i)) + m + 1)
    [IsCurveOver L F] [Algebra.EssFiniteType L F]
    [∀ i, IsCurveOver (IsLocalRing.ResidueField A) (Fbar i)]
    [∀ i, Algebra.EssFiniteType (IsLocalRing.ResidueField A) (Fbar i)]
    (e₀ : Fin m) (P P' : Place L F) (hP : P ∈ (An e₀).dom) (hP' : P' ∈ (An e₀).dom) (hPP' : P ≠ P')
    (d : ℕ) (u u' : Aˣ) (h : P.evalAt (An e₀).param ∈ A) (h' : P'.evalAt (An e₀).param ∈ A)
    (hd : (⟨P.evalAt (An e₀).param, h⟩ : A) = u * π ^ d) (hd' : (⟨P'.evalAt (An e₀).param, h'⟩ : A) = u' * π ^ d)
    (g : F) (hg0 : g ≠ 0)
    (hgann : ∀ e, ∀ Q ∈ (An e).dom, Q ≠ P → Q ≠ P' → 0 ≤ Q.ord g)
    (hgP : -1 ≤ P.ord g) (hgP' : 1 ≤ P'.ord g)
    (hgres : ∀ i, ∃ hg : g ∈ (C i).integers, (C i).residue ⟨g, hg⟩ ≠ 0 ∧ ∀ x ∈ (C i).nodes,
      (C i).residue ⟨g, hg⟩ ∈ x.toValuationSubring ∧ x.evalAt ((C i).residue ⟨g, hg⟩) ≠ 0)
    :
    ∃ Dg : Divisor L F, (∀ Q, Dg Q = Q.ord g) ∧
      (∀ e, ∀ Q ∈ (An e).dom, Dg Q = (Finsupp.single P' 1 - Finsupp.single P 1 : Divisor L F) Q) ∧
      ∃ Di : Fin n → Divisor L F, Dg - (Finsupp.single P' 1 - Finsupp.single P 1) = ∑ i, Di i ∧
        (∀ i, ∀ Q ∈ (Di i).support, Q ∈ (C i).dom) ∧ ∀ i, Divisor.degree (Di i) = 0 := by
  classical
  have _ := hdisc; have _ := hgenus; have _ := hnodes; have _ := hrk
  obtain ⟨Dg, hDg, -⟩ := HasPrincipalDivisors.exists_divisor (K := L) g hg0

  set r : F := ((An e₀).param - algebraMap L F (P.evalAt (An e₀).param)) /
      ((An e₀).param - algebraMap L F (P'.evalAt (An e₀).param)) with hr
  have hloc := AlgebraicCurve.Annulus.ord_sub_div_sub_and_residue_src_eq_one_and_residue_tgt_eq_of_depth_eq A π
    hπ hπ0 F n m Fbar hratBar C hratF An An' src tgt xs xt w hpair hw hatt hnodes hcover e₀ P P' hP hP' hPP' d u u'
    h h' hd hd'
  obtain ⟨hr0, -, hrdom, ⟨hrs, hrs1⟩, ⟨hrt, hrtl⟩⟩ := hloc

  have hne_of_ne : ∀ e, e ≠ e₀ → ∀ Q ∈ (An e).dom, Q ≠ P ∧ Q ≠ P' := by
    intro e he Q hQ
    constructor
    · rintro rfl
      rcases hcover Q with ⟨i, -, -, hnot⟩ | ⟨e', -, hun, -⟩
      · exact hnot e hQ
      · exact he ((hun e hQ).trans (hun e₀ hP).symm)
    · rintro rfl
      rcases hcover Q with ⟨i, -, -, hnot⟩ | ⟨e', -, hun, -⟩
      · exact hnot e hQ
      · exact he ((hun e hQ).trans (hun e₀ hP').symm)

  have hann : ∀ e, ∀ Q ∈ (An e).dom, Dg Q = (Finsupp.single P' 1 - Finsupp.single P 1 : Divisor L F) Q := by
    intro e Q hQ
    rw [hDg, Finsupp.sub_apply, Finsupp.single_apply, Finsupp.single_apply]
    obtain ⟨hgs, -, hgsnode⟩ := hgres (src e)
    obtain ⟨hgt, -, hgtnode⟩ := hgres (tgt e)
    obtain ⟨hxs_reg, hxs_val⟩ := hgsnode (xs e) (hatt e).1.1
    obtain ⟨hxt_reg, hxt_val⟩ := hgtnode (xt e) (hatt e).2.1
    by_cases he : e = e₀
    · subst he

      have hk0 : g * r ≠ 0 := mul_ne_zero hg0 hr0
      have hkpole : ∀ Q ∈ (An e).dom, 0 ≤ Q.ord (g * r) := by
        intro Q hQ
        rw [Q.ord_mul hg0 hr0, hrdom Q hQ, Finsupp.sub_apply, Finsupp.single_apply, Finsupp.single_apply]
        by_cases h1 : P = Q
        · subst h1; rw [if_pos rfl, if_neg (Ne.symm hPP')]; linarith [hgP]
        · by_cases h2 : P' = Q
          · subst h2; rw [if_neg h1, if_pos rfl]; linarith [hgP']
          · rw [if_neg h1, if_neg h2]; linarith [hgann e Q hQ (Ne.symm h1) (Ne.symm h2)]
      have hks : g * r ∈ (C (src e)).integers := mul_mem hgs hrs
      have hkt : g * r ∈ (C (tgt e)).integers := mul_mem hgt hrt
      have hress : (C (src e)).residue ⟨g * r, hks⟩ = (C (src e)).residue ⟨g, hgs⟩ := by
        have : (⟨g * r, hks⟩ : (C (src e)).integers) = ⟨g, hgs⟩ * ⟨r, hrs⟩ := rfl
        rw [this, map_mul, hrs1, mul_one]
      have hrest : (C (tgt e)).residue ⟨g * r, hkt⟩ = (C (tgt e)).residue ⟨g, hgt⟩ *
          algebraMap (IsLocalRing.ResidueField A) (Fbar (tgt e)) (IsLocalRing.residue A ((u : A) * ↑u'⁻¹)) := by
        have : (⟨g * r, hkt⟩ : (C (tgt e)).integers) = ⟨g, hgt⟩ * ⟨r, hrt⟩ := rfl
        rw [this, map_mul, hrtl]
      have hconst_mem : algebraMap (IsLocalRing.ResidueField A) (Fbar (tgt e))
          (IsLocalRing.residue A ((u : A) * ↑u'⁻¹)) ∈ (xt e).toValuationSubring := (xt e).algebraMap_mem' _
      have hclean := AlgebraicCurve.Annulus.forall_ord_eq_zero_of_units_at_ends (An e) (An' e) (hpair e)
        (C (src e)) (C (tgt e)) (xs e) (xt e) (hatt e).1 (hatt e).2 (g * r) hk0 hkpole
        hks (by rw [hress]; exact hxs_reg) (by rw [hress]; exact hxs_val)
        hkt (by rw [hrest]; exact mul_mem hxt_reg hconst_mem) (by
          rw [hrest, (xt e).evalAt_mul_of_mem' (hratBar _ _) hxt_reg hconst_mem, (xt e).evalAt_algebraMap']
          exact mul_ne_zero hxt_val (((IsLocalRing.residue A).isUnit_map (u * u'⁻¹).isUnit).ne_zero))
      have h0 := hclean Q hQ
      rw [Q.ord_mul hg0 hr0, hrdom Q hQ, Finsupp.sub_apply, Finsupp.single_apply, Finsupp.single_apply] at h0
      linarith
    · obtain ⟨hQP, hQP'⟩ := hne_of_ne e he Q hQ
      have hclean := AlgebraicCurve.Annulus.forall_ord_eq_zero_of_units_at_ends (An e) (An' e) (hpair e)
        (C (src e)) (C (tgt e)) (xs e) (xt e) (hatt e).1 (hatt e).2 g hg0
        (fun Q hQ => hgann e Q hQ (hne_of_ne e he Q hQ).1 (hne_of_ne e he Q hQ).2)
        hgs hxs_reg hxs_val hgt hxt_reg hxt_val
      rw [hclean Q hQ, if_neg (Ne.symm hQP'), if_neg (Ne.symm hQP)]; ring

  refine ⟨Dg, hDg, hann, fun i => (Dg - (Finsupp.single P' 1 - Finsupp.single P 1)).filter
    (fun Q => Q ∈ (C i).dom), ?_, ?_, ?_⟩
  · ext Q
    rw [Finsupp.finsetSum_apply]
    simp only [Finsupp.filter_apply]
    rcases hcover Q with ⟨i, hi, huniq, -⟩ | ⟨e, he, -, hnot⟩
    · rw [Finset.sum_eq_single i]
      · rw [if_pos hi]
      · intro j _ hji
        rw [if_neg]
        exact fun hj => hji (huniq j hj)
      · intro habs; exact absurd (Finset.mem_univ i) habs
    · have h0 : (Dg - (Finsupp.single P' 1 - Finsupp.single P 1) : Divisor L F) Q = 0 := by
        rw [Finsupp.sub_apply, hann e Q he, sub_self]
      rw [h0]
      symm
      refine Finset.sum_eq_zero fun j _ => ?_
      rw [if_neg (hnot j)]
  · intro i Q hQ
    rw [Finsupp.mem_support_iff, Finsupp.filter_apply] at hQ
    by_contra hc
    exact hQ (if_neg hc)
  · intro i
    obtain ⟨hgi, hgi0, hginode⟩ := hgres i

    set Di : Divisor L F := (Dg - (Finsupp.single P' 1 - Finsupp.single P 1)).filter
      (fun Q => Q ∈ (C i).dom) with hDi
    have hPdom : P ∉ (C i).dom := by
      rcases hcover P with ⟨j, -, -, hnot⟩ | ⟨e, -, -, hnot⟩
      · exact absurd hP (hnot e₀)
      · exact hnot i
    have hP'dom : P' ∉ (C i).dom := by
      rcases hcover P' with ⟨j, -, -, hnot⟩ | ⟨e, -, -, hnot⟩
      · exact absurd hP' (hnot e₀)
      · exact hnot i
    have hDi_dom : ∀ Q ∈ (C i).dom, Di Q = Q.ord g := by
      intro Q hQ
      rw [hDi, Finsupp.filter_apply, if_pos hQ, Finsupp.sub_apply, Finsupp.sub_apply, Finsupp.single_apply,
        Finsupp.single_apply, hDg, if_neg (fun h0 : P' = Q => hP'dom (h0 ▸ hQ)),
        if_neg (fun h0 : P = Q => hPdom (h0 ▸ hQ))]
      ring
    have hDi_off : ∀ Q, Q ∉ (C i).dom → Di Q = 0 := by
      intro Q hQ; rw [hDi, Finsupp.filter_apply, if_neg hQ]
    have hDi_supp : ∀ Q ∈ Di.support, Q ∈ (C i).dom := by
      intro Q hQ; by_contra hc; exact (Finsupp.mem_support_iff.mp hQ) (hDi_off Q hc)

    have hmap := (C i).mapDomain_placeMap ⟨g, hgi⟩ hgi0 Di hDi_dom hDi_off
    obtain ⟨Dbar, hDbar, hDbardeg⟩ :=
      HasPrincipalDivisors.exists_divisor (K := IsLocalRing.ResidueField A) ((C i).residue ⟨g, hgi⟩) hgi0
    have hmapD : Finsupp.mapDomain (C i).placeMap Di = Dbar := by
      ext y
      by_cases hy : y ∈ (C i).nodes
      ·
        obtain ⟨hyreg, hyval⟩ := hginode y hy
        rw [hDbar, y.ord_eq_zero_of_evalAt_ne_zero hyreg hyval, Finsupp.mapDomain, Finsupp.sum_apply]
        refine Finset.sum_eq_zero fun Q hQ => ?_
        dsimp only
        rw [Finsupp.single_apply, if_neg]
        intro hQy
        exact (C i).placeMap_not_mem_nodes Q (hDi_supp Q hQ) (hQy ▸ hy)
      · rw [hmap y hy, hDbar]

    have hdegDi : Divisor.degree Di = Di.sum fun _ k => k := by
      rw [Divisor.degree, Finsupp.liftAddHom_apply]
      refine Finsupp.sum_congr fun Q hQ => ?_
      rw [AddMonoidHom.mulRight_apply, Place.deg_eq_one_of_isRational' (hratF i Q (hDi_supp Q hQ))]
      simp
    have hdegDbar : Divisor.degree Dbar = Dbar.sum fun _ k => k := by
      rw [Divisor.degree, Finsupp.liftAddHom_apply]
      refine Finsupp.sum_congr fun y _ => ?_
      rw [AddMonoidHom.mulRight_apply, Place.deg_eq_one_of_isRational' (hratBar i y)]
      simp
    have hsum : (Di.sum fun _ k => k) = Dbar.sum fun _ k => k := by
      rw [← hmapD, Finsupp.sum_mapDomain_index (fun _ => rfl) (fun _ _ _ => rfl)]
    rw [hdegDi, hsum, ← hdegDbar, hDbardeg]

end S_AlgebraicCurve_SemistableCovering_ord_eq_single_sub_single_of_forall_residue_evalAt_ne_zero_of_rankOne
end P2MW
export P2MW.S_AlgebraicCurve_SemistableCovering_ord_eq_single_sub_single_of_forall_residue_evalAt_ne_zero_of_rankOne (solution)
