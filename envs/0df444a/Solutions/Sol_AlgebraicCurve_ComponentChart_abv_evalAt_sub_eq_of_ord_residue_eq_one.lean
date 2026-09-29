-- Prove2me | solution 1 for AlgebraicCurve.ComponentChart.abv_evalAt_sub_eq_of_ord_residue_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/0e2da14a-cfe1-5120-a40d-e03d98780036

import Definitions.Def_AlgebraicCurve_SemistableCharts
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_ComponentChart_abv_evalAt_sub_eq_of_ord_residue_eq_one

set_option autoImplicit false

p2m_open "AlgebraicCurve P2MW.S_AlgebraicCurve_ComponentChart_abv_evalAt_sub_eq_of_ord_residue_eq_one.AlgebraicCurve IsLocalRing"

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "ComponentChart Place Divisor HasPrincipalDivisors HasPrincipalDivisors.exists_divisor"
p2m_open "AlgebraicCurve"

variable {L : Type*} [Field L] {A : ValuationSubring L} {F : Type*} [Field F] [Algebra L F]
variable {Fbar : Type*} [Field Fbar] [Algebra (IsLocalRing.ResidueField A) Fbar]

namespace Place p2m_export "AlgebraicCurve.Place" "ext coe_algebraMap ResidueField ord ord_mul ord_inv ord_coe_unit exists_unit_mul_zpow algebraMap_mem' toValuationSubring adicValuation_le_one_of_mem adicValuation_le_one_iff IsRational algebraMap_residueField_injective residueInv_algebraMap evalAt evalAt_of_mem algebraMap_evalAt" end Place
namespace Place
p2m_open_scoped "AlgebraicCurve.Place" in

private theorem _root_.AlgebraicCurve.Place.evalAt_mul' {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)
    (hv : v.IsRational) {f g : F} (hf : f ∈ v.toValuationSubring) (hg : g ∈ v.toValuationSubring) :
    v.evalAt (f * g) = v.evalAt f * v.evalAt g := by
  apply v.algebraMap_residueField_injective
  rw [v.algebraMap_evalAt hv (mul_mem hf hg), map_mul, v.algebraMap_evalAt hv hf,
    v.algebraMap_evalAt hv hg, ← map_mul]
  rfl

end Place
p2m_export "AlgebraicCurve" "Place.evalAt_mul'"
namespace Place
p2m_open_scoped "AlgebraicCurve.Place" in

private theorem _root_.AlgebraicCurve.Place.evalAt_algebraMap' {K F : Type*} [Field K] [Field F] [Algebra K F]
    (v : Place K F) (a : K) : v.evalAt (algebraMap K F a) = a := by
  rw [v.evalAt_of_mem (v.algebraMap_mem' a)]
  have h : (⟨algebraMap K F a, v.algebraMap_mem' a⟩ : v.toValuationSubring)
      = algebraMap K v.toValuationSubring a := Subtype.ext (v.coe_algebraMap a).symm
  rw [h, ← IsLocalRing.ResidueField.algebraMap_eq, ← IsScalarTower.algebraMap_apply,
    v.residueInv_algebraMap]

end Place
p2m_export "AlgebraicCurve" "Place.evalAt_algebraMap'"
namespace Place
p2m_open_scoped "AlgebraicCurve.Place" in

private theorem _root_.AlgebraicCurve.Place.evalAt_sub' {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)
    (hv : v.IsRational) {f g : F} (hf : f ∈ v.toValuationSubring) (hg : g ∈ v.toValuationSubring) :
    v.evalAt (f - g) = v.evalAt f - v.evalAt g := by
  apply v.algebraMap_residueField_injective
  rw [v.algebraMap_evalAt hv (sub_mem hf hg), map_sub, v.algebraMap_evalAt hv hf,
    v.algebraMap_evalAt hv hg, ← map_sub]
  rfl

end Place
p2m_export "AlgebraicCurve" "Place.evalAt_sub'"
namespace Place
p2m_open_scoped "AlgebraicCurve.Place" in

private theorem _root_.AlgebraicCurve.Place.ord_nonneg_of_mem' {K F : Type*} [Field K] [Field F] [Algebra K F]
    (v : Place K F) {f : F} (hf : f ∈ v.toValuationSubring) : 0 ≤ v.ord f := by
  rcases (v.adicValuation_le_one_iff).1 (v.adicValuation_le_one_of_mem hf) with h | h
  · simp [h]
  · exact h

end Place
p2m_export "AlgebraicCurve" "Place.ord_nonneg_of_mem'"
namespace Place
p2m_open_scoped "AlgebraicCurve.Place" in

private theorem _root_.AlgebraicCurve.Place.isUnit_of_ord_eq_zero' {K F : Type*} [Field K] [Field F] [Algebra K F]
    (v : Place K F) {f : F} (hf : f ∈ v.toValuationSubring) (hf0 : f ≠ 0) (h : v.ord f = 0) :
    IsUnit (⟨f, hf⟩ : v.toValuationSubring) := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  obtain ⟨u, hu⟩ := v.exists_unit_mul_zpow hf0 hϖ
  rw [h, zpow_zero, mul_one] at hu
  have : (⟨f, hf⟩ : v.toValuationSubring) = u := Subtype.ext hu
  rw [this]
  exact Units.isUnit u

end Place
p2m_export "AlgebraicCurve" "Place.isUnit_of_ord_eq_zero'"

private theorem inv_mem_of_isUnit' {F : Type*} [Field F] {O : ValuationSubring F} {x : F}
    (hx : x ∈ O) (hu : IsUnit (⟨x, hx⟩ : O)) : x⁻¹ ∈ O := by
  obtain ⟨u, hu⟩ := hu
  have hx0 : x ≠ 0 := by
    rintro rfl
    have : (u : O) = 0 := by rw [hu]; rfl
    exact u.ne_zero this
  have hval : ((u⁻¹ : Oˣ) : O).1 = x⁻¹ := by
    have h1 := congrArg (fun t : O => (t : F)) u.mul_inv
    simp only [Subring.coe_mul, OneMemClass.coe_one] at h1
    rw [hu] at h1
    exact (eq_inv_of_mul_eq_one_right h1)
  exact hval ▸ ((u⁻¹ : Oˣ) : O).2

namespace Place
p2m_open_scoped "AlgebraicCurve.Place" in

private theorem _root_.AlgebraicCurve.Place.ord_pos_of_evalAt_eq_zero' {K F : Type*} [Field K] [Field F] [Algebra K F]
    (v : Place K F) (hv : v.IsRational) {f : F} (hf : f ∈ v.toValuationSubring) (hf0 : f ≠ 0)
    (h : v.evalAt f = 0) : 0 < v.ord f := by
  rcases (v.ord_nonneg_of_mem' hf).eq_or_lt with h0 | h0
  · exfalso
    have hu := v.isUnit_of_ord_eq_zero' hf hf0 h0.symm
    have hres : IsLocalRing.residue v.toValuationSubring ⟨f, hf⟩ = 0 := by
      rw [← v.algebraMap_evalAt hv hf, h, map_zero]
    rw [IsLocalRing.residue_eq_zero_iff] at hres
    exact (IsLocalRing.mem_maximalIdeal _).1 hres hu
  · exact h0

end Place
p2m_export "AlgebraicCurve" "Place.ord_pos_of_evalAt_eq_zero'"
namespace Place
p2m_open_scoped "AlgebraicCurve.Place" in

private theorem _root_.AlgebraicCurve.Place.residue_ne_zero_of_ord_eq_zero' {K F : Type*} [Field K] [Field F] [Algebra K F]
    (v : Place K F) {f : F} (hf : f ∈ v.toValuationSubring) (hf0 : f ≠ 0) (h : v.ord f = 0) :
    IsLocalRing.residue v.toValuationSubring ⟨f, hf⟩ ≠ 0 := by
  intro h0
  rw [IsLocalRing.residue_eq_zero_iff] at h0
  exact (IsLocalRing.mem_maximalIdeal _).1 h0 (v.isUnit_of_ord_eq_zero' hf hf0 h)

end Place
p2m_export "AlgebraicCurve" "Place.residue_ne_zero_of_ord_eq_zero'"

private theorem abv_eq_one_of_isUnit_vs {L : Type*} [Field L] {A : ValuationSubring L}
    (μ : AbsoluteValue L ℝ) (hμA : ∀ a : L, a ∈ A ↔ μ a ≤ 1) {a : L} (ha : a ∈ A)
    (hu : IsUnit (⟨a, ha⟩ : A)) : μ a = 1 := by
  obtain ⟨b, hb⟩ := hu.exists_right_inv
  have hb' : a * (b : L) = 1 := by
    have := congrArg (fun t : A => (t : L)) hb
    simpa using this
  have h1 : μ a * μ (b : L) = 1 := by rw [← map_mul, hb', map_one]
  have ha1 : μ a ≤ 1 := (hμA a).1 ha
  have hb1 : μ (b : L) ≤ 1 := (hμA (b : L)).1 b.2
  have ha0 : 0 ≤ μ a := μ.nonneg a
  exact le_antisymm ha1 (by nlinarith)

namespace ComponentChart p2m_export "AlgebraicCurve.ComponentChart" "integers placeMap residue pointwise ker_residue mapDomain_placeMap placeMap_not_mem_nodes dom" end ComponentChart
namespace ComponentChart
p2m_open_scoped "AlgebraicCurve.ComponentChart" in

private theorem _root_.AlgebraicCurve.ComponentChart.ord_eq_of_fibre' [HasPrincipalDivisors L F] (C : ComponentChart A F Fbar)
    (f : F) (hf : f ∈ C.integers) (hres : C.residue ⟨f, hf⟩ ≠ 0)
    (P : Place L F) (hP : P ∈ C.dom) (hord : (C.placeMap P).ord (C.residue ⟨f, hf⟩) = 1)
    (hreg : ∀ w ∈ C.dom, C.placeMap w = C.placeMap P → f ∈ w.toValuationSubring)
    (hPz : 0 < P.ord f) :
    P.ord f = 1 ∧ ∀ w ∈ C.dom, C.placeMap w = C.placeMap P → w ≠ P → w.ord f = 0 := by
  classical
  have hf0 : f ≠ 0 := by
    rintro rfl
    have h0 : (⟨(0 : F), hf⟩ : C.integers) = 0 := rfl
    rw [h0, map_zero] at hres
    exact hres rfl
  obtain ⟨D, hD, -⟩ := HasPrincipalDivisors.exists_divisor (K := L) f hf0

  set D' : Divisor L F := D.filter (· ∈ C.dom) with hD'
  have hD'dom : ∀ Q ∈ C.dom, D' Q = Q.ord f := by
    intro Q hQ
    rw [hD', Finsupp.filter_apply_pos _ _ hQ, hD]
  have hD'off : ∀ Q, Q ∉ C.dom → D' Q = 0 := by
    intro Q hQ
    rw [hD', Finsupp.filter_apply_neg _ _ hQ]
  have hpush := C.mapDomain_placeMap ⟨f, hf⟩ hres D' hD'dom hD'off (C.placeMap P)
    (C.placeMap_not_mem_nodes P hP)
  rw [hord] at hpush

  have hsum : Finsupp.mapDomain C.placeMap D' (C.placeMap P)
      = ∑ w ∈ D'.support with C.placeMap w = C.placeMap P, D' w := by
    rw [Finsupp.mapDomain, Finsupp.sum_apply, Finsupp.sum, Finset.sum_filter]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [Finsupp.single_apply]
  rw [hsum] at hpush

  have hnn : ∀ w ∈ D'.support.filter (fun w => C.placeMap w = C.placeMap P), 0 ≤ D' w := by
    intro w hw
    rw [Finset.mem_filter] at hw
    have hwdom : w ∈ C.dom := by
      by_contra h
      exact (Finsupp.mem_support_iff.1 hw.1) (hD'off w h)
    rw [hD'dom w hwdom]
    exact w.ord_nonneg_of_mem' (hreg w hwdom hw.2)
  have hPmem : P ∈ D'.support.filter (fun w => C.placeMap w = C.placeMap P) := by
    rw [Finset.mem_filter, Finsupp.mem_support_iff, hD'dom P hP]
    exact ⟨hPz.ne', rfl⟩
  have hPle : D' P ≤ 1 := by
    rw [← hpush]
    exact Finset.single_le_sum hnn hPmem
  have hDP : D' P = P.ord f := hD'dom P hP
  have hP1 : P.ord f = 1 := le_antisymm (hDP ▸ hPle) hPz
  refine ⟨hP1, ?_⟩
  intro w hw hfib hne

  have hrest : ∑ v ∈ (D'.support.filter (fun w => C.placeMap w = C.placeMap P)).erase P, D' v = 0 := by
    have := Finset.add_sum_erase _ (fun v => D' v) hPmem
    rw [hpush, hDP, hP1] at this
    linarith
  by_cases hws : w ∈ D'.support
  · have hwmem : w ∈ (D'.support.filter (fun w => C.placeMap w = C.placeMap P)).erase P := by
      rw [Finset.mem_erase, Finset.mem_filter]
      exact ⟨hne, hws, hfib⟩
    have := (Finset.sum_eq_zero_iff_of_nonneg (fun v hv => hnn v (Finset.mem_of_mem_erase hv))).1
      hrest w hwmem
    rwa [hD'dom w hw] at this
  · have := Finsupp.notMem_support_iff.1 hws
    rwa [hD'dom w hw] at this

end ComponentChart
p2m_export "AlgebraicCurve" "ComponentChart.ord_eq_of_fibre'"
end AlgebraicCurve

theorem solution
    {L : Type*} [Field L] {A : ValuationSubring L} {F : Type*} [Field F] [Algebra L F]
    {Fbar : Type*} [Field Fbar] [Algebra (ResidueField A) Fbar]
    [HasPrincipalDivisors L F] (C : ComponentChart A F Fbar)
    (μ : AbsoluteValue L ℝ) (hμA : ∀ a : L, a ∈ A ↔ μ a ≤ 1)
    (P : Place L F) (hP : P ∈ C.dom) (hrat : ∀ w ∈ C.dom, w.IsRational)
    (ρ T : F)
    (hρ : ρ - algebraMap L F (P.evalAt ρ) ∈ C.integers) (hρ0 : C.residue ⟨_, hρ⟩ ≠ 0)
    (hρ1 : (C.placeMap P).ord (C.residue ⟨_, hρ⟩) = 1)
    (hρreg : ∀ w ∈ C.dom, C.placeMap w = C.placeMap P → ρ ∈ w.toValuationSubring)
    (hT : T - algebraMap L F (P.evalAt T) ∈ C.integers) (hT0 : C.residue ⟨_, hT⟩ ≠ 0)
    (hT1 : (C.placeMap P).ord (C.residue ⟨_, hT⟩) = 1)
    (hTreg : ∀ w ∈ C.dom, C.placeMap w = C.placeMap P → T ∈ w.toValuationSubring) :
    ∀ Q ∈ C.dom, C.placeMap Q = C.placeMap P →
      μ (Q.evalAt T - P.evalAt T) = μ (Q.evalAt ρ - P.evalAt ρ) := by
  classical
  intro Q hQ hfib

  set ρ' : F := ρ - algebraMap L F (P.evalAt ρ) with hρ'
  set T' : F := T - algebraMap L F (P.evalAt T) with hT'
  have hPrat : P.IsRational := hrat P hP
  have hQrat : Q.IsRational := hrat Q hQ

  have hρ'reg : ∀ w ∈ C.dom, C.placeMap w = C.placeMap P → ρ' ∈ w.toValuationSubring :=
    fun w hw hw' => sub_mem (hρreg w hw hw') (w.algebraMap_mem' _)
  have hT'reg : ∀ w ∈ C.dom, C.placeMap w = C.placeMap P → T' ∈ w.toValuationSubring :=
    fun w hw hw' => sub_mem (hTreg w hw hw') (w.algebraMap_mem' _)
  have hρ'0 : ρ' ≠ 0 := by
    intro h0
    apply hρ0
    have : (⟨ρ', hρ⟩ : C.integers) = 0 := Subtype.ext h0
    rw [this, map_zero]
  have hT'0 : T' ≠ 0 := by
    intro h0
    apply hT0
    have : (⟨T', hT⟩ : C.integers) = 0 := Subtype.ext h0
    rw [this, map_zero]
  have hρ'P : P.evalAt ρ' = 0 := by
    rw [hρ', P.evalAt_sub' hPrat (hρreg P hP rfl) (P.algebraMap_mem' _), P.evalAt_algebraMap', sub_self]
  have hT'P : P.evalAt T' = 0 := by
    rw [hT', P.evalAt_sub' hPrat (hTreg P hP rfl) (P.algebraMap_mem' _), P.evalAt_algebraMap', sub_self]
  have hρ'pos : 0 < P.ord ρ' := P.ord_pos_of_evalAt_eq_zero' hPrat (hρ'reg P hP rfl) hρ'0 hρ'P
  have hT'pos : 0 < P.ord T' := P.ord_pos_of_evalAt_eq_zero' hPrat (hT'reg P hP rfl) hT'0 hT'P
  obtain ⟨hρ'1, hρ'off⟩ := C.ord_eq_of_fibre' ρ' hρ hρ0 P hP hρ1 hρ'reg hρ'pos
  obtain ⟨hT'1, hT'off⟩ := C.ord_eq_of_fibre' T' hT hT0 P hP hT1 hT'reg hT'pos

  have hTQ : Q.evalAt T - P.evalAt T = Q.evalAt T' := by
    rw [hT', Q.evalAt_sub' hQrat (hTreg Q hQ hfib) (Q.algebraMap_mem' _), Q.evalAt_algebraMap']
  have hρQ : Q.evalAt ρ - P.evalAt ρ = Q.evalAt ρ' := by
    rw [hρ', Q.evalAt_sub' hQrat (hρreg Q hQ hfib) (Q.algebraMap_mem' _), Q.evalAt_algebraMap']
  rw [hTQ, hρQ]
  by_cases hQP : Q = P
  · subst hQP
    rw [hρ'P, hT'P]

  have hρ'unitC : IsUnit (⟨ρ', hρ⟩ : C.integers) := by
    by_contra hnu
    apply hρ0
    have : (⟨ρ', hρ⟩ : C.integers) ∈ RingHom.ker C.residue := by
      rw [C.ker_residue]
      exact (IsLocalRing.mem_maximalIdeal _).2 hnu
    exact this
  have hρ'invC : ρ'⁻¹ ∈ C.integers := inv_mem_of_isUnit' hρ hρ'unitC
  set q : F := T' * ρ'⁻¹ with hq
  have hqC : q ∈ C.integers := mul_mem hT hρ'invC
  have hqρ : q * ρ' = T' := by rw [hq, inv_mul_cancel_right₀ hρ'0]

  have hresq : C.residue ⟨q, hqC⟩ * C.residue ⟨ρ', hρ⟩ = C.residue ⟨T', hT⟩ := by
    rw [← map_mul]
    congr 1
    exact Subtype.ext hqρ
  have hresq' : C.residue ⟨q, hqC⟩ = C.residue ⟨T', hT⟩ * (C.residue ⟨ρ', hρ⟩)⁻¹ :=
    (eq_mul_inv_iff_mul_eq₀ hρ0).2 hresq
  have hresq0 : C.residue ⟨q, hqC⟩ ≠ 0 := by
    rw [hresq']
    exact mul_ne_zero hT0 (inv_ne_zero hρ0)
  have hordq : (C.placeMap P).ord (C.residue ⟨q, hqC⟩) = 0 := by
    rw [hresq', (C.placeMap P).ord_mul hT0 (inv_ne_zero hρ0), (C.placeMap P).ord_inv, hT1, hρ1]
    ring

  have hqreg : ∀ w ∈ C.dom, C.placeMap w = C.placeMap P → q ∈ w.toValuationSubring ∧ w.ord q = 0 := by
    intro w hw hw'
    by_cases hwP : w = P
    · subst hwP
      obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible w.toValuationSubring
      obtain ⟨u1, hu1⟩ := w.exists_unit_mul_zpow hT'0 hϖ
      obtain ⟨u2, hu2⟩ := w.exists_unit_mul_zpow hρ'0 hϖ
      rw [hT'1] at hu1
      rw [hρ'1] at hu2
      have hϖ0 : (ϖ : F) ≠ 0 := by
        simpa [ne_eq, ZeroMemClass.coe_eq_zero] using hϖ.ne_zero
      have hinvcoe : (((u2⁻¹ : w.toValuationSubringˣ) : w.toValuationSubring) : F)
          = ((((u2 : w.toValuationSubringˣ) : w.toValuationSubring) : F))⁻¹ := by
        apply eq_inv_of_mul_eq_one_right
        have h1 := congrArg (fun t : w.toValuationSubring => (t : F)) u2.mul_inv
        simp only [MulMemClass.coe_mul, OneMemClass.coe_one] at h1
        exact h1
      have hqu : q = ((u1 * u2⁻¹ : w.toValuationSubringˣ) : w.toValuationSubring) := by
        rw [hq, hu1, hu2]
        push_cast
        rw [hinvcoe]
        field_simp
      refine ⟨hqu ▸ ((u1 * u2⁻¹ : w.toValuationSubringˣ) : w.toValuationSubring).2, ?_⟩
      rw [hqu]
      exact w.ord_coe_unit _
    · have hρw : w.ord ρ' = 0 := hρ'off w hw hw' hwP
      have hTw : w.ord T' = 0 := hT'off w hw hw' hwP
      have hρ'unitw := w.isUnit_of_ord_eq_zero' (hρ'reg w hw hw') hρ'0 hρw
      refine ⟨mul_mem (hT'reg w hw hw') (inv_mem_of_isUnit' _ hρ'unitw), ?_⟩
      rw [hq, w.ord_mul hT'0 (inv_ne_zero hρ'0), w.ord_inv, hTw, hρw]
      ring

  obtain ⟨hm, hqA, hcomp⟩ := C.pointwise Q hQ hQrat q hqC (fun w hw hw' => (hqreg w hw (hw'.trans hfib)).1)
  have hq0 : q ≠ 0 := mul_ne_zero hT'0 (inv_ne_zero hρ'0)
  have hunitA : IsUnit (⟨Q.evalAt q, hqA⟩ : A) := by
    by_contra hnu
    have hmax : (⟨Q.evalAt q, hqA⟩ : A) ∈ IsLocalRing.maximalIdeal A := (IsLocalRing.mem_maximalIdeal _).2 hnu
    have hz : IsLocalRing.residue A ⟨Q.evalAt q, hqA⟩ = 0 := (IsLocalRing.residue_eq_zero_iff _).2 hmax
    rw [hz, map_zero] at hcomp

    have hbar := (C.placeMap Q).residue_ne_zero_of_ord_eq_zero' hm hresq0 (hfib ▸ hordq)
    exact hbar hcomp.symm
  have hμq : μ (Q.evalAt q) = 1 := abv_eq_one_of_isUnit_vs μ hμA hqA hunitA

  have hTq : Q.evalAt T' = Q.evalAt q * Q.evalAt ρ' := by
    rw [← Q.evalAt_mul' hQrat (hqreg Q hQ hfib).1 (hρ'reg Q hQ hfib), hqρ]
  rw [hTq, map_mul, hμq, one_mul]

end S_AlgebraicCurve_ComponentChart_abv_evalAt_sub_eq_of_ord_residue_eq_one
end P2MW
export P2MW.S_AlgebraicCurve_ComponentChart_abv_evalAt_sub_eq_of_ord_residue_eq_one (solution)
