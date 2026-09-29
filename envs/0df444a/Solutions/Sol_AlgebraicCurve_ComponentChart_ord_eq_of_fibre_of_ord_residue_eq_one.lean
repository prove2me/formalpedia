-- Prove2me | solution 1 for AlgebraicCurve.ComponentChart.ord_eq_of_fibre_of_ord_residue_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/2161dc13-c257-5e32-a6a3-aaa4f7236e89

import Definitions.Def_AlgebraicCurve_SemistableCharts
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_ComponentChart_ord_eq_of_fibre_of_ord_residue_eq_one

set_option autoImplicit false

p2m_open "AlgebraicCurve P2MW.S_AlgebraicCurve_ComponentChart_ord_eq_of_fibre_of_ord_residue_eq_one.AlgebraicCurve IsLocalRing"

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "ComponentChart Place Divisor HasPrincipalDivisors HasPrincipalDivisors.exists_divisor"
p2m_open "AlgebraicCurve"

variable {L : Type*} [Field L] {A : ValuationSubring L} {F : Type*} [Field F] [Algebra L F]
variable {Fbar : Type*} [Field Fbar] [Algebra (IsLocalRing.ResidueField A) Fbar]

namespace Place p2m_export "AlgebraicCurve.Place" "ResidueField ord toValuationSubring adicValuation_le_one_of_mem adicValuation_le_one_iff" end Place
namespace Place
p2m_open_scoped "AlgebraicCurve.Place" in

private theorem _root_.AlgebraicCurve.Place.ord_nonneg_of_mem_toValuationSubring (v : Place L F) {f : F}
    (hf : f ∈ v.toValuationSubring) : 0 ≤ v.ord f := by
  rcases (v.adicValuation_le_one_iff).1 (v.adicValuation_le_one_of_mem hf) with h | h
  · simp [h]
  · exact h

end Place
p2m_export "AlgebraicCurve" "Place.ord_nonneg_of_mem_toValuationSubring"
end AlgebraicCurve

theorem solution
    {L : Type*} [Field L] {A : ValuationSubring L} {F : Type*} [Field F] [Algebra L F]
    {Fbar : Type*} [Field Fbar] [Algebra (ResidueField A) Fbar]
    [HasPrincipalDivisors L F] (C : ComponentChart A F Fbar)
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
    exact w.ord_nonneg_of_mem_toValuationSubring (hreg w hwdom hw.2)
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

end S_AlgebraicCurve_ComponentChart_ord_eq_of_fibre_of_ord_residue_eq_one
end P2MW
export P2MW.S_AlgebraicCurve_ComponentChart_ord_eq_of_fibre_of_ord_residue_eq_one (solution)
