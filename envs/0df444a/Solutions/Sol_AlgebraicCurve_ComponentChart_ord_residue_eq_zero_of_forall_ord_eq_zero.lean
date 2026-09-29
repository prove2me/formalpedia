-- Prove2me | solution 1 for AlgebraicCurve.ComponentChart.ord_residue_eq_zero_of_forall_ord_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/b3907a54-9167-5837-a41d-46d7acf53c23

import Definitions.Def_AlgebraicCurve_SemistableCharts
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_ComponentChart_ord_residue_eq_zero_of_forall_ord_eq_zero

set_option autoImplicit false

open AlgebraicCurve IsLocalRing

theorem solution
    {L : Type*} [Field L] (A : ValuationSubring L)
    {F : Type*} [Field F] [Algebra L F] [HasPrincipalDivisors L F]
    {Fbar : Type*} [Field Fbar] [Algebra (ResidueField A) Fbar]
    (C : ComponentChart A F Fbar) (f : F) (hf : f ∈ C.integers) (hres : C.residue ⟨f, hf⟩ ≠ 0)
    (Q : Place (ResidueField A) Fbar) (hQ : Q ∉ C.nodes)
    (hord : ∀ P ∈ C.dom, C.placeMap P = Q → P.ord f = 0) :
    Q.ord (C.residue ⟨f, hf⟩) = 0 := by
  classical
  have hf0 : f ≠ 0 := by
    intro h0
    apply hres
    have : (⟨f, hf⟩ : C.integers) = 0 := Subtype.ext h0
    rw [this, map_zero]
  obtain ⟨D, hD, -⟩ := HasPrincipalDivisors.exists_divisor (K := L) (F := F) f hf0
  set Ddom : Divisor L F := D.filter (· ∈ C.dom) with hDdom
  have h1 : ∀ P ∈ C.dom, Ddom P = P.ord ((⟨f, hf⟩ : C.integers) : F) := by
    intro P hP
    rw [hDdom, Finsupp.filter_apply_pos (· ∈ C.dom) D hP, hD P]
  have h2 : ∀ P, P ∉ C.dom → Ddom P = 0 := by
    intro P hP
    rw [hDdom, Finsupp.filter_apply_neg (· ∈ C.dom) D hP]
  have hmap := C.mapDomain_placeMap ⟨f, hf⟩ hres Ddom h1 h2 Q hQ
  rw [← hmap, Finsupp.mapDomain, Finsupp.sum_apply]

  refine Finset.sum_eq_zero fun P hP => ?_
  show Finsupp.single (C.placeMap P) (Ddom P) Q = 0
  rw [Finsupp.single_apply]
  split_ifs with hPQ
  · have hPdom : P ∈ C.dom := by
      by_contra hn
      exact (Finsupp.mem_support_iff.mp hP) (h2 P hn)
    rw [h1 P hPdom]
    exact hord P hPdom hPQ
  · rfl

end S_AlgebraicCurve_ComponentChart_ord_residue_eq_zero_of_forall_ord_eq_zero
end P2MW
export P2MW.S_AlgebraicCurve_ComponentChart_ord_residue_eq_zero_of_forall_ord_eq_zero (solution)
