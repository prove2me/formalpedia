-- Prove2me | solution 1 for AlgebraicCurve.RegularProlongation.ord_residue_nonneg_of_degreeOn_of_forall_ord_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/b6ba36aa-51d7-53c7-9d2f-f961087392d0

import Mathlib
import Definitions.Def_AlgebraicCurve_ResidueDiscs
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_RegularProlongation_ord_residue_nonneg_of_degreeOn_of_forall_ord_nonneg

set_option autoImplicit false

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "RegularProlongation Place"
namespace RegularProlongation
p2m_export "AlgebraicCurve.RegularProlongation" "DegreeOn integers residue"
namespace NodeNotDisc
p2m_open "AlgebraicCurve.RegularProlongation AlgebraicCurve"

open IsLocalRing

theorem main
    {L : Type*} [Field L] {A : ValuationSubring L} {F : Type*} [Field F] [Algebra L F]
    {Fbar : Type*} [Field Fbar] [Algebra (ResidueField A) Fbar]
    (R : AlgebraicCurve.RegularProlongation A F Fbar) (Q : AlgebraicCurve.Place (ResidueField A) Fbar)
    (D : Set (AlgebraicCurve.Place L F))
    (hdeg : R.DegreeOn Q D)
    (f : R.integers) (hres : R.residue f ≠ 0)
    (hfin : {P : AlgebraicCurve.Place L F | P.ord (f : F) ≠ 0}.Finite)
    (hD : ∀ P ∈ D, 0 ≤ P.ord (f : F)) :
    0 ≤ Q.ord (R.residue f) := by
  classical

  let g : AlgebraicCurve.Place L F → ℤ := fun P => if P ∈ D then P.ord (f : F) else 0
  have hg_supp : ∀ P, g P ≠ 0 → P ∈ hfin.toFinset := by
    intro P hP
    rw [Set.Finite.mem_toFinset]
    show P.ord (f : F) ≠ 0
    intro h0
    apply hP
    simp only [g, h0, ite_self]
  let D' : AlgebraicCurve.Place L F →₀ ℤ := Finsupp.onFinset hfin.toFinset g hg_supp
  have hD'apply : ∀ P, D' P = g P := fun P => Finsupp.onFinset_apply
  have h1 : ∀ P ∈ D, D' P = P.ord (f : F) := by
    intro P hP
    rw [hD'apply]
    simp only [g, if_pos hP]
  have h2 : ∀ P, P ∉ D → D' P = 0 := by
    intro P hP
    rw [hD'apply]
    simp only [g, if_neg hP]
  have hsum : D'.sum (fun _ n => n) = Q.ord (R.residue f) := hdeg f hres D' h1 h2
  rw [← hsum]
  apply Finset.sum_nonneg
  intro P _
  rw [hD'apply]
  simp only [g]
  split_ifs with hP
  · exact hD P hP
  · exact le_rfl

end AlgebraicCurve.RegularProlongation.NodeNotDisc

open IsLocalRing in
theorem solution
    {L : Type*} [Field L] {A : ValuationSubring L} {F : Type*} [Field F] [Algebra L F]
    {Fbar : Type*} [Field Fbar] [Algebra (ResidueField A) Fbar]
    (R : AlgebraicCurve.RegularProlongation A F Fbar) (Q : AlgebraicCurve.Place (ResidueField A) Fbar)
    (D : Set (AlgebraicCurve.Place L F))
    (hdeg : R.DegreeOn Q D)
    (f : R.integers) (hres : R.residue f ≠ 0)

    (hfin : {P : AlgebraicCurve.Place L F | P.ord (f : F) ≠ 0}.Finite)

    (hD : ∀ P ∈ D, 0 ≤ P.ord (f : F)) :
    0 ≤ Q.ord (R.residue f) :=
  AlgebraicCurve.RegularProlongation.NodeNotDisc.main R Q D hdeg f hres hfin hD

end S_AlgebraicCurve_RegularProlongation_ord_residue_nonneg_of_degreeOn_of_forall_ord_nonneg
end P2MW
export P2MW.S_AlgebraicCurve_RegularProlongation_ord_residue_nonneg_of_degreeOn_of_forall_ord_nonneg (solution)
