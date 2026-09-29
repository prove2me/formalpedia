-- Prove2me | solution 1 for AlgebraicCurve.Annulus.abv_evalAt_lt_one_of_isAttached_of_ord_residue_pos
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/4660d0eb-ac31-580b-8b36-a54509a16244

import Definitions.Def_AlgebraicCurve_SemistableCharts
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_Annulus_abv_evalAt_lt_one_of_isAttached_of_ord_residue_pos

set_option autoImplicit false

p2m_open "AlgebraicCurve P2MW.S_AlgebraicCurve_Annulus_abv_evalAt_lt_one_of_isAttached_of_ord_residue_pos.AlgebraicCurve IsLocalRing"

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "ComponentChart Annulus Place"
p2m_open "AlgebraicCurve"

private theorem abv_eq_one_of_isUnit_valuationSubring {L : Type*} [Field L] {A : ValuationSubring L}
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

private theorem abv_lt_one_of_mem_maximalIdeal_valuationSubring {L : Type*} [Field L]
    {A : ValuationSubring L} (μ : AbsoluteValue L ℝ) (hμA : ∀ a : L, a ∈ A ↔ μ a ≤ 1) {a : L}
    (ha : a ∈ A) (hm : (⟨a, ha⟩ : A) ∈ maximalIdeal A) : μ a < 1 := by
  have ha1 : μ a ≤ 1 := (hμA a).1 ha
  refine lt_of_le_of_ne ha1 fun h1 => ?_
  apply (IsLocalRing.mem_maximalIdeal _).1 hm
  have ha0 : a ≠ 0 := fun h0 => by simp [h0] at h1
  have hinv : a⁻¹ ∈ A := (hμA _).2 (by rw [map_inv₀, h1, inv_one])
  exact isUnit_iff_exists_inv.2 ⟨⟨a⁻¹, hinv⟩, Subtype.ext (mul_inv_cancel₀ ha0)⟩

end AlgebraicCurve

theorem solution
    {L : Type*} [Field L] {A : ValuationSubring L} {F : Type*} [Field F] [Algebra L F]
    {Fbar : Type*} [Field Fbar] [Algebra (ResidueField A) Fbar]
    (μ : AbsoluteValue L ℝ) (hμA : ∀ a : L, a ∈ A ↔ μ a ≤ 1)
    (An : Annulus A F) (C : ComponentChart A F Fbar) (x : Place (ResidueField A) Fbar)
    (hatt : An.IsAttached C x)
    (f : F) (hf : f ∈ C.integers) (hres : C.residue ⟨f, hf⟩ ≠ 0)
    (hx : 0 < x.ord (C.residue ⟨f, hf⟩)) (hzf : ∀ Q ∈ An.dom, Q.ord f = 0) :
    ∀ Q ∈ An.dom, μ (Q.evalAt f) < 1 ∧
      μ (Q.evalAt f) = μ (Q.evalAt An.param) ^ (x.ord (C.residue ⟨f, hf⟩)) := by
  intro Q hQ
  obtain ⟨-, hzC, -, hlaw⟩ := hatt
  obtain ⟨hw, hunit⟩ := hlaw f hf hres hzf Q hQ
  obtain ⟨-, -, ⟨hzA, hzmax⟩, hz0, -⟩ := An.mem_dom Q hQ
  set n : ℤ := x.ord (C.residue ⟨f, hf⟩) with hn
  set z : L := Q.evalAt An.param with hz
  have hμz1 : μ z < 1 := abv_lt_one_of_mem_maximalIdeal_valuationSubring μ hμA hzA hzmax
  have hμz0 : 0 < μ z := μ.pos hz0
  have hunit1 : μ (Q.evalAt f * z ^ (-n)) = 1 :=
    abv_eq_one_of_isUnit_valuationSubring μ hμA hw hunit
  have heq : μ (Q.evalAt f) = μ z ^ n := by
    rw [map_mul, map_zpow₀, zpow_neg] at hunit1
    exact (mul_inv_eq_one₀ (zpow_ne_zero _ hμz0.ne')).1 hunit1
  refine ⟨?_, heq⟩
  rw [heq]
  exact zpow_lt_one₀ hμz0 hμz1 hx

end S_AlgebraicCurve_Annulus_abv_evalAt_lt_one_of_isAttached_of_ord_residue_pos
end P2MW
export P2MW.S_AlgebraicCurve_Annulus_abv_evalAt_lt_one_of_isAttached_of_ord_residue_pos (solution)
