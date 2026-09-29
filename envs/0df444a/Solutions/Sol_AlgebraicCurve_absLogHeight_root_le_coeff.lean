-- Prove2me | solution 1 for AlgebraicCurve.absLogHeight_root_le_coeff
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/28e0c706-3c84-5ad1-815b-9f3a46839be5

import Definitions.Def_ModularCurve_JZeroHeightForm
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.Algebra.Polynomial.FieldDivision
import Theorems.Thm_Height_inv_finrank_mul_logHeight_inclusion
import Theorems.Thm_AlgebraicCurve_sum_absLogHeight_roots_le_coeff
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_absLogHeight_root_le_coeff

set_option autoImplicit false
set_option Elab.async false

attribute [local instance] AlgebraicCurve.finiteDimensional_adjoin_range

namespace AlgebraicCurve p2m_export "AlgebraicCurve" "finiteDimensional_adjoin_range absLogHeight sum_absLogHeight_roots_le_coeff" end AlgebraicCurve
p2m_open_scoped "AlgebraicCurve" in

private theorem AlgebraicCurve.absLogHeight_eq_of_mem {ι : Type} [Fintype ι]
    (x : ι → AlgebraicClosure ℚ) (L : IntermediateField ℚ (AlgebraicClosure ℚ))
    [FiniteDimensional ℚ L] (hx : ∀ i, x i ∈ L) :
    absLogHeight x
      = (Module.finrank ℚ L : ℝ)⁻¹ * Height.logHeight (fun i => (⟨x i, hx i⟩ : L)) := by
  have hle : IntermediateField.adjoin ℚ (Set.range x) ≤ L :=
    IntermediateField.adjoin_le_iff.mpr (Set.range_subset_iff.mpr hx)
  have h3 := Height.inv_finrank_mul_logHeight_inclusion (L := L) hle
    (fun i => (⟨x i, IntermediateField.subset_adjoin ℚ (Set.range x) ⟨i, rfl⟩⟩ :
      IntermediateField.adjoin ℚ (Set.range x)))
  have htup : (fun i => IntermediateField.inclusion hle
      (⟨x i, IntermediateField.subset_adjoin ℚ (Set.range x) ⟨i, rfl⟩⟩ :
        IntermediateField.adjoin ℚ (Set.range x))) = fun i => (⟨x i, hx i⟩ : L) := by
    funext i
    rfl
  unfold AlgebraicCurve.absLogHeight
  rw [← htup]
  exact h3.symm

namespace MWB1

p2m_open "ModularCurve AlgebraicCurve P2MW.S_AlgebraicCurve_absLogHeight_root_le_coeff.AlgebraicCurve"

private theorem mwb1_absLogHeight_nonneg {ι : Type} [Fintype ι]
    (x : ι → AlgebraicClosure ℚ) : 0 ≤ absLogHeight x := by
  unfold AlgebraicCurve.absLogHeight
  exact mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _)) (Height.logHeight_nonneg _)

private theorem mwb1_srh_abs {ι : Type*} (t : Finset ι) (α : ι → AlgebraicClosure ℚ)
    (m : ι → ℕ) {n : ℕ} (hdeg : ∑ i ∈ t, m i ≤ n) :
    ∑ i ∈ t, (m i : ℝ) * absLogHeight ![α i, 1]
      ≤ absLogHeight (fun k : Fin (n + 1) =>
          (∏ i ∈ t, (Polynomial.X - Polynomial.C (α i)) ^ m i).coeff k)
        + Real.log (Real.sqrt (n + 1)) :=
  AlgebraicCurve.sum_absLogHeight_roots_le_coeff t α m hdeg

open Real in

private theorem mwb1_root_ht {χ : Polynomial (AlgebraicClosure ℚ)} (hχ : χ.Monic)
    {z : AlgebraicClosure ℚ} (hz : χ.eval z = 0) :
    absLogHeight ![z, 1]
      ≤ absLogHeight (fun k : Fin (χ.natDegree + 1) => χ.coeff k)
        + Real.log (Real.sqrt (χ.natDegree + 1)) := by
  classical
  have hχ0 : χ ≠ 0 := hχ.ne_zero
  have hsplits : χ.Splits := IsAlgClosed.splits χ
  have hprod : χ = (χ.roots.map fun r => Polynomial.X - Polynomial.C r).prod :=
    hsplits.eq_prod_roots_of_monic hχ
  have hfactor : (χ.roots.map fun r => Polynomial.X - Polynomial.C r).prod
      = ∏ r ∈ χ.roots.toFinset,
          (Polynomial.X - Polynomial.C r) ^ χ.roots.count r :=
    Finset.prod_multiset_map_count _ _
  have hdeg : (∑ r ∈ χ.roots.toFinset, χ.roots.count r) ≤ χ.natDegree := by
    rw [Multiset.toFinset_sum_count_eq]
    exact_mod_cast (Polynomial.card_roots' χ)
  have hsrh := MWB1.mwb1_srh_abs χ.roots.toFinset id (fun r => χ.roots.count r) hdeg
  have hzr : z ∈ χ.roots := by
    rw [Polynomial.mem_roots hχ0]
    exact hz
  have hz1 : 1 ≤ χ.roots.count z := Multiset.one_le_count_iff_mem.mpr hzr
  have hsingle : absLogHeight ![z, 1]
      ≤ ∑ r ∈ χ.roots.toFinset, (χ.roots.count r : ℝ) * absLogHeight ![id r, 1] := by
    have hmem : z ∈ χ.roots.toFinset := Multiset.mem_toFinset.mpr hzr
    calc absLogHeight ![z, 1]
        = absLogHeight ![id z, 1] := rfl
      _ ≤ (χ.roots.count z : ℝ) * absLogHeight ![id z, 1] := by
          have h1 : (1 : ℝ) ≤ (χ.roots.count z : ℝ) := by exact_mod_cast hz1
          have h2 := MWB1.mwb1_absLogHeight_nonneg (![id z, 1])
          nlinarith
      _ ≤ _ := Finset.single_le_sum (f := fun r => (χ.roots.count r : ℝ) * absLogHeight ![id r, 1])
          (fun r _ => mul_nonneg (by positivity) (MWB1.mwb1_absLogHeight_nonneg _)) hmem
  refine hsingle.trans (hsrh.trans ?_)
  have hpoly : (∏ r ∈ χ.roots.toFinset,
      (Polynomial.X - Polynomial.C (id r)) ^ χ.roots.count r) = χ := by
    simp only [id]
    rw [← hfactor, ← hprod]
  rw [hpoly]

end MWB1

open ModularCurve _root_.AlgebraicCurve _root_.P2MW.S_AlgebraicCurve_absLogHeight_root_le_coeff.AlgebraicCurve in
theorem solution {p : Polynomial (AlgebraicClosure ℚ)}
    (hmonic : p.Monic) {z : AlgebraicClosure ℚ} (hroot : p.eval z = 0) :
    absLogHeight ![z, 1]
      ≤ absLogHeight (fun k : Fin (p.natDegree + 1) => p.coeff k)
        + Real.log (Real.sqrt (p.natDegree + 1)) :=
  MWB1.mwb1_root_ht hmonic hroot

end S_AlgebraicCurve_absLogHeight_root_le_coeff
end P2MW
export P2MW.S_AlgebraicCurve_absLogHeight_root_le_coeff (solution)
