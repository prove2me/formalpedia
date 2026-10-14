-- Prove2me | solution 1 for Apery.energy_raw
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-10-12T00:37:31.734139+00:00
-- url     : https://prove2.me/submissions/9837107c-a52e-48f8-8c16-a1674f4bf1c0

/-
# Irrationality of $\zeta(5)$ via normalized Hankel determinants
# The raw configuration inequality — reduction to the atom energy and the four blocks

This file proves the platform theorem `Apery.energy_raw`:

  `∑ᵢ ∑ᵢ' log|tᵢ - tᵢ'| ≤ -h log ε + 2K ∑ᵢ (Uρ(tᵢ) + Err ε tᵢ) - K² I(ρ)`

from the six imported platform children `Apery.atom_energy_nonpos` (Lemma 6.2 for the atoms),
the four block inequalities `Apery.block_A`–`Apery.block_D` and the symmetry
`Apery.pairInt_log_symm`. All remaining steps — the reordering of the double sums into the
four blocks, the identity `I(ρ) = ∑_{j,j'} c_j c_{j'} log((b_{max} - a_{max})/4)` and the final
algebra — are proved here as a faithful port of the pinned source project
mo271/Zeta5 @ 7fe736760f4b96bfdb4334b68e3b3124ecbe10b0, `Apery/EnergyRaw.lean`
(with the Table 1 positivity facts of `Apery/Potential.lean`).
-/

import Mathlib
import Definitions.Def_Zeta5_SourceConstruction
import Definitions.Def_Zeta5_SourceValue
import Definitions.Def_Zeta5_SourceConstants
import Definitions.Def_Zeta5_SourceMeasure
import Definitions.Def_Zeta5_SourceAnalytic
import Definitions.Def_Zeta5_SourceEnergy
import Definitions.Def_Zeta5_SourceAtoms
import Theorems.Thm_Apery_atom_energy_nonpos
import Theorems.Thm_Apery_block_A
import Theorems.Thm_Apery_block_B
import Theorems.Thm_Apery_block_C
import Theorems.Thm_Apery_block_D
import Theorems.Thm_Apery_pairInt_log_symm

set_option autoImplicit false

section Port0
/-!
# The raw configuration inequality

From the atom energy nonpositivity (`atom_energy_nonpos`), the four block inequalities
`block_A`–`block_D` and the symmetry `pairInt_log_symm` (all imported children), we assemble
the raw inequality

`∑ᵢ ∑ᵢ' log|tᵢ - tᵢ'| ≤ -h log ε + 2K ∑ᵢ (Uρ(tᵢ) + Err ε tᵢ) - K² I(ρ)`.

Ported from mo271/Zeta5 @ 7fe736760f4b96bfdb4334b68e3b3124ecbe10b0, `Apery/EnergyRaw.lean`.
-/

open MeasureTheory Set Real intervalIntegral Filter Topology Finset

namespace Apery

lemma cρ_pos : ∀ j ∈ Finset.Icc 1 16, 0 < cρ j := by
  intro j hj
  rw [Finset.mem_Icc] at hj
  obtain ⟨hj1, hj2⟩ := hj
  interval_cases j <;> norm_num [cρ, table1]

/-- Reindexing `∑_{j ∈ Icc 1 m} f j = ∑_{j < m} f (j + 1)`. -/
lemma sum_Icc_eq_sum_range' (m : ℕ) (f : ℕ → ℝ) :
    ∑ j ∈ Finset.Icc 1 m, f j = ∑ j ∈ Finset.range m, f (j + 1) := by
  have e1 : Finset.Icc 1 m = Finset.Ico 1 (m + 1) := by
    ext x; simp only [Finset.mem_Icc, Finset.mem_Ico]; omega
  rw [e1, Finset.sum_Ico_eq_sum_range, show m + 1 - 1 = m by omega]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [add_comm]

/-- `∑_{j,j' < N} c_j c_j' f (max j j') = ∑_{j < N} (S_{j+1}² - S_j²) f_j` with `S_k = ∑_{i<k} c_i`. -/
lemma sum_sum_max_eq (c f : ℕ → ℝ) (N : ℕ) :
    ∑ j ∈ range N, ∑ j' ∈ range N, c j * c j' * f (max j j') =
      ∑ j ∈ range N, ((∑ i ∈ range (j + 1), c i) ^ 2 - (∑ i ∈ range j, c i) ^ 2) * f j := by
  induction N with
  | zero => simp
  | succ N ih =>
    simp only [Finset.sum_range_succ] at ih ⊢
    rw [Finset.sum_add_distrib, ih]
    have h1 : ∀ j ∈ range N, c j * c N * f (max j N) = c j * c N * f N := by
      intro j hj
      rw [max_eq_right (Finset.mem_range.mp hj).le]
    have h2 : ∀ j' ∈ range N, c N * c j' * f (max N j') = c N * c j' * f N := by
      intro j' hj'
      rw [max_eq_left (Finset.mem_range.mp hj').le]
    rw [Finset.sum_congr rfl h1, Finset.sum_congr rfl h2, max_self]
    simp only [← Finset.sum_mul, ← Finset.mul_sum]
    ring

/-- `I(ρ)` as a double sum over the sixteen intervals. -/
lemma Irho_eq_double_sum :
    Irho = ∑ j : Fin 16, ∑ j' : Fin 16, cρ (j + 1) * cρ (j' + 1) *
      Real.log ((bρ (max (j : ℕ) j' + 1) - aρ (max (j : ℕ) j' + 1)) / 4) := by
  have hS : ∀ k, Sρ k = ∑ i ∈ range k, cρ (i + 1) := fun k => by
    rw [Sρ, sum_Icc_eq_sum_range']
  unfold Irho
  rw [sum_Icc_eq_sum_range']
  simp only [Nat.add_sub_cancel, hS]
  rw [← sum_sum_max_eq (fun i => cρ (i + 1)) (fun j => Real.log ((bρ (j + 1) - aρ (j + 1)) / 4)) 16,
    ← Fin.sum_univ_eq_sum_range (fun j => ∑ j' ∈ range 16, cρ (j + 1) * cρ (j' + 1) *
      Real.log ((bρ (max j j' + 1) - aρ (max j j' + 1)) / 4)) 16]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← Fin.sum_univ_eq_sum_range (fun j' => cρ ((j : ℕ) + 1) * cρ (j' + 1) *
      Real.log ((bρ (max (j : ℕ) j' + 1) - aρ (max (j : ℕ) j' + 1)) / 4)) 16]

/-- The arcsine–arcsine block dominates `(2π)² I(ρ)`. -/
lemma block_D_sum {h : ℕ} (t : Fin h → ℝ) {ε : ℝ} (hε : 0 < ε) :
    (2 * π) ^ 2 * Irho ≤
      ∑ j : Fin 16, ∑ j' : Fin 16, cρ (j + 1) * cρ (j' + 1) * Plog t ε (Sum.inr j) (Sum.inr j') := by
  rw [Irho_eq_double_sum, Finset.mul_sum]
  refine Finset.sum_le_sum fun j _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun j' _ => ?_
  have hc : 0 ≤ cρ (j + 1) * cρ (j' + 1) :=
    mul_nonneg (cρ_pos _ (by simp only [Finset.mem_Icc]; omega)).le
      (cρ_pos _ (by simp only [Finset.mem_Icc]; omega)).le
  have hP : (2 * π) ^ 2 * Real.log ((bρ (max (j : ℕ) j' + 1) - aρ (max (j : ℕ) j' + 1)) / 4) ≤
      Plog t ε (Sum.inr j) (Sum.inr j') := by
    rcases le_total (j : ℕ) j' with hjj | hjj
    · rw [max_eq_right hjj]; exact block_D t hε j j'
    · rw [max_eq_left hjj, Plog, pairInt_log_symm t hε]; exact block_D t hε j' j
  calc (2 * π) ^ 2 * (cρ (j + 1) * cρ (j' + 1) *
        Real.log ((bρ (max (j : ℕ) j' + 1) - aρ (max (j : ℕ) j' + 1)) / 4))
      = cρ (j + 1) * cρ (j' + 1) *
        ((2 * π) ^ 2 * Real.log ((bρ (max (j : ℕ) j' + 1) - aρ (max (j : ℕ) j' + 1)) / 4)) := by
        ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hP hc

/-- The circle–circle block. -/
lemma block_AB_sum {h : ℕ} (t : Fin h → ℝ) (hinj : Function.Injective t) {ε : ℝ} (hε : 0 < ε) :
    (2 * π) ^ 2 * ((h : ℝ) * Real.log ε + ∑ i, ∑ i', Real.log |t i - t i'|) ≤
      ∑ i, ∑ i', Plog t ε (Sum.inl i) (Sum.inl i') := by
  have hi : ∀ i, (2 * π) ^ 2 * (Real.log ε + ∑ i', Real.log |t i - t i'|) ≤
      ∑ i', Plog t ε (Sum.inl i) (Sum.inl i') := by
    intro i
    rw [← Finset.add_sum_erase (s := Finset.univ) (f := fun i' => Plog t ε (Sum.inl i) (Sum.inl i'))
      (Finset.mem_univ i), block_A t hε i,
      ← Finset.sum_erase (s := Finset.univ) (a := i) (f := fun i' => Real.log |t i - t i'|)
        (by simp), mul_add, Finset.mul_sum]
    refine add_le_add le_rfl (Finset.sum_le_sum fun i' hi' => ?_)
    exact block_B t hε i i' (fun h => Finset.ne_of_mem_erase hi' (hinj h).symm)
  calc (2 * π) ^ 2 * ((h : ℝ) * Real.log ε + ∑ i, ∑ i', Real.log |t i - t i'|)
      = ∑ i : Fin h, (2 * π) ^ 2 * (Real.log ε + ∑ i', Real.log |t i - t i'|) := by
        simp only [mul_add, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
          Fintype.card_fin, nsmul_eq_mul, Finset.mul_sum]
        ring
    _ ≤ _ := Finset.sum_le_sum fun i _ => hi i

/-- The circle–arcsine block. -/
lemma block_C_sum {h : ℕ} (t : Fin h → ℝ) {ε : ℝ} (hε : 0 < ε) (i : Fin h) :
    ∑ j : Fin 16, cρ (j + 1) * Plog t ε (Sum.inl i) (Sum.inr j) ≤
      (2 * π) ^ 2 * (Uρ (t i) + Err ε (t i)) := by
  have hU : Uρ (t i) = ∑ j : Fin 16, cρ (j + 1) * Uω (aρ (j + 1)) (bρ (j + 1)) (t i) := by
    rw [Uρ, sum_Icc_eq_sum_range', Fin.sum_univ_eq_sum_range
      (fun j => cρ (j + 1) * Uω (aρ (j + 1)) (bρ (j + 1)) (t i)) 16]
  rw [hU, Err, ← Finset.sum_add_distrib, Finset.mul_sum]
  refine Finset.sum_le_sum fun j _ => ?_
  have hc : 0 ≤ cρ (j + 1) := (cρ_pos _ (by simp only [Finset.mem_Icc]; omega)).le
  calc cρ (j + 1) * Plog t ε (Sum.inl i) (Sum.inr j)
      ≤ cρ (j + 1) * ((2 * π) ^ 2 * (Uω (aρ (j + 1)) (bρ (j + 1)) (t i) +
          errj ε (t i) (mρ (j + 1)) (rρ (j + 1)))) :=
        mul_le_mul_of_nonneg_left (block_C t hε i j) hc
    _ = _ := by ring

/-- **The raw configuration inequality.** -/
theorem energy_raw (n : ℕ) (hn : 0 < n) (t : Fin (37 * n) → ℝ) (hinj : Function.Injective t)
    {ε : ℝ} (hε : 0 < ε) :
    ∑ i, ∑ i', Real.log |t i - t i'| ≤
      -(37 * n : ℝ) * Real.log ε + 2 * Kr n * ∑ i, (Uρ (t i) + Err ε (t i)) - Kr n ^ 2 * Irho := by
  have hK : 0 < Kr n := by simp only [Kr]; positivity
  set AB := ∑ i, ∑ i', Plog t ε (Sum.inl i) (Sum.inl i') with hAB
  set C := ∑ i, ∑ j : Fin 16, cρ (j + 1) * Plog t ε (Sum.inl i) (Sum.inr j) with hC
  set D := ∑ j : Fin 16, ∑ j' : Fin 16, cρ (j + 1) * cρ (j' + 1) * Plog t ε (Sum.inr j) (Sum.inr j')
    with hD
  have hE : ∑ i, (∑ i', 1 / Kr n * (1 / Kr n) * Plog t ε (Sum.inl i) (Sum.inl i') +
      ∑ j : Fin 16, 1 / Kr n * -cρ (j + 1) * Plog t ε (Sum.inl i) (Sum.inr j)) +
      ∑ j : Fin 16, (∑ i, -cρ (j + 1) * (1 / Kr n) * Plog t ε (Sum.inr j) (Sum.inl i) +
        ∑ j' : Fin 16, -cρ (j + 1) * -cρ (j' + 1) * Plog t ε (Sum.inr j) (Sum.inr j')) ≤ 0 := by
    have := atom_energy_nonpos n hn t hε
    unfold energy at this
    simpa only [Fintype.sum_sum_type, atomS, Plog] using this
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib] at hE
  have hL1 : ∑ i, ∑ i', 1 / Kr n * (1 / Kr n) * Plog t ε (Sum.inl i) (Sum.inl i') =
      (1 / Kr n) ^ 2 * AB := by
    rw [hAB, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i' _ => by ring
  have hL2 : ∑ i, ∑ j : Fin 16, 1 / Kr n * -cρ (j + 1) * Plog t ε (Sum.inl i) (Sum.inr j) =
      -(1 / Kr n) * C := by
    rw [hC, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  have hL3 : ∑ j : Fin 16, ∑ i, -cρ (j + 1) * (1 / Kr n) * Plog t ε (Sum.inr j) (Sum.inl i) =
      -(1 / Kr n) * C := by
    rw [hC, Finset.mul_sum, Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Plog]
    rw [pairInt_log_symm t hε]
    ring
  have hL4 : ∑ j : Fin 16, ∑ j' : Fin 16, -cρ (j + 1) * -cρ (j' + 1) *
      Plog t ε (Sum.inr j) (Sum.inr j') = D := by
    rw [hD]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun j' _ => by ring
  rw [hL1, hL2, hL3, hL4] at hE
  have hE' : (1 / Kr n) ^ 2 * AB - 2 * (1 / Kr n) * C + D ≤ 0 := by linarith
  have h1 := block_AB_sum t hinj hε
  have h2 : C ≤ (2 * π) ^ 2 * ∑ i, (Uρ (t i) + Err ε (t i)) := by
    rw [hC, Finset.mul_sum]
    exact Finset.sum_le_sum fun i _ => block_C_sum t hε i
  have h3 := block_D_sum t hε
  rw [← hAB] at h1
  rw [← hD] at h3
  -- combine: (1/K)² AB ≤ 2 (1/K) C - D
  have hpi : 0 < (2 * π) ^ 2 := by positivity
  have hK2 : 0 < (1 / Kr n) ^ 2 := by positivity
  have key : (1 / Kr n) ^ 2 * ((2 * π) ^ 2 * ((37 * n : ℝ) * Real.log ε +
      ∑ i, ∑ i', Real.log |t i - t i'|)) ≤
      2 * (1 / Kr n) * ((2 * π) ^ 2 * ∑ i, (Uρ (t i) + Err ε (t i))) - (2 * π) ^ 2 * Irho := by
    have := mul_le_mul_of_nonneg_left h1 hK2.le
    push_cast at this
    have h2' := mul_le_mul_of_nonneg_left h2 (by positivity : (0:ℝ) ≤ 2 * (1 / Kr n))
    linarith
  have key2 : (1 / Kr n) ^ 2 * ((37 * n : ℝ) * Real.log ε + ∑ i, ∑ i', Real.log |t i - t i'|) ≤
      2 * (1 / Kr n) * ∑ i, (Uρ (t i) + Err ε (t i)) - Irho := by
    have := key
    have e : (1 / Kr n) ^ 2 * ((2 * π) ^ 2 * ((37 * n : ℝ) * Real.log ε +
        ∑ i, ∑ i', Real.log |t i - t i'|)) = (2 * π) ^ 2 *
        ((1 / Kr n) ^ 2 * ((37 * n : ℝ) * Real.log ε + ∑ i, ∑ i', Real.log |t i - t i'|)) := by ring
    have e2 : 2 * (1 / Kr n) * ((2 * π) ^ 2 * ∑ i, (Uρ (t i) + Err ε (t i))) - (2 * π) ^ 2 * Irho =
        (2 * π) ^ 2 * (2 * (1 / Kr n) * ∑ i, (Uρ (t i) + Err ε (t i)) - Irho) := by ring
    rw [e, e2] at this
    exact le_of_mul_le_mul_left this hpi
  have this := mul_le_mul_of_nonneg_left key2 (sq_nonneg (Kr n))
  have e1 : Kr n ^ 2 * ((1 / Kr n) ^ 2 * ((37 * n : ℝ) * Real.log ε +
      ∑ i, ∑ i', Real.log |t i - t i'|)) =
      (37 * n : ℝ) * Real.log ε + ∑ i, ∑ i', Real.log |t i - t i'| := by
    field_simp
  have e2 : Kr n ^ 2 * (2 * (1 / Kr n) * ∑ i, (Uρ (t i) + Err ε (t i)) - Irho) =
      2 * Kr n * ∑ i, (Uρ (t i) + Err ε (t i)) - Kr n ^ 2 * Irho := by
    field_simp
  rw [e1, e2] at this
  linarith

end Apery
end Port0


open MeasureTheory Polynomial Finset in
/-- The platform target `Apery.energy_raw`, restated at top level as `solution`. -/
theorem solution (n : ℕ) (hn : 0 < n) (t : Fin (37 * n) → ℝ) (hinj : Function.Injective t)
    {ε : ℝ} (hε : 0 < ε) :
    ∑ i, ∑ i', Real.log |t i - t i'| ≤
      -(37 * n : ℝ) * Real.log ε +
        2 * Apery.Kr n * ∑ i, (Apery.Uρ (t i) + Apery.Err ε (t i)) -
          Apery.Kr n ^ 2 * Apery.Irho :=
  Apery.energy_raw n hn t hinj hε
