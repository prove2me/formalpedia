-- Prove2me | Definitions.Def_CK_GeneralCK_FiniteLaw
-- name    : CK_GeneralCK_FiniteLaw
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-27T22:24:51.993774+00:00
-- url     : https://prove2.me/theorems/4875b6f3-105c-4059-918c-ed4197400db5
-- title:
--   Courtade–Kumar proof module `GeneralCK.FiniteLaw` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.FiniteLaw` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.FiniteLaw` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.FiniteLaw (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/FiniteLaw.lean)

import Definitions.Def_CK_GeneralCK_EtaMonotone
import Mathlib.Analysis.Convex.Jensen
import Definitions.Def_GeneralCK_finite_law_regional

/-! Finite interior laws, their actual moment constraints, and the two target symmetries. -/
namespace GeneralCK
open scoped BigOperators










namespace InteriorLaw
variable {ι : Type*} [Fintype ι]











@[simp] theorem avg_const (μ : InteriorLaw ι) (c : ℝ) : μ.avg (fun _ => c) = c := by
  simp only [avg, ← Finset.sum_mul, μ.weight_sum, one_mul]

theorem avg_add (μ : InteriorLaw ι) (v w : ι → ℝ) :
    μ.avg (fun i => v i + w i) = μ.avg v + μ.avg w := by
  simp [avg, mul_add, Finset.sum_add_distrib]

theorem avg_sub (μ : InteriorLaw ι) (v w : ι → ℝ) :
    μ.avg (fun i => v i - w i) = μ.avg v - μ.avg w := by
  simp [avg, mul_sub, Finset.sum_sub_distrib]

theorem avg_mono (μ : InteriorLaw ι) {v w : ι → ℝ} (h : ∀ i, v i ≤ w i) :
    μ.avg v ≤ μ.avg w :=
  Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (h i) (μ.weight_nonneg i)

theorem exists_pos_weight (μ : InteriorLaw ι) : ∃ i, 0 < μ.weight i := by
  by_contra hn
  push Not at hn
  have hz : ∑ i, μ.weight i = 0 := Finset.sum_eq_zero fun i _ =>
    le_antisymm (hn i) (μ.weight_nonneg i)
  linarith [μ.weight_sum]

theorem avg_pos (μ : InteriorLaw ι) {v : ι → ℝ} (hv : ∀ i, 0 < v i) : 0 < μ.avg v := by
  obtain ⟨i, hi⟩ := μ.exists_pos_weight
  exact Finset.sum_pos' (fun j _ => mul_nonneg (μ.weight_nonneg j) (hv j).le)
    ⟨i, Finset.mem_univ i, mul_pos hi (hv i)⟩

theorem avg_interior (μ : InteriorLaw ι) {v : ι → ℝ}
    (hv : ∀ i, 0 < v i ∧ v i < 1) : 0 < μ.avg v ∧ μ.avg v < 1 := by
  have hp := μ.avg_pos (fun i => (hv i).1)
  have hq := μ.avg_pos (v := fun i => 1 - v i) (fun i => sub_pos.mpr (hv i).2)
  rw [μ.avg_sub, μ.avg_const] at hq
  constructor <;> linarith

theorem entropy_avg_le (μ : InteriorLaw ι) {v : ι → ℝ}
    (hv : ∀ i, 0 ≤ v i ∧ v i ≤ 1) : μ.avg (H ∘ v) ≤ H (μ.avg v) := by
  have hj := Real.strictConcave_binEntropy.concaveOn.le_map_sum
    (t := Finset.univ) (w := μ.weight) (p := v)
    (fun i _ => μ.weight_nonneg i) μ.weight_sum (fun i _ => hv i)
  have h := div_le_div_of_nonneg_right hj log_two_pos.le
  simpa only [avg, H, Function.comp_apply, smul_eq_mul, div_eq_mul_inv,
    Finset.sum_mul, mul_assoc] using h

theorem a_interior (μ : InteriorLaw ι) : 0 < μ.a ∧ μ.a < 1 :=
  μ.avg_interior μ.left_interior
theorem b_interior (μ : InteriorLaw ι) : 0 < μ.b ∧ μ.b < 1 :=
  μ.avg_interior μ.right_interior
theorem e_pos (μ : InteriorLaw ι) : 0 < μ.e :=
  μ.avg_pos fun i => H_pos (μ.left_interior i).1 (μ.left_interior i).2
theorem f_pos (μ : InteriorLaw ι) : 0 < μ.f :=
  μ.avg_pos fun i => H_pos (μ.right_interior i).1 (μ.right_interior i).2
theorem e_le_cap (μ : InteriorLaw ι) : μ.e ≤ H μ.a :=
  μ.entropy_avg_le fun i => ⟨(μ.left_interior i).1.le, (μ.left_interior i).2.le⟩
theorem f_le_cap (μ : InteriorLaw ι) : μ.f ≤ H μ.b :=
  μ.entropy_avg_le fun i => ⟨(μ.right_interior i).1.le, (μ.right_interior i).2.le⟩



















@[simp] theorem swap_a (μ : InteriorLaw ι) : μ.swap.a = μ.b := rfl
@[simp] theorem swap_b (μ : InteriorLaw ι) : μ.swap.b = μ.a := rfl
@[simp] theorem swap_e (μ : InteriorLaw ι) : μ.swap.e = μ.f := rfl
@[simp] theorem swap_f (μ : InteriorLaw ι) : μ.swap.f = μ.e := rfl
@[simp] theorem complement_a (μ : InteriorLaw ι) : μ.complement.a = 1 - μ.a := by
  change μ.avg (fun i => 1 - μ.left i) = 1 - μ.a
  rw [μ.avg_sub, μ.avg_const]; rfl
@[simp] theorem complement_b (μ : InteriorLaw ι) : μ.complement.b = 1 - μ.b := by
  change μ.avg (fun i => 1 - μ.right i) = 1 - μ.b
  rw [μ.avg_sub, μ.avg_const]; rfl
@[simp] theorem complement_e (μ : InteriorLaw ι) : μ.complement.e = μ.e := by
  simp [e, avg, complement, Function.comp_apply, H_complement]
@[simp] theorem complement_f (μ : InteriorLaw ι) : μ.complement.f = μ.f := by
  simp [f, avg, complement, Function.comp_apply, H_complement]

end InteriorLaw

theorem J_complement (v : ℝ) : J (1 - v) = -J v := by
  unfold J
  rw [sub_sub_cancel, show v / (1 - v) = ((1 - v) / v)⁻¹ from (inv_div _ _).symm,
    Real.log_inv, neg_div]

theorem interiorCost_comm (u v : ℝ) : interiorCost u v = interiorCost v u := by
  unfold interiorCost; ring

theorem interiorCost_complement (u v : ℝ) :
    interiorCost (1 - u) (1 - v) = interiorCost u v := by
  simp only [interiorCost, J_complement]; ring

namespace InteriorLaw
variable {ι : Type*} [Fintype ι]

@[simp] theorem swap_cost (μ : InteriorLaw ι) : μ.swap.cost = μ.cost := by
  simp only [cost, avg, swap, interiorCost_comm (μ.right _) (μ.left _)]
@[simp] theorem complement_cost (μ : InteriorLaw ι) : μ.complement.cost = μ.cost := by
  simp only [cost, avg, complement, interiorCost_complement]
@[simp] theorem swap_gap (μ : InteriorLaw ι) : μ.swap.gap = μ.gap := by
  simp only [gap, swap_a, swap_b, swap_e, swap_f, add_comm]
@[simp] theorem complement_gap (μ : InteriorLaw ι) : μ.complement.gap = μ.gap := by
  simp only [gap, complement_a, complement_b, complement_e, complement_f]
  rw [show (1 - μ.a + (1 - μ.b)) / 2 = 1 - (μ.a + μ.b) / 2 by ring]
  simp only [B_complement]

/-- The genuine symmetries produce the exact canonical domain consumed by the cover. -/
theorem exists_canonical (μ : InteriorLaw ι) :
    ∃ ν : InteriorLaw ι, ν.a ≤ ν.b ∧ ν.a + ν.b ≤ 1 ∧
      ν.gap = μ.gap ∧ ν.cost = μ.cost := by
  by_cases hab : μ.a ≤ μ.b
  · by_cases hs : μ.a + μ.b ≤ 1
    · exact ⟨μ, hab, hs, rfl, rfl⟩
    · refine ⟨μ.complement.swap, ?_, ?_, ?_, ?_⟩
      · simp only [swap_a, swap_b, complement_a, complement_b]; linarith
      · simp only [swap_a, swap_b, complement_a, complement_b]; linarith
      · simp
      · simp
  · by_cases hs : μ.a + μ.b ≤ 1
    · refine ⟨μ.swap, ?_, ?_, ?_, ?_⟩
      · simp only [swap_a, swap_b]; linarith
      · simp only [swap_a, swap_b]; linarith
      · simp
      · simp
    · refine ⟨μ.complement, ?_, ?_, ?_, ?_⟩
      · simp only [complement_a, complement_b]; linarith
      · simp only [complement_a, complement_b]; linarith
      · simp
      · simp

end InteriorLaw

/-- Canonical finite-law inequalities suffice, with feasibility supplied by the law itself. -/
theorem finiteHybridBellman_of_canonical
    (hc : ∀ (k : ℕ) (μ : InteriorLaw (Fin k)),
      μ.a ≤ μ.b → μ.a + μ.b ≤ 1 → μ.gap ≤ μ.cost) : FiniteHybridBellman := by
  intro k w u v hw hsum hu hv
  let μ : InteriorLaw (Fin k) := ⟨w, u, v, hw, hsum, hu, hv⟩
  obtain ⟨ν, hab, hs, hg, hj⟩ := μ.exists_canonical
  have h := hc k ν hab hs
  rw [hg, hj] at h
  exact sub_le_iff_le_add'.mp h

end GeneralCK


