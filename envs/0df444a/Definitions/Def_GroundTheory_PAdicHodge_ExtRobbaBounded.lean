-- Prove2me | Definitions.Def_GroundTheory_PAdicHodge_ExtRobbaBounded
-- name    : GroundTheory_PAdicHodge_ExtRobbaBounded
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-25T11:16:09.378862+00:00
-- url     : https://prove2.me/theorems/4ad74c76-5d18-4b21-bd36-68fe6a696ea6
-- title:
--   Ext Robba Bounded
-- statement:
--   Definitions and structural lemmas for Ext Robba Bounded, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/ExtRobbaBounded.lean

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_ExtRobbaTeich
import Definitions.Def_GroundTheory_PAdicHodge_RobbaSeries
import Theorems.Thm_GroundTheory_PAdicHodge_Laurent_ConvergesAt_bddAbove
import Theorems.Thm_GroundTheory_PAdicHodge_Laurent_ConvergesAt_finite_le
import Theorems.Thm_GroundTheory_PAdicHodge_Laurent_ConvergesAt_le_gaussNorm
import Theorems.Thm_GroundTheory_PAdicHodge_Laurent_gaussNorm_le
import Theorems.Thm_GroundTheory_PAdicHodge_Laurent_gaussNorm_nonneg
import Theorems.Thm_GroundTheory_PAdicHodge_Laurent_gaussNorm_pos
import Theorems.Thm_GroundTheory_PAdicHodge_Laurent_lowIndex_le
import Theorems.Thm_GroundTheory_PAdicHodge_Laurent_lowIndex_mem
import Theorems.Thm_GroundTheory_PAdicHodge_Laurent_ne_zero_of_mem_domSet
import Theorems.Thm_GroundTheory_PAdicHodge_Laurent_weight_lt_of_lt_lowIndex
import Theorems.Thm_GroundTheory_PAdicHodge_TeichLift_PrefixLe_mono
import Theorems.Thm_GroundTheory_PAdicHodge_TeichLift_coeff_eq_coeff_of_sub_mem
import Theorems.Thm_GroundTheory_PAdicHodge_TeichLift_coeff_eq_of_mem
import Theorems.Thm_GroundTheory_PAdicHodge_TeichLift_coeff_ofCoeff
import Theorems.Thm_GroundTheory_PAdicHodge_TeichLift_coeff_teich
import Theorems.Thm_GroundTheory_PAdicHodge_TeichLift_coeff_zero_elem
import Theorems.Thm_GroundTheory_PAdicHodge_TeichLift_eq_of_coeff_eq
import Theorems.Thm_GroundTheory_PAdicHodge_TeichLift_finSum_congr
import Theorems.Thm_GroundTheory_PAdicHodge_TeichLift_prefixLe_add
import Theorems.Thm_GroundTheory_PAdicHodge_TeichLift_prefixLe_mul
import Theorems.Thm_GroundTheory_PAdicHodge_TeichLift_prefixLe_neg
import Theorems.Thm_GroundTheory_PAdicHodge_TeichLift_prefixLe_sub
import Theorems.Thm_GroundTheory_PAdicHodge_TeichLift_sub_partialSum
import Theorems.Thm_P2M_GroundTheory_PAdicHodge_TeichLift_coeff___mul_zero_c24e500c7aa0
import Theorems.Thm_P2M_GroundTheory_PAdicHodge_TeichLift_coeff___pow_mul_add_de69595147c6
import Theorems.Thm_P2M_GroundTheory_PAdicHodge_TeichLift_coeff___pow_mul_of_lt_398143255abf
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.PAdicHodge.TeichLift.coeff_ofCoeff
attribute [local simp] GroundTheory.PAdicHodge.TeichLift.coeff_zero_elem
attribute [local simp] P2M_GroundTheory_PAdicHodge_TeichLift_coeff___mul_zero_c24e500c7aa0


set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
set_option linter.unusedSectionVars false
namespace GroundTheory.PAdicHodge
open Laurent Filter Topology
section Seq
variable {L : Type*} [NontriviallyNormedField L] [IsUltrametricDist L]
theorem norm_le_div_of_weight {a : L} {m n : ℤ} {ρ M : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1)
    (hmn : m ≤ n) (h : ‖a‖ * ρ ^ m ≤ M) : ‖a‖ ≤ M / ρ ^ n := by
  rw [le_div_iff₀ (zpow_pos hρ0 n)]
  exact (mul_le_mul_of_nonneg_left (zpow_le_zpow_right_of_le_one₀ hρ0 hρ1 hmn) (norm_nonneg _)).trans h
theorem exists_prefix_small {a : ℤ → L} {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (h : ConvergesAt a ρ) {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℤ, ∀ n, N ≤ n → ∀ m ≤ n, ‖a m‖ * ρ ^ n ≤ ε := by
  obtain ⟨N0, hN0⟩ : ∃ N0 : ℤ, ∀ m, N0 ≤ m → ‖a m‖ * ρ ^ m ≤ ε := by
    obtain ⟨B, hB⟩ := (h.finite_le hε).bddAbove
    refine ⟨B + 1, fun m hm => ?_⟩
    by_contra hc
    push_neg at hc
    have := hB (show m ∈ {n | ε ≤ ‖a n‖ * ρ ^ n} from hc.le)
    omega
  have hG := gaussNorm_nonneg (a := a) hρ0
  obtain ⟨K, hK⟩ := exists_pow_lt_of_lt_one (show 0 < ε / (gaussNorm a ρ + 1) by positivity) hρ1
  refine ⟨N0 + K, fun n hn m hm => ?_⟩
  rcases le_or_gt N0 m with h1 | h1
  · exact (mul_le_mul_of_nonneg_left (zpow_le_zpow_right_of_le_one₀ hρ0 hρ1.le hm)
      (norm_nonneg _)).trans (hN0 m h1)
  · have hnm : (K : ℤ) ≤ n - m := by omega
    have hρK : ρ ^ (n - m) ≤ ρ ^ K := by
      rw [← zpow_natCast]; exact zpow_le_zpow_right_of_le_one₀ hρ0 hρ1.le hnm
    calc ‖a m‖ * ρ ^ n = (‖a m‖ * ρ ^ m) * ρ ^ (n - m) := by
          rw [mul_assoc, ← zpow_add₀ hρ0.ne', add_sub_cancel]
      _ ≤ gaussNorm a ρ * ρ ^ K :=
          mul_le_mul (h.le_gaussNorm m) hρK (zpow_pos hρ0 _).le hG
      _ ≤ (gaussNorm a ρ + 1) * (ε / (gaussNorm a ρ + 1)) := by
          apply mul_le_mul (by linarith) hK.le (by positivity) (by linarith)
      _ = ε := by field_simp
theorem convergesAt_of_eventually {a : ℤ → L} {ρ : ℝ} (hρ0 : 0 < ρ) (hneg : ∃ N, ∀ n < N, a n = 0)
    (h : ∀ ε > 0, ∃ N : ℤ, ∀ n, N ≤ n → ‖a n‖ * ρ ^ n ≤ ε) : ConvergesAt a ρ := by
  rw [ConvergesAt, Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨N1, hN1⟩ := hneg
  obtain ⟨N2, hN2⟩ := h (ε / 2) (by positivity)
  refine Filter.eventually_cofinite.2 ((Set.finite_Ico N1 N2).subset fun n hn => ?_)
  have hw : 0 ≤ ‖a n‖ * ρ ^ n := mul_nonneg (norm_nonneg _) (zpow_pos hρ0 n).le
  rw [Set.mem_setOf_eq, dist_zero_right, Real.norm_eq_abs, abs_of_nonneg hw, not_lt] at hn
  refine ⟨?_, ?_⟩
  · by_contra hc
    push_neg at hc
    rw [hN1 n hc, norm_zero, zero_mul] at hn
    linarith
  · by_contra hc
    push_neg at hc
    have := hN2 n hc
    linarith
theorem exists_lt_bound {f : ℕ → ℝ} {k : ℕ} {g : ℝ} (hg : 0 < g) (h : ∀ i < k, f i < g) :
    ∃ g' < g, 0 ≤ g' ∧ ∀ i < k, f i ≤ g' := by
  induction k with
  | zero => exact ⟨0, hg, le_rfl, fun i hi => absurd hi (Nat.not_lt_zero _)⟩
  | succ k ih =>
    obtain ⟨g1, hg1, hg10, hg1'⟩ := ih fun i hi => h i (by omega)
    refine ⟨max g1 (f k), max_lt hg1 (h k (by omega)), le_max_of_le_left hg10, fun i hi => ?_⟩
    rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
    · exact le_max_of_le_left (hg1' i hi)
    · exact le_max_right _ _
end Seq
namespace TeichLift
variable {p : ℕ} [hp : Fact p.Prime] {L : Type*} [NontriviallyNormedField L] [IsUltrametricDist L]
  [CharP L p] [PerfectRing L p] {Γ : Type*} [CommRing Γ] (T : TeichLift p L Γ)
theorem coeff_tail_iterate (x : Γ) (k m : ℕ) : T.coeff (T.tail^[k] x) m = T.coeff x (m + k) := by
  simp only [coeff, ← Function.iterate_add_apply]
theorem finSum_ite_eq (a : ℕ → L) {N n : ℕ} (h : N ≤ n) :
    T.finSum (fun j => if j < N then a j else 0) n = T.finSum a N := by
  induction n, h using Nat.le_induction with
  | base => exact T.finSum_congr fun i hi => if_pos hi
  | succ n hNn ih => rw [finSum_succ, ih, if_neg (by omega), T.teich_zero, mul_zero, add_zero]
theorem coeff_finSum (a : ℕ → L) (N i : ℕ) :
    T.coeff (T.finSum a N) i = if i < N then a i else 0 := by
  refine T.coeff_eq_of_mem (a := fun j => if j < N then a j else 0) ?_ i le_rfl
  rcases le_total (i + 1) N with h | h
  · have e : T.finSum (fun j => if j < N then a j else 0) (i + 1) = T.finSum a (i + 1) :=
      T.finSum_congr fun j hj => if_pos (by omega)
    rw [e]; exact T.finSum_sub_finSum_mem a h
  · rw [T.finSum_ite_eq a h, sub_self]; exact zero_mem _
theorem coeff_sub_partialSum (x : Γ) (k i : ℕ) :
    T.coeff (x - T.partialSum x k) i = if i < k then 0 else T.coeff x i := by
  rw [sub_partialSum]
  split_ifs with h
  · exact T.coeff_π_pow_mul_of_lt _ h
  · obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' (not_lt.1 h)
    rw [coeff_π_pow_mul_add, coeff_tail_iterate]
def zcoeff (x : Γ) (n : ℤ) : L := if 0 ≤ n then T.coeff x n.toNat else 0
@[simp] theorem zcoeff_natCast (x : Γ) (n : ℕ) : T.zcoeff x n = T.coeff x n := by simp [zcoeff]
theorem zcoeff_of_neg (x : Γ) {n : ℤ} (h : n < 0) : T.zcoeff x n = 0 := by
  simp [zcoeff, not_le.2 h]
theorem zcoeff_neg_exists (x : Γ) : ∃ N, ∀ n < N, T.zcoeff x n = 0 :=
  ⟨0, fun _ hn => T.zcoeff_of_neg x hn⟩
theorem zcoeff_eq_zero_iff (x : Γ) : T.zcoeff x = 0 ↔ x = 0 := by
  constructor
  · intro h
    refine T.eq_of_coeff_eq (funext fun n => ?_)
    have := congrFun h n
    rw [zcoeff_natCast] at this
    rw [this, coeff_zero_elem, Pi.zero_apply]
  · rintro rfl; funext n; simp [zcoeff]
theorem norm_zcoeff_add_le {x y : Γ} {n : ℤ} {b : ℝ} (hb : 0 ≤ b)
    (hx : ∀ m ≤ n, ‖T.zcoeff x m‖ ≤ b) (hy : ∀ m ≤ n, ‖T.zcoeff y m‖ ≤ b) :
    ‖T.zcoeff (x + y) n‖ ≤ b := by
  rcases lt_or_ge n 0 with hn | hn
  · rw [T.zcoeff_of_neg _ hn, norm_zero]; exact hb
  · lift n to ℕ using hn
    rw [zcoeff_natCast]
    refine T.prefixLe_add (fun m hm => ?_) (fun m hm => ?_) n le_rfl
    · have := hx m (by exact_mod_cast hm); rwa [zcoeff_natCast] at this
    · have := hy m (by exact_mod_cast hm); rwa [zcoeff_natCast] at this
theorem norm_zcoeff_neg_le {x : Γ} {n : ℤ} {b : ℝ} (hb : 0 ≤ b)
    (hx : ∀ m ≤ n, ‖T.zcoeff x m‖ ≤ b) : ‖T.zcoeff (-x) n‖ ≤ b := by
  rcases lt_or_ge n 0 with hn | hn
  · rw [T.zcoeff_of_neg _ hn, norm_zero]; exact hb
  · lift n to ℕ using hn
    rw [zcoeff_natCast]
    refine T.prefixLe_neg (fun m hm => ?_) n le_rfl
    have := hx m (by exact_mod_cast hm); rwa [zcoeff_natCast] at this
theorem norm_zcoeff_mul_le {x y : Γ} {n : ℤ} {b : ℝ} (hb : 0 ≤ b)
    (h : ∀ i j : ℤ, i + j ≤ n → ‖T.zcoeff x i‖ * ‖T.zcoeff y j‖ ≤ b) :
    ‖T.zcoeff (x * y) n‖ ≤ b := by
  rcases lt_or_ge n 0 with hn | hn
  · rw [T.zcoeff_of_neg _ hn, norm_zero]; exact hb
  · lift n to ℕ using hn
    rw [zcoeff_natCast]
    refine T.prefixLe_mul hb (fun i j hij => ?_) n le_rfl
    have := h i j (by exact_mod_cast hij); rwa [zcoeff_natCast, zcoeff_natCast] at this
variable {ρ : ℝ}
theorem gaussNorm_zcoeff_add_le {x y : Γ} (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1)
    (hx : ConvergesAt (T.zcoeff x) ρ) (hy : ConvergesAt (T.zcoeff y) ρ) :
    gaussNorm (T.zcoeff (x + y)) ρ ≤
      max (gaussNorm (T.zcoeff x) ρ) (gaussNorm (T.zcoeff y) ρ) := by
  refine gaussNorm_le fun n => ?_
  have hM : 0 ≤ max (gaussNorm (T.zcoeff x) ρ) (gaussNorm (T.zcoeff y) ρ) :=
    le_max_of_le_left (gaussNorm_nonneg hρ0)
  have := T.norm_zcoeff_add_le (n := n) (div_nonneg hM (zpow_pos hρ0 n).le)
    (fun m hm => norm_le_div_of_weight hρ0 hρ1 hm ((hx.le_gaussNorm m).trans (le_max_left _ _)))
    (fun m hm => norm_le_div_of_weight hρ0 hρ1 hm ((hy.le_gaussNorm m).trans (le_max_right _ _)))
  rwa [le_div_iff₀ (zpow_pos hρ0 n)] at this
theorem convergesAt_zcoeff_add {x y : Γ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (hx : ConvergesAt (T.zcoeff x) ρ) (hy : ConvergesAt (T.zcoeff y) ρ) :
    ConvergesAt (T.zcoeff (x + y)) ρ := by
  refine convergesAt_of_eventually hρ0 (T.zcoeff_neg_exists _) fun ε hε => ?_
  obtain ⟨N1, hN1⟩ := exists_prefix_small hρ0 hρ1 hx hε
  obtain ⟨N2, hN2⟩ := exists_prefix_small hρ0 hρ1 hy hε
  refine ⟨max N1 N2, fun n hn => ?_⟩
  have := T.norm_zcoeff_add_le (n := n) (div_nonneg hε.le (zpow_pos hρ0 n).le)
    (fun m hm => by
      rw [le_div_iff₀ (zpow_pos hρ0 n)]; exact hN1 n (le_of_max_le_left hn) m hm)
    (fun m hm => by
      rw [le_div_iff₀ (zpow_pos hρ0 n)]; exact hN2 n (le_of_max_le_right hn) m hm)
  rwa [le_div_iff₀ (zpow_pos hρ0 n)] at this
theorem gaussNorm_zcoeff_neg_le {x : Γ} (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1)
    (hx : ConvergesAt (T.zcoeff x) ρ) :
    gaussNorm (T.zcoeff (-x)) ρ ≤ gaussNorm (T.zcoeff x) ρ := by
  refine gaussNorm_le fun n => ?_
  have := T.norm_zcoeff_neg_le (n := n) (div_nonneg (gaussNorm_nonneg hρ0) (zpow_pos hρ0 n).le)
    (fun m hm => norm_le_div_of_weight hρ0 hρ1 hm (hx.le_gaussNorm m))
  rwa [le_div_iff₀ (zpow_pos hρ0 n)] at this
theorem convergesAt_zcoeff_neg {x : Γ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (hx : ConvergesAt (T.zcoeff x) ρ) : ConvergesAt (T.zcoeff (-x)) ρ := by
  refine convergesAt_of_eventually hρ0 (T.zcoeff_neg_exists _) fun ε hε => ?_
  obtain ⟨N1, hN1⟩ := exists_prefix_small hρ0 hρ1 hx hε
  refine ⟨N1, fun n hn => ?_⟩
  have := T.norm_zcoeff_neg_le (n := n) (div_nonneg hε.le (zpow_pos hρ0 n).le)
    (fun m hm => by rw [le_div_iff₀ (zpow_pos hρ0 n)]; exact hN1 n hn m hm)
  rwa [le_div_iff₀ (zpow_pos hρ0 n)] at this
theorem gaussNorm_zcoeff_neg {x : Γ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (hx : ConvergesAt (T.zcoeff x) ρ) :
    gaussNorm (T.zcoeff (-x)) ρ = gaussNorm (T.zcoeff x) ρ := by
  refine le_antisymm (T.gaussNorm_zcoeff_neg_le hρ0 hρ1.le hx) ?_
  have := T.gaussNorm_zcoeff_neg_le hρ0 hρ1.le (T.convergesAt_zcoeff_neg hρ0 hρ1 hx)
  rwa [neg_neg] at this
theorem weight_natCast_le {x : Γ} (hx : ConvergesAt (T.zcoeff x) ρ) (i : ℕ) :
    ‖T.coeff x i‖ * ρ ^ (i : ℤ) ≤ gaussNorm (T.zcoeff x) ρ := by
  have := hx.le_gaussNorm (i : ℤ); rwa [T.zcoeff_natCast] at this
theorem gaussNorm_zcoeff_mul_le {x y : Γ} (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1)
    (hx : ConvergesAt (T.zcoeff x) ρ) (hy : ConvergesAt (T.zcoeff y) ρ) :
    gaussNorm (T.zcoeff (x * y)) ρ ≤ gaussNorm (T.zcoeff x) ρ * gaussNorm (T.zcoeff y) ρ := by
  have hgx := gaussNorm_nonneg (a := T.zcoeff x) hρ0
  have hgy := gaussNorm_nonneg (a := T.zcoeff y) hρ0
  refine gaussNorm_le fun n => ?_
  have := T.norm_zcoeff_mul_le (n := n) (div_nonneg (mul_nonneg hgx hgy) (zpow_pos hρ0 n).le)
    fun i j hij => by
      rw [le_div_iff₀ (zpow_pos hρ0 n)]
      calc ‖T.zcoeff x i‖ * ‖T.zcoeff y j‖ * ρ ^ n
          ≤ ‖T.zcoeff x i‖ * ‖T.zcoeff y j‖ * ρ ^ (i + j) :=
            mul_le_mul_of_nonneg_left (zpow_le_zpow_right_of_le_one₀ hρ0 hρ1 hij) (by positivity)
        _ = (‖T.zcoeff x i‖ * ρ ^ i) * (‖T.zcoeff y j‖ * ρ ^ j) := by
            rw [zpow_add₀ hρ0.ne']; ring
        _ ≤ _ := mul_le_mul (hx.le_gaussNorm i) (hy.le_gaussNorm j) (by positivity) hgx
  rwa [le_div_iff₀ (zpow_pos hρ0 n)] at this
theorem convergesAt_zcoeff_mul {x y : Γ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (hx : ConvergesAt (T.zcoeff x) ρ) (hy : ConvergesAt (T.zcoeff y) ρ) :
    ConvergesAt (T.zcoeff (x * y)) ρ := by
  refine convergesAt_of_eventually hρ0 (T.zcoeff_neg_exists _) fun ε hε => ?_
  have hgx : 0 ≤ gaussNorm (T.zcoeff x) ρ := gaussNorm_nonneg hρ0
  have hgy : 0 ≤ gaussNorm (T.zcoeff y) ρ := gaussNorm_nonneg hρ0
  set C := max (gaussNorm (T.zcoeff x) ρ) (gaussNorm (T.zcoeff y) ρ) + 1 with hCdef
  have hC : 0 < C := by positivity
  have hCx : gaussNorm (T.zcoeff x) ρ ≤ C := by linarith [le_max_left (gaussNorm (T.zcoeff x) ρ) (gaussNorm (T.zcoeff y) ρ)]
  have hCy : gaussNorm (T.zcoeff y) ρ ≤ C := by linarith [le_max_right (gaussNorm (T.zcoeff x) ρ) (gaussNorm (T.zcoeff y) ρ)]
  obtain ⟨N1, hN1⟩ := exists_prefix_small hρ0 hρ1 hx (div_pos hε hC)
  obtain ⟨N2, hN2⟩ := exists_prefix_small hρ0 hρ1 hy (div_pos hε hC)
  set N := max (max N1 N2) 0
  have coordinate_level_le : N1 ≤ N := (le_max_left N1 N2).trans (le_max_left _ 0)
  have hN2N : N2 ≤ N := (le_max_right N1 N2).trans (le_max_left _ 0)
  refine ⟨2 * N, fun n hn => ?_⟩
  have := T.norm_zcoeff_mul_le (x := x) (y := y) (n := n) (div_nonneg hε.le (zpow_pos hρ0 n).le) fun i j hij => by
    rw [le_div_iff₀ (zpow_pos hρ0 n)]
    rcases lt_or_ge i 0 with hi | hi
    · rw [T.zcoeff_of_neg _ hi, norm_zero, zero_mul, zero_mul]; exact hε.le
    rcases lt_or_ge j 0 with hj | hj
    · rw [T.zcoeff_of_neg _ hj, norm_zero, mul_zero, zero_mul]; exact hε.le
    by_cases h1 : N ≤ n - i
    · calc ‖T.zcoeff x i‖ * ‖T.zcoeff y j‖ * ρ ^ n
          = (‖T.zcoeff x i‖ * ρ ^ i) * (‖T.zcoeff y j‖ * ρ ^ (n - i)) := by
            rw [show ρ ^ n = ρ ^ i * ρ ^ (n - i) by rw [← zpow_add₀ hρ0.ne', add_sub_cancel]]; ring
        _ ≤ gaussNorm (T.zcoeff x) ρ * (ε / C) :=
            mul_le_mul (hx.le_gaussNorm i) (hN2 (n - i) (hN2N.trans h1) j (by omega))
              (by positivity) hgx
        _ ≤ C * (ε / C) := mul_le_mul_of_nonneg_right hCx (by positivity)
        _ = ε := by field_simp
    · calc ‖T.zcoeff x i‖ * ‖T.zcoeff y j‖ * ρ ^ n
          = (‖T.zcoeff x i‖ * ρ ^ (n - j)) * (‖T.zcoeff y j‖ * ρ ^ j) := by
            rw [show ρ ^ n = ρ ^ (n - j) * ρ ^ j by rw [← zpow_add₀ hρ0.ne', sub_add_cancel]]; ring
        _ ≤ (ε / C) * gaussNorm (T.zcoeff y) ρ :=
            mul_le_mul (hN1 (n - j) (coordinate_level_le.trans (by omega)) i (by omega)) (hy.le_gaussNorm j)
              (by positivity) (by positivity)
        _ ≤ (ε / C) * C := mul_le_mul_of_nonneg_left hCy (by positivity)
        _ = ε := by field_simp
  rwa [le_div_iff₀ (zpow_pos hρ0 n)] at this
theorem gaussNorm_lowIndex_zcoeff_mul {x y : Γ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (hx : ConvergesAt (T.zcoeff x) ρ) (hy : ConvergesAt (T.zcoeff y) ρ) (hx0 : x ≠ 0)
    (hy0 : y ≠ 0) :
    gaussNorm (T.zcoeff (x * y)) ρ = gaussNorm (T.zcoeff x) ρ * gaussNorm (T.zcoeff y) ρ ∧
      lowIndex (T.zcoeff (x * y)) ρ = lowIndex (T.zcoeff x) ρ + lowIndex (T.zcoeff y) ρ := by
  have hx0' : T.zcoeff x ≠ 0 := fun h => hx0 ((T.zcoeff_eq_zero_iff x).1 h)
  have hy0' : T.zcoeff y ≠ 0 := fun h => hy0 ((T.zcoeff_eq_zero_iff y).1 h)
  set gx := gaussNorm (T.zcoeff x) ρ with hgxdef
  set gy := gaussNorm (T.zcoeff y) ρ with hgydef
  have hgx : 0 < gx := gaussNorm_pos hρ0 hx hx0'
  have hgy : 0 < gy := gaussNorm_pos hρ0 hy hy0'
  have hi0 := lowIndex_mem hρ0 hx hx0'
  have hl0 := lowIndex_mem hρ0 hy hy0'
  have hi0nn : 0 ≤ lowIndex (T.zcoeff x) ρ := by
    by_contra h
    push_neg at h
    exact ne_zero_of_mem_domSet hρ0 hx hx0' hi0 (T.zcoeff_of_neg x h)
  have hl0nn : 0 ≤ lowIndex (T.zcoeff y) ρ := by
    by_contra h
    push_neg at h
    exact ne_zero_of_mem_domSet hρ0 hy hy0' hl0 (T.zcoeff_of_neg y h)
  obtain ⟨k0, hk0⟩ : ∃ k0 : ℕ, lowIndex (T.zcoeff x) ρ = k0 :=
    ⟨_, (Int.toNat_of_nonneg hi0nn).symm⟩
  obtain ⟨l0, hl0'⟩ : ∃ l0 : ℕ, lowIndex (T.zcoeff y) ρ = l0 :=
    ⟨_, (Int.toNat_of_nonneg hl0nn).symm⟩
  have hwk0 : ‖T.coeff x k0‖ * ρ ^ (k0 : ℤ) = gx := by
    have := hi0; rw [hk0] at this
    simp only [domSet, Set.mem_setOf_eq, T.zcoeff_natCast] at this; exact this
  have hwl0 : ‖T.coeff y l0‖ * ρ ^ (l0 : ℤ) = gy := by
    have := hl0; rw [hl0'] at this
    simp only [domSet, Set.mem_setOf_eq, T.zcoeff_natCast] at this; exact this
  have hlt_x : ∀ i < k0, ‖T.coeff x i‖ * ρ ^ (i : ℤ) < gx := fun i hi => by
    have := weight_lt_of_lt_lowIndex hρ0 hx hx0' (n := i) (by rw [hk0]; exact_mod_cast hi)
    rwa [T.zcoeff_natCast] at this
  have hlt_y : ∀ i < l0, ‖T.coeff y i‖ * ρ ^ (i : ℤ) < gy := fun i hi => by
    have := weight_lt_of_lt_lowIndex hρ0 hy hy0' (n := i) (by rw [hl0']; exact_mod_cast hi)
    rwa [T.zcoeff_natCast] at this
  obtain ⟨gA, hgA, hgA0, hgA'⟩ := exists_lt_bound hgx hlt_x
  obtain ⟨gC, hgC, hgC0, hgC'⟩ := exists_lt_bound hgy hlt_y
  have wA : ∀ i, ‖T.coeff (T.partialSum x k0) i‖ * ρ ^ (i : ℤ) ≤ gA := fun i => by
    rw [partialSum, coeff_finSum]
    split_ifs with h
    · exact hgA' i h
    · rw [norm_zero, zero_mul]; exact hgA0
  have wC : ∀ i, ‖T.coeff (T.partialSum y l0) i‖ * ρ ^ (i : ℤ) ≤ gC := fun i => by
    rw [partialSum, coeff_finSum]
    split_ifs with h
    · exact hgC' i h
    · rw [norm_zero, zero_mul]; exact hgC0
  have wX1 : ∀ i, ‖T.coeff (x - T.partialSum x k0) i‖ * ρ ^ (i : ℤ) ≤ gx := fun i => by
    rw [coeff_sub_partialSum]
    split_ifs
    · rw [norm_zero, zero_mul]; exact hgx.le
    · exact T.weight_natCast_le hx i
  have wy : ∀ j, ‖T.coeff y j‖ * ρ ^ (j : ℤ) ≤ gy := T.weight_natCast_le hy
  have key : ∀ (u v : Γ) (Mu Mv : ℝ), 0 ≤ Mu → 0 ≤ Mv →
      (∀ i, ‖T.coeff u i‖ * ρ ^ (i : ℤ) ≤ Mu) → (∀ j, ‖T.coeff v j‖ * ρ ^ (j : ℤ) ≤ Mv) →
      ∀ m : ℕ, T.PrefixLe (u * v) m (Mu * Mv / ρ ^ (m : ℤ)) := by
    intro u v Mu Mv hMu hMv hu hv m
    refine T.prefixLe_mul (div_nonneg (mul_nonneg hMu hMv) (zpow_pos hρ0 _).le) fun i j hij => ?_
    rw [le_div_iff₀ (zpow_pos hρ0 _)]
    calc ‖T.coeff u i‖ * ‖T.coeff v j‖ * ρ ^ (m : ℤ)
        ≤ ‖T.coeff u i‖ * ‖T.coeff v j‖ * ρ ^ ((i : ℤ) + j) :=
          mul_le_mul_of_nonneg_left
            (zpow_le_zpow_right_of_le_one₀ hρ0 hρ1.le (by exact_mod_cast hij)) (by positivity)
      _ = (‖T.coeff u i‖ * ρ ^ (i : ℤ)) * (‖T.coeff v j‖ * ρ ^ (j : ℤ)) := by
          rw [zpow_add₀ hρ0.ne']; ring
      _ ≤ Mu * Mv := mul_le_mul (hu i) (hv j) (by positivity) hMu
  set β := max (gA * gy) (gx * gC) with hβdef
  have hβ : β < gx * gy := max_lt (mul_lt_mul_of_pos_right hgA hgy) (mul_lt_mul_of_pos_left hgC hgx)
  set E := T.partialSum x k0 * y + (x - T.partialSum x k0) * T.partialSum y l0 with hEdef
  have hE : ∀ m : ℕ, T.PrefixLe E m (β / ρ ^ (m : ℤ)) := fun m =>
    T.prefixLe_add
      ((key _ _ gA gy hgA0 hgy.le wA wy m).mono
        (div_le_div_of_nonneg_right (le_max_left _ _) (zpow_pos hρ0 _).le))
      ((key _ _ gx gC hgx.le hgC0 wX1 wC m).mono
        (div_le_div_of_nonneg_right (le_max_right _ _) (zpow_pos hρ0 _).le))
  set n := k0 + l0 with hndef
  have hX1Y1 : (x - T.partialSum x k0) * (y - T.partialSum y l0) =
      T.π ^ n * (T.tail^[k0] x * T.tail^[l0] y) := by
    rw [sub_partialSum, sub_partialSum, hndef, pow_add]; ring
  have hxy : x * y = E + (x - T.partialSum x k0) * (y - T.partialSum y l0) := by
    rw [hEdef]; ring
  have hcn : T.coeff ((x - T.partialSum x k0) * (y - T.partialSum y l0)) n =
      T.coeff x k0 * T.coeff y l0 := by
    have := T.coeff_π_pow_mul_add n (T.tail^[k0] x * T.tail^[l0] y) 0
    rw [zero_add] at this
    rw [hX1Y1, this, coeff_zero, map_mul]; rfl
  have hlow : ∀ m < n, ‖T.coeff (x * y) m‖ * ρ ^ (m : ℤ) ≤ β := fun m hm => by
    have e := T.coeff_eq_coeff_of_sub_mem (x := x * y) (y := E) (n := m)
      (by rw [hxy, add_sub_cancel_left, hX1Y1]; exact T.π_pow_mul_mem (by omega) _) m le_rfl
    rw [e]
    have := hE m m le_rfl
    rwa [le_div_iff₀ (zpow_pos hρ0 _)] at this
  have hn : gx * gy ≤ ‖T.coeff (x * y) n‖ * ρ ^ (n : ℤ) := by
    by_contra hcon
    push_neg at hcon
    have hβ' : max β (‖T.coeff (x * y) n‖ * ρ ^ (n : ℤ)) < gx * gy := max_lt hβ hcon
    have h1 : T.PrefixLe (x * y) n (max β (‖T.coeff (x * y) n‖ * ρ ^ (n : ℤ)) / ρ ^ (n : ℤ)) :=
      fun m hm => by
        rcases hm.lt_or_eq with hm | rfl
        · exact norm_le_div_of_weight hρ0 hρ1.le (by exact_mod_cast hm.le)
            ((hlow m hm).trans (le_max_left _ _))
        · exact norm_le_div_of_weight hρ0 hρ1.le le_rfl (le_max_right _ _)
    have h2 := T.prefixLe_sub h1 ((hE n).mono
      (div_le_div_of_nonneg_right (le_max_left _ _) (zpow_pos hρ0 _).le))
    have h3 : x * y - E = (x - T.partialSum x k0) * (y - T.partialSum y l0) := by
      rw [hxy, add_sub_cancel_left]
    rw [h3] at h2
    have := h2 n le_rfl
    rw [hcn, norm_mul, le_div_iff₀ (zpow_pos hρ0 _)] at this
    have e : ‖T.coeff x k0‖ * ‖T.coeff y l0‖ * ρ ^ (n : ℤ) = gx * gy := by
      rw [← hwk0, ← hwl0, hndef]; push_cast; rw [zpow_add₀ hρ0.ne']; ring
    linarith
  have hc := T.convergesAt_zcoeff_mul hρ0 hρ1 hx hy
  have hxyn : T.zcoeff (x * y) ≠ 0 := by
    intro h
    have := congrFun h (n : ℤ)
    rw [T.zcoeff_natCast, Pi.zero_apply] at this
    rw [this, norm_zero, zero_mul] at hn
    linarith [mul_pos hgx hgy]
  have hg : gaussNorm (T.zcoeff (x * y)) ρ = gx * gy :=
    le_antisymm (T.gaussNorm_zcoeff_mul_le hρ0 hρ1.le hx hy)
      (hn.trans (T.weight_natCast_le hc n))
  refine ⟨hg, ?_⟩
  have hmem : (n : ℤ) ∈ domSet (T.zcoeff (x * y)) ρ := by
    simp only [domSet, Set.mem_setOf_eq, T.zcoeff_natCast]
    exact le_antisymm (T.weight_natCast_le hc n) (hg ▸ hn)
  rw [hk0, hl0']
  refine le_antisymm ?_ ?_
  · have := lowIndex_le hρ0 hc hxyn hmem; rw [hndef] at this; exact_mod_cast this
  · by_contra hcon
    push_neg at hcon
    have hj := lowIndex_mem hρ0 hc hxyn
    set j := lowIndex (T.zcoeff (x * y)) ρ
    simp only [domSet, Set.mem_setOf_eq] at hj
    rcases lt_or_ge j 0 with hj0 | hj0
    · rw [T.zcoeff_of_neg _ hj0, norm_zero, zero_mul, hg] at hj
      linarith [mul_pos hgx hgy]
    · obtain ⟨m, hm⟩ : ∃ m : ℕ, j = m := ⟨_, (Int.toNat_of_nonneg hj0).symm⟩
      rw [hm, T.zcoeff_natCast, hg] at hj
      have hmn : m < n := by rw [hndef]; push_cast at hcon; omega
      linarith [hlow m hmn]
theorem gaussNorm_zcoeff_mul {x y : Γ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (hx : ConvergesAt (T.zcoeff x) ρ) (hy : ConvergesAt (T.zcoeff y) ρ) :
    gaussNorm (T.zcoeff (x * y)) ρ = gaussNorm (T.zcoeff x) ρ * gaussNorm (T.zcoeff y) ρ := by
  by_cases hx0 : x = 0
  · subst hx0; simp [zcoeff, gaussNorm]
  by_cases hy0 : y = 0
  · subst hy0; simp [zcoeff, gaussNorm]
  exact (T.gaussNorm_lowIndex_zcoeff_mul hρ0 hρ1 hx hy hx0 hy0).1
end TeichLift
section Shift
variable {L : Type*} [NontriviallyNormedField L] [IsUltrametricDist L] {a : ℤ → L} {ρ : ℝ}
theorem weight_shift (hρ0 : 0 < ρ) (N k : ℤ) :
    ‖a (k + N)‖ * ρ ^ k = (‖a (k + N)‖ * ρ ^ (k + N)) * ρ ^ (-N) := by
  rw [mul_assoc, ← zpow_add₀ hρ0.ne', add_neg_cancel_right]
theorem convergesAt_shift (hρ0 : 0 < ρ) (h : ConvergesAt a ρ) (N : ℤ) :
    ConvergesAt (fun k => a (k + N)) ρ := by
  have h1 : Tendsto (fun k : ℤ => ‖a (k + N)‖ * ρ ^ (k + N)) cofinite (𝓝 0) :=
    h.comp (add_left_injective N).tendsto_cofinite
  have := h1.mul_const (ρ ^ (-N))
  rw [zero_mul] at this
  refine this.congr fun k => ?_
  rw [weight_shift hρ0]
theorem convergesAt_shift_iff (hρ0 : 0 < ρ) (N : ℤ) :
    ConvergesAt (fun k => a (k + N)) ρ ↔ ConvergesAt a ρ := by
  refine ⟨fun h => ?_, fun h => convergesAt_shift hρ0 h N⟩
  have := convergesAt_shift hρ0 h (-N)
  simpa using this
theorem gaussNorm_shift (hρ0 : 0 < ρ) (N : ℤ) :
    gaussNorm (fun k => a (k + N)) ρ = gaussNorm a ρ * ρ ^ (-N) := by
  unfold gaussNorm
  simp_rw [weight_shift hρ0 N]
  rw [← Real.iSup_mul_of_nonneg (zpow_pos hρ0 _).le]
  congr 1
  exact (Equiv.addRight N).iSup_comp (g := fun j => ‖a j‖ * ρ ^ j)
theorem convergesAt_of_le (hneg : ∃ N, ∀ n < N, a n = 0) (h : ConvergesAt a ρ)
    {ρ' : ℝ} (hρ' : 0 < ρ') (hle : ρ' ≤ ρ) : ConvergesAt a ρ' := by
  refine convergesAt_of_eventually hρ' hneg fun ε hε => ?_
  obtain ⟨B, hB⟩ := (h.finite_le hε).bddAbove
  refine ⟨max (B + 1) 0, fun n hn => ?_⟩
  have hn0 : 0 ≤ n := le_of_max_le_right hn
  have h1 : ‖a n‖ * ρ' ^ n ≤ ‖a n‖ * ρ ^ n :=
    mul_le_mul_of_nonneg_left (by
      obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hn0
      rw [zpow_natCast, zpow_natCast]; exact pow_le_pow_left₀ hρ'.le hle m) (norm_nonneg _)
  refine h1.trans (le_of_lt (not_le.1 fun hc => ?_))
  have := hB (show n ∈ {n | ε ≤ ‖a n‖ * ρ ^ n} from hc)
  have := le_of_max_le_left hn
  omega
end Shift
namespace TeichLift
variable {p : ℕ} [hp : Fact p.Prime] {L : Type*} [NontriviallyNormedField L] [IsUltrametricDist L]
  [CharP L p] [PerfectRing L p] {Γ : Type*} [CommRing Γ] (T : TeichLift p L Γ) {ρ : ℝ}
theorem zcoeff_π_pow_mul (M : ℕ) (z : Γ) (j : ℤ) : T.zcoeff (T.π ^ M * z) (j + M) = T.zcoeff z j := by
  rcases lt_or_ge j 0 with hj | hj
  · rw [T.zcoeff_of_neg z hj]
    rcases lt_or_ge (j + M) 0 with h2 | h2
    · exact T.zcoeff_of_neg _ h2
    · obtain ⟨m, hm⟩ : ∃ m : ℕ, j + M = m := ⟨_, (Int.toNat_of_nonneg h2).symm⟩
      rw [hm, zcoeff_natCast]
      exact T.coeff_π_pow_mul_of_lt _ (by omega)
  · lift j to ℕ using hj
    rw [show (j : ℤ) + M = ((j + M : ℕ) : ℤ) by push_cast; ring, zcoeff_natCast, zcoeff_natCast,
      coeff_π_pow_mul_add]
theorem zcoeff_one : T.zcoeff 1 = Pi.single 0 1 := by
  funext n
  rcases lt_or_ge n 0 with hn | hn
  · rw [T.zcoeff_of_neg _ hn, Pi.single_apply, if_neg hn.ne]
  · lift n to ℕ using hn
    rw [zcoeff_natCast, ← T.teich_one, coeff_teich, Pi.single_apply]
    simp
abbrev B := Localization.Away T.π
theorem algebraMap_injective : Function.Injective (algebraMap Γ T.B) :=
  IsLocalization.injective (M := Submonoid.powers T.π) T.B
    (Submonoid.powers_le.2 T.π_mem_nonZeroDivisors)
def coeffB (b : T.B) (k : ℤ) : L :=
  T.zcoeff (IsLocalization.Away.surj T.π b).choose_spec.choose
    (k + (IsLocalization.Away.surj T.π b).choose)
theorem coeffB_eq {b : T.B} {x : Γ} {N : ℕ} (h : b * algebraMap Γ T.B T.π ^ N = algebraMap Γ T.B x) :
    T.coeffB b = fun k => T.zcoeff x (k + N) := by
  set N' := (IsLocalization.Away.surj T.π b).choose
  set x' := (IsLocalization.Away.surj T.π b).choose_spec.choose
  have h' : b * algebraMap Γ T.B T.π ^ N' = algebraMap Γ T.B x' :=
    (IsLocalization.Away.surj T.π b).choose_spec.choose_spec
  have key : T.π ^ N * x' = T.π ^ N' * x := by
    apply T.algebraMap_injective
    simp only [map_mul, map_pow, ← h, ← h']
    ring
  funext k
  simp only [coeffB]
  rw [← T.zcoeff_π_pow_mul N x' (k + N'), key, show k + (N' : ℤ) + N = k + N + N' by ring,
    T.zcoeff_π_pow_mul]
theorem convergesAt_pi_single (n₀ : ℤ) (c : L) (ρ : ℝ) : ConvergesAt (Pi.single n₀ c) ρ := by
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [(Set.finite_singleton n₀).compl_mem_cofinite] with n hn
  simp [Pi.single_apply, show n ≠ n₀ from hn]
theorem coeffB_algebraMap (x : Γ) : T.coeffB (algebraMap Γ T.B x) = T.zcoeff x := by
  rw [T.coeffB_eq (x := x) (N := 0) (by simp)]; simp
theorem coeffB_neg_exists (b : T.B) : ∃ N, ∀ n < N, T.coeffB b n = 0 := by
  obtain ⟨n, x, hx⟩ := IsLocalization.Away.surj T.π b
  refine ⟨-n, fun k hk => ?_⟩
  rw [T.coeffB_eq hx]
  exact T.zcoeff_of_neg _ (by omega)
theorem exists_common (b c : T.B) : ∃ (x y : Γ) (N : ℕ),
    b * algebraMap Γ T.B T.π ^ N = algebraMap Γ T.B x ∧
      c * algebraMap Γ T.B T.π ^ N = algebraMap Γ T.B y := by
  obtain ⟨n, x, hx⟩ := IsLocalization.Away.surj T.π b
  obtain ⟨m, y, hy⟩ := IsLocalization.Away.surj T.π c
  refine ⟨x * T.π ^ m, y * T.π ^ n, n + m, ?_, ?_⟩
  · rw [pow_add, ← mul_assoc, hx, map_mul, map_pow]
  · rw [pow_add, mul_comm (_ ^ n), ← mul_assoc, hy, map_mul, map_pow]
variable {b c : T.B}
theorem convergesAt_coeffB_add (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (hb : ConvergesAt (T.coeffB b) ρ)
    (hc : ConvergesAt (T.coeffB c) ρ) :
    ConvergesAt (T.coeffB (b + c)) ρ ∧
      gaussNorm (T.coeffB (b + c)) ρ ≤ max (gaussNorm (T.coeffB b) ρ) (gaussNorm (T.coeffB c) ρ) := by
  obtain ⟨x, y, N, hx, hy⟩ := T.exists_common b c
  have hxy : (b + c) * algebraMap Γ T.B T.π ^ N = algebraMap Γ T.B (x + y) := by
    rw [add_mul, hx, hy, map_add]
  rw [T.coeffB_eq hx, convergesAt_shift_iff hρ0] at hb
  rw [T.coeffB_eq hy, convergesAt_shift_iff hρ0] at hc
  rw [T.coeffB_eq hxy, T.coeffB_eq hx, T.coeffB_eq hy, convergesAt_shift_iff hρ0,
    gaussNorm_shift hρ0, gaussNorm_shift hρ0, gaussNorm_shift hρ0]
  refine ⟨T.convergesAt_zcoeff_add hρ0 hρ1 hb hc, ?_⟩
  rw [← max_mul_of_nonneg _ _ (zpow_pos hρ0 _).le]
  exact mul_le_mul_of_nonneg_right (T.gaussNorm_zcoeff_add_le hρ0 hρ1.le hb hc)
    (zpow_pos hρ0 _).le
theorem convergesAt_coeffB_neg (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (hb : ConvergesAt (T.coeffB b) ρ) :
    ConvergesAt (T.coeffB (-b)) ρ ∧ gaussNorm (T.coeffB (-b)) ρ = gaussNorm (T.coeffB b) ρ := by
  obtain ⟨n, x, hx⟩ := IsLocalization.Away.surj T.π b
  have hx' : (-b) * algebraMap Γ T.B T.π ^ n = algebraMap Γ T.B (-x) := by
    rw [neg_mul, hx, map_neg]
  rw [T.coeffB_eq hx, convergesAt_shift_iff hρ0] at hb
  rw [T.coeffB_eq hx', T.coeffB_eq hx, convergesAt_shift_iff hρ0, gaussNorm_shift hρ0,
    gaussNorm_shift hρ0, T.gaussNorm_zcoeff_neg hρ0 hρ1 hb]
  exact ⟨T.convergesAt_zcoeff_neg hρ0 hρ1 hb, rfl⟩
theorem convergesAt_coeffB_mul (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (hb : ConvergesAt (T.coeffB b) ρ)
    (hc : ConvergesAt (T.coeffB c) ρ) :
    ConvergesAt (T.coeffB (b * c)) ρ ∧
      gaussNorm (T.coeffB (b * c)) ρ = gaussNorm (T.coeffB b) ρ * gaussNorm (T.coeffB c) ρ := by
  obtain ⟨x, y, N, hx, hy⟩ := T.exists_common b c
  have hxy : (b * c) * algebraMap Γ T.B T.π ^ (N + N) = algebraMap Γ T.B (x * y) := by
    rw [pow_add, map_mul, ← hx, ← hy]; ring
  rw [T.coeffB_eq hx, convergesAt_shift_iff hρ0] at hb
  rw [T.coeffB_eq hy, convergesAt_shift_iff hρ0] at hc
  rw [T.coeffB_eq hxy, T.coeffB_eq hx, T.coeffB_eq hy, convergesAt_shift_iff hρ0,
    gaussNorm_shift hρ0, gaussNorm_shift hρ0, gaussNorm_shift hρ0,
    T.gaussNorm_zcoeff_mul hρ0 hρ1 hb hc]
  refine ⟨T.convergesAt_zcoeff_mul hρ0 hρ1 hb hc, ?_⟩
  push_cast
  rw [neg_add, zpow_add₀ hρ0.ne']; ring
def Econ (ρ : Set.Ioo (0 : ℝ) 1) : Subring T.B where
  carrier := {b | ConvergesAt (T.coeffB b) ρ}
  zero_mem' := by
    show ConvergesAt (T.coeffB 0) ρ
    rw [← map_zero (algebraMap Γ T.B), coeffB_algebraMap, (T.zcoeff_eq_zero_iff 0).2 rfl]
    simpa using convergesAt_pi_single (L := L) 0 0 ρ
  one_mem' := by
    show ConvergesAt (T.coeffB 1) ρ
    rw [← map_one (algebraMap Γ T.B), coeffB_algebraMap, zcoeff_one]
    exact convergesAt_pi_single 0 1 ρ
  add_mem' hb hc := (T.convergesAt_coeffB_add ρ.2.1 ρ.2.2 hb hc).1
  mul_mem' hb hc := (T.convergesAt_coeffB_mul ρ.2.1 ρ.2.2 hb hc).1
  neg_mem' hb := (T.convergesAt_coeffB_neg ρ.2.1 ρ.2.2 hb).1
theorem Econ_anti {ρ ρ' : Set.Ioo (0 : ℝ) 1} (h : (ρ' : ℝ) ≤ ρ) : T.Econ ρ ≤ T.Econ ρ' :=
  fun _ hb => convergesAt_of_le (T.coeffB_neg_exists _) hb ρ'.2.1 h
def Gcon : Subring Γ where
  carrier := {x | ∃ ρ : Set.Ioo (0 : ℝ) 1, ConvergesAt (T.zcoeff x) ρ}
  zero_mem' := ⟨⟨1 / 2, by norm_num, by norm_num⟩, by
    rw [(T.zcoeff_eq_zero_iff 0).2 rfl]; simpa using convergesAt_pi_single (L := L) 0 0 (1 / 2)⟩
  one_mem' := ⟨⟨1 / 2, by norm_num, by norm_num⟩, by rw [zcoeff_one]; exact convergesAt_pi_single _ _ _⟩
  add_mem' := by
    rintro x y ⟨ρ₁, h₁⟩ ⟨ρ₂, h₂⟩
    refine ⟨⟨min ρ₁ ρ₂, lt_min ρ₁.2.1 ρ₂.2.1, min_lt_of_left_lt ρ₁.2.2⟩, ?_⟩
    exact T.convergesAt_zcoeff_add (lt_min ρ₁.2.1 ρ₂.2.1) (min_lt_of_left_lt ρ₁.2.2)
      (convergesAt_of_le (T.zcoeff_neg_exists x) h₁ (lt_min ρ₁.2.1 ρ₂.2.1) (min_le_left _ _))
      (convergesAt_of_le (T.zcoeff_neg_exists y) h₂ (lt_min ρ₁.2.1 ρ₂.2.1) (min_le_right _ _))
  mul_mem' := by
    rintro x y ⟨ρ₁, h₁⟩ ⟨ρ₂, h₂⟩
    refine ⟨⟨min ρ₁ ρ₂, lt_min ρ₁.2.1 ρ₂.2.1, min_lt_of_left_lt ρ₁.2.2⟩, ?_⟩
    exact T.convergesAt_zcoeff_mul (lt_min ρ₁.2.1 ρ₂.2.1) (min_lt_of_left_lt ρ₁.2.2)
      (convergesAt_of_le (T.zcoeff_neg_exists x) h₁ (lt_min ρ₁.2.1 ρ₂.2.1) (min_le_left _ _))
      (convergesAt_of_le (T.zcoeff_neg_exists y) h₂ (lt_min ρ₁.2.1 ρ₂.2.1) (min_le_right _ _))
  neg_mem' := by
    rintro x ⟨ρ, h⟩
    exact ⟨ρ, T.convergesAt_zcoeff_neg ρ.2.1 ρ.2.2 h⟩
def Edag : Subring T.B where
  carrier := {b | ∃ ρ : Set.Ioo (0 : ℝ) 1, ConvergesAt (T.coeffB b) ρ}
  zero_mem' := ⟨⟨1 / 2, by norm_num, by norm_num⟩, (T.Econ _).zero_mem⟩
  one_mem' := ⟨⟨1 / 2, by norm_num, by norm_num⟩, (T.Econ _).one_mem⟩
  add_mem' := by
    rintro x y ⟨ρ₁, h₁⟩ ⟨ρ₂, h₂⟩
    refine ⟨⟨min ρ₁ ρ₂, lt_min ρ₁.2.1 ρ₂.2.1, min_lt_of_left_lt ρ₁.2.2⟩, ?_⟩
    exact (T.Econ _).add_mem (T.Econ_anti (ρ := ρ₁) (min_le_left _ _) h₁)
      (T.Econ_anti (ρ := ρ₂) (min_le_right _ _) h₂)
  mul_mem' := by
    rintro x y ⟨ρ₁, h₁⟩ ⟨ρ₂, h₂⟩
    refine ⟨⟨min ρ₁ ρ₂, lt_min ρ₁.2.1 ρ₂.2.1, min_lt_of_left_lt ρ₁.2.2⟩, ?_⟩
    exact (T.Econ _).mul_mem (T.Econ_anti (ρ := ρ₁) (min_le_left _ _) h₁)
      (T.Econ_anti (ρ := ρ₂) (min_le_right _ _) h₂)
  neg_mem' := by
    rintro x ⟨ρ, h⟩
    exact ⟨ρ, (T.Econ ρ).neg_mem h⟩
end TeichLift
end GroundTheory.PAdicHodge


