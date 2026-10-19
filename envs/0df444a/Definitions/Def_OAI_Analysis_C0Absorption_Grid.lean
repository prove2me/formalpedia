-- Prove2me | Definitions.Def_OAI_Analysis_C0Absorption_Grid
-- name    : OAI_Analysis_C0Absorption_Grid
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T21:15:31.003813+00:00
-- url     : https://prove2.me/theorems/15dbf3e3-9971-4d63-8042-5df34a927a34
-- title:
--   Band grids and Lipschitz partitions of unity on prefix cubes
-- statement:
--   These notions belong to the construction of a separable Banach space $Z$ that contains no linear copy of $c_0$, yet $Z\times c_0$ is bi-Lipschitz equivalent to $Z$ and $Z$ is Lipschitz-universal for separable metric spaces. $Z$ is a completion of the space of molecules on the unit ball of $c_0$ (finitely supported functions with total sum zero), normed by test functions from carefully chosen Lipschitz classes. For a band $j$, the prefix cube is $[-1,1]^j$, the restriction of a point of the unit ball of $c_0$ to its first $j$ coordinates, which is $1$-Lipschitz. The band grid consists of the points with coordinates in $\{k/2^j:|k|\le2^j\}$.
--
--   1. **Bumps.** For a grid point $\xi$, $\mathrm{bump}_\xi(s)=\max(0,1-d(s,\xi)2^j)$ and $\mathrm{vector}_\xi(s)=\min(1,\max(0,2-d(s,\xi)2^j))$. Both are $2^j$-Lipschitz, and the vector equals $1$ wherever the bump is positive.
--   2. **Rows.** The denominator $\sum_\xi\mathrm{bump}_\xi\ge\frac12$, and the normalized rows
--   $$
--   \mathrm{row}_\xi=\frac{\mathrm{bump}_\xi}{\sum_\eta\mathrm{bump}_\eta}
--   $$
--   form a partition of unity with $\sum_\xi\mathrm{row}_\xi\,\mathrm{vector}_\xi=1$.
--   3. **Stability.** $\sum_\xi|\mathrm{row}_\xi(s)-\mathrm{row}_\xi(t)|\le L_j\,d(s,t)$, with $L_j=4\cdot\#\mathrm{grid}\cdot2^j$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/C0Absorption/Grid.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/C0Absorption/Grid.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the C0Absorption mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_C0Absorption
import Definitions.Def_OAI_Analysis_C0Absorption_Molecules
import Definitions.Def_OAI_Analysis_C0Absorption_Norm
import Definitions.Def_OAI_Analysis_C0Absorption_Completion
import Definitions.Def_OAI_Analysis_C0Absorption_Signs
import Definitions.Def_OAI_Analysis_C0Absorption_Lists
import Definitions.Def_OAI_Analysis_C0Absorption_Pairings
import Definitions.Def_OAI_Analysis_C0Absorption_Localization
import Definitions.Def_OAI_Analysis_C0Absorption_Coordinates
import Definitions.Def_OAI_Analysis_C0Absorption_Triangular
import Definitions.Def_OAI_Analysis_C0Absorption_Tests
import Definitions.Def_OAI_Analysis_C0Absorption_Duality
import Definitions.Def_OAI_Analysis_C0Absorption_Selection
import Definitions.Def_OAI_Analysis_C0Absorption_Supports
import Definitions.Def_OAI_Analysis_C0Absorption_Operations
import Definitions.Def_OAI_Analysis_C0Absorption_Detection

namespace OAI

open Set Filter Topology
open scoped NNReal BigOperators ZeroAtInfty
open NormedSpace

namespace C0Absorption
noncomputable section
open Set Filter Topology
open scoped NNReal BigOperators ZeroAtInfty

abbrev BandGrid (j : ℕ) := Fin j → GridIndex (2^j)
abbrev PrefixCube (j : ℕ) := Fin j → Icc (-1 : ℝ) 1

def bandPoint (j : ℕ) (ξ : BandGrid j) : PrefixCube j :=
  fun k => gridPoint (2^j) (by positivity) (ξ k)

def prefixRestrict (j : ℕ) (s : C0Ball) : PrefixCube j := fun k =>
  ⟨s.val k, abs_le.mp ((c0_norm_apply_le s.val k).trans (by
    have hh := s.property
    simpa only [Metric.mem_closedBall,dist_zero_right] using hh))⟩

theorem prefixRestrict_lipschitz (j : ℕ) : LipschitzWith 1 (prefixRestrict j) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [NNReal.coe_one,one_mul]
  apply (dist_pi_le_iff dist_nonneg).mpr
  intro k
  exact BoundedContinuousFunction.dist_coe_le_dist (f := x.val.toBCF) (g := y.val.toBCF) k

def bandBump (j : ℕ) (ξ : BandGrid j) (s : PrefixCube j) : ℝ :=
  max 0 (1-dist s (bandPoint j ξ)/dyadic j)

def bandVector (j : ℕ) (ξ : BandGrid j) (s : PrefixCube j) : ℝ :=
  min 1 (max 0 (2-dist s (bandPoint j ξ)/dyadic j))

def bandDenominator (j : ℕ) (s : PrefixCube j) : ℝ := ∑ ξ : BandGrid j, bandBump j ξ s

def bandRow (j : ℕ) (ξ : BandGrid j) (s : PrefixCube j) : ℝ :=
  bandBump j ξ s / bandDenominator j s

theorem bandBump_nonneg (j : ℕ) (ξ : BandGrid j) (s : PrefixCube j) :
    0 ≤ bandBump j ξ s := le_max_left _ _

theorem bandVector_nonneg (j : ℕ) (ξ : BandGrid j) (s : PrefixCube j) :
    0 ≤ bandVector j ξ s := le_min zero_le_one (le_max_left _ _)

theorem bandVector_le_one (j : ℕ) (ξ : BandGrid j) (s : PrefixCube j) :
    bandVector j ξ s ≤ 1 := min_le_left _ _

theorem bandVector_eq_one {j : ℕ} {ξ : BandGrid j} {s : PrefixCube j}
    (h : bandBump j ξ s ≠ 0) : bandVector j ξ s=1 := by
  have hh : 0 < 1-dist s (bandPoint j ξ)/dyadic j := by
    by_contra hn
    exact h (max_eq_left (by linarith))
  unfold bandVector
  rw [min_eq_left]
  exact le_max_of_le_right (by linarith)

theorem bandVector_support {j : ℕ} {ξ : BandGrid j} {s : PrefixCube j}
    (h : bandVector j ξ s ≠ 0) : dist s (bandPoint j ξ) < 2*dyadic j := by
  have hmax : max 0 (2-dist s (bandPoint j ξ)/dyadic j) ≠ 0 := by
    intro hh
    exact h (by simp only [bandVector,hh,min_eq_right zero_le_one])
  have hh : 0 < 2-dist s (bandPoint j ξ)/dyadic j := by
    by_contra hn
    exact hmax (max_eq_left (by linarith))
  exact (div_lt_iff₀ (dyadic_pos j)).mp (by linarith)

theorem const_dist_div_lipschitz {X : Type*} [PseudoMetricSpace X] (q : X) (a : ℝ) (j : ℕ) :
    LipschitzWith (2^j) (fun s => a-dist s q/dyadic j) := by
  apply LipschitzWith.of_dist_le_mul
  intro s t
  rw [Real.dist_eq,sub_sub_sub_cancel_left,← sub_div,abs_div,abs_of_pos (dyadic_pos j)]
  calc
    _ ≤ dist t s/dyadic j := div_le_div_of_nonneg_right (abs_dist_sub_le t s q) (dyadic_pos j).le
    _ = (2^j : ℝ≥0)*dist s t := by simp only [dyadic,div_inv_eq_mul,NNReal.coe_pow,NNReal.coe_ofNat,dist_comm]; ring

theorem bandBump_lipschitz (j : ℕ) (ξ : BandGrid j) :
    LipschitzWith (2^j) (bandBump j ξ) :=
  (const_dist_div_lipschitz (bandPoint j ξ) 1 j).const_max 0

theorem bandVector_lipschitz (j : ℕ) (ξ : BandGrid j) :
    LipschitzWith (2^j) (bandVector j ξ) :=
  ((const_dist_div_lipschitz (bandPoint j ξ) 2 j).const_max 0).const_min 1

theorem bandDenominator_ge (j : ℕ) (s : PrefixCube j) : 1/2 ≤ bandDenominator j s := by
  classical
  let ξ : BandGrid j := fun k => nearestGridIndex (2^j) (by positivity) (s k)
  have hd : dist s (bandPoint j ξ) ≤ dyadic j/2 := by
    apply (dist_pi_le_iff (div_nonneg (dyadic_pos j).le (by norm_num) : 0 ≤ dyadic j/2)).mpr
    intro k
    have hh := nearestGrid_dist (2^j) (by positivity) (s k)
    change dist (s k) (gridPoint _ _ (nearestGridIndex _ _ (s k))) ≤ _
    refine hh.trans_eq ?_
    push_cast
    unfold dyadic
    ring
  have hb : 1/2 ≤ bandBump j ξ s := by
    apply le_max_of_le_right
    have hh : dist s (bandPoint j ξ)/dyadic j ≤ 1/2 := (div_le_iff₀ (dyadic_pos j)).mpr (by linarith)
    linarith
  exact hb.trans (Finset.single_le_sum (fun a _ => bandBump_nonneg j a s) (Finset.mem_univ ξ))

theorem bandDenominator_pos (j : ℕ) (s : PrefixCube j) : 0 < bandDenominator j s :=
  lt_of_lt_of_le (by norm_num) (bandDenominator_ge j s)

theorem bandRow_nonneg (j : ℕ) (ξ : BandGrid j) (s : PrefixCube j) :
    0 ≤ bandRow j ξ s := div_nonneg (bandBump_nonneg j ξ s) (bandDenominator_pos j s).le

theorem bandRow_sum (j : ℕ) (s : PrefixCube j) : ∑ ξ : BandGrid j, bandRow j ξ s=1 := by
  simp only [bandRow,← Finset.sum_div]
  change bandDenominator j s/bandDenominator j s=1
  exact div_self (bandDenominator_pos j s).ne'

theorem bandRow_vector (j : ℕ) (s : PrefixCube j) :
    ∑ ξ : BandGrid j, bandRow j ξ s*bandVector j ξ s=1 := by
  rw [← bandRow_sum j s]
  apply Finset.sum_congr rfl
  intro ξ _
  by_cases h : bandBump j ξ s=0
  · simp only [bandRow,h,zero_div,zero_mul]
  · rw [bandVector_eq_one h,mul_one]

theorem normalized_sum_distance {A : Type*} [Fintype A] (b c : A → ℝ)
    (_hb : ∀ i, 0 ≤ b i) (hc : ∀ i, 0 ≤ c i)
    (hB : 1/2 ≤ ∑ i,b i) (hC : 1/2 ≤ ∑ i,c i) :
    (∑ i, |b i/(∑ i,b i)-c i/(∑ i,c i)|) ≤ 4*∑ i,|b i-c i| := by
  let B := ∑ i,b i
  let C := ∑ i,c i
  have hB' : 0 < B := lt_of_lt_of_le (by norm_num) hB
  have hC' : 0 < C := lt_of_lt_of_le (by norm_num) hC
  have hdist : |C-B| ≤ ∑ i,|b i-c i| := by
    rw [abs_sub_comm]
    change |(∑ i,b i)-(∑ i,c i)| ≤ _
    rw [← Finset.sum_sub_distrib]
    exact Finset.abs_sum_le_sum_abs _ _
  have hrow : ∑ i,c i/C=1 := by rw [← Finset.sum_div]; exact div_self hC'.ne'
  have he (i : A) : b i/B-c i/C=(b i-c i)/B+(c i/C)*((C-B)/B) := by
    field_simp
    ; ring
  calc
    _ ≤ ∑ i, (|b i-c i|/B+(c i/C)*(|C-B|/B)) := by
      apply Finset.sum_le_sum
      intro i _
      rw [he]
      refine (abs_add_le _ _).trans_eq ?_
      simp only [abs_mul,abs_div,abs_of_pos hB',abs_of_nonneg (hc i),abs_of_pos hC']
    _ = (∑ i,|b i-c i|)/B+|C-B|/B := by
      rw [Finset.sum_add_distrib,← Finset.sum_div,← Finset.sum_mul,hrow,one_mul]
    _ ≤ (∑ i,|b i-c i|)/B+(∑ i,|b i-c i|)/B :=
      add_le_add_right ((div_le_div_iff_of_pos_right hB').mpr hdist) _
    _ ≤ 4*∑ i,|b i-c i| := by
      have hh : (∑ i,|b i-c i|)/B ≤ 2*∑ i,|b i-c i| := by
        apply (div_le_iff₀ hB').mpr
        have ha : 0 ≤ ∑ i,|b i-c i| := Finset.sum_nonneg (fun i _ => abs_nonneg _)
        nlinarith
      linarith

def bandL (j : ℕ) : ℝ≥0 := 4*Fintype.card (BandGrid j)*2^j

theorem bandRow_distance (j : ℕ) (s t : PrefixCube j) :
    (∑ ξ : BandGrid j,|bandRow j ξ s-bandRow j ξ t|) ≤ bandL j*dist s t := by
  refine (normalized_sum_distance (fun ξ => bandBump j ξ s) (fun ξ => bandBump j ξ t)
    (fun ξ => bandBump_nonneg j ξ s) (fun ξ => bandBump_nonneg j ξ t)
    (bandDenominator_ge j s) (bandDenominator_ge j t)).trans ?_
  calc
    _ ≤ 4*∑ ξ : BandGrid j, (2 : ℝ)^j*dist s t := by
      gcongr with ξ
      simpa only [Real.dist_eq,NNReal.coe_pow,NNReal.coe_ofNat] using
        (bandBump_lipschitz j ξ).dist_le_mul s t
    _ = bandL j*dist s t := by simp [bandL]; ring

end
end C0Absorption

end OAI


