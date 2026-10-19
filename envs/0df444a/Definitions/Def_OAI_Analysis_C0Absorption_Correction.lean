-- Prove2me | Definitions.Def_OAI_Analysis_C0Absorption_Correction
-- name    : OAI_Analysis_C0Absorption_Correction
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T21:26:04.38154+00:00
-- url     : https://prove2.me/theorems/d78ceb36-2108-430d-b1f1-4366edac284c
-- title:
--   Block vectors and rows weighted by radius and band
-- statement:
--   These notions belong to the construction of a separable Banach space $Z$ that contains no linear copy of $c_0$, yet $Z\times c_0$ is bi-Lipschitz equivalent to $Z$ and $Z$ is Lipschitz-universal for separable metric spaces. $Z$ is a completion of the space of molecules on the unit ball of $c_0$ (finitely supported functions with total sum zero), normed by test functions from carefully chosen Lipschitz classes. Levels are pairs $(i,n)$ with $J(i,n)=i+n+2$ bands. A label is a level together with a band $j\le J$ and a grid tag in the band grid of $[-1,1]^j$. The coordinates of $c_0$ are re-indexed by $\mathbb N\sqcup\mathrm{Labels}$ (row coordinates and label coordinates). For a level with local radius $r(s)$, the angle weights are $\theta_j=\theta(J,r(s),j)$. The band functions at band $j$ and tag $\xi$ are $\mathrm{vector}_\xi$ and $\mathrm{row}_\xi$ of the prefix of $s$.
--
--   1. **Block weights.**
--   $$
--   \mathrm{blockVector}(s)_{(j,\xi)}=\theta_j\cdot\mathrm{vector}_\xi\bigl(s|_{[0,j)}\bigr),\qquad\mathrm{blockRow}(s)_{(j,\xi)}=\theta_j\cdot\mathrm{row}_\xi\bigl(s|_{[0,j)}\bigr).
--   $$
--   2. **Properties.** Vectors lie in $[0,1]$, rows are nonnegative with $\sum\mathrm{row}\le2$, and $\sum_b\mathrm{row}_b\,\mathrm{vector}_b=1$, using $\sum_j\theta_j^2=1$.
--   3. **Weighted stability.** With $r=\min(r(s),r(t))$,
--   $$
--   r\sum_b|\mathrm{row}_b(s)-\mathrm{row}_b(t)|\le\eta\,d(s,t),\qquad r\,|\mathrm{vector}_b(s)-\mathrm{vector}_b(t)|\le\eta\,d(s,t),
--   $$
--   with $\eta=\frac1{1000}$. The radius schedule absorbs the large Lipschitz constants of fine bands.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/C0Absorption/Correction.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/C0Absorption/Correction.lean by skeleton subtraction
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
import Definitions.Def_OAI_Analysis_C0Absorption_Grid
import Definitions.Def_OAI_Analysis_C0Absorption_Weights
import Definitions.Def_OAI_Analysis_C0Absorption_Angles
import Definitions.Def_OAI_Analysis_C0Absorption_Blocks

namespace OAI

open Set Filter Topology
open scoped NNReal BigOperators ZeroAtInfty
open NormedSpace

namespace C0Absorption
noncomputable section
open Set Filter Topology
open scoped NNReal BigOperators ZeroAtInfty

def blockVector (lev : Level) (s : C0Ball) (b : Block lev) : ℝ :=
  theta (levelJ lev) (localRadius lev s.val) b.1 * bandVector b.1 b.2 (prefixRestrict b.1 s)

def blockRow (lev : Level) (s : C0Ball) (b : Block lev) : ℝ :=
  theta (levelJ lev) (localRadius lev s.val) b.1 * bandRow b.1 b.2 (prefixRestrict b.1 s)

theorem blockVector_nonneg (lev : Level) (s : C0Ball) (b : Block lev) :
    0≤blockVector lev s b := mul_nonneg (theta_nonneg _ _ _) (bandVector_nonneg _ _ _)

theorem blockVector_le_one (lev : Level) (s : C0Ball) (b : Block lev) :
    blockVector lev s b ≤ 1 := by
  calc
    _ ≤ 1*1 := mul_le_mul (theta_le_one _ _ _) (bandVector_le_one _ _ _) (bandVector_nonneg _ _ _) zero_le_one
    _ = 1 := one_mul _

theorem blockRow_nonneg (lev : Level) (s : C0Ball) (b : Block lev) :
    0≤blockRow lev s b := mul_nonneg (theta_nonneg _ _ _) (bandRow_nonneg _ _ _)

theorem blockRow_sum (lev : Level) (s : C0Ball) : ∑ b : Block lev,blockRow lev s b ≤ 2 := by
  change (∑ b : (j : Fin (levelJ lev+1)) × BandGrid j.val,
    theta (levelJ lev) (localRadius lev s.val) b.1 * bandRow b.1 b.2 (prefixRestrict b.1 s)) ≤ 2
  rw [Fintype.sum_sigma]
  simp only [← Finset.mul_sum,bandRow_sum,mul_one]
  exact theta_sum_le _ _

theorem blockRow_vector (lev : Level) (s : C0Ball) :
    ∑ b : Block lev, blockRow lev s b*blockVector lev s b=1 := by
  change (∑ b : (j : Fin (levelJ lev+1)) × BandGrid j.val,
    (theta (levelJ lev) (localRadius lev s.val) b.1 * bandRow b.1 b.2 (prefixRestrict b.1 s))*
    (theta (levelJ lev) (localRadius lev s.val) b.1 * bandVector b.1 b.2 (prefixRestrict b.1 s)))=1
  rw [Fintype.sum_sigma]
  have he (j : Fin (levelJ lev+1)) : (∑ ξ : BandGrid j,
    (theta (levelJ lev) (localRadius lev s.val) j*bandRow j ξ (prefixRestrict j s))*
    (theta (levelJ lev) (localRadius lev s.val) j*bandVector j ξ (prefixRestrict j s)))=
    theta (levelJ lev) (localRadius lev s.val) j^2 := by
    calc
      _ = ∑ ξ : BandGrid j, theta (levelJ lev) (localRadius lev s.val) j^2*
          (bandRow j ξ (prefixRestrict j s)*bandVector j ξ (prefixRestrict j s)) := by
        apply Finset.sum_congr rfl
        intro ξ _
        ring
      _ = _ := by rw [← Finset.mul_sum,bandRow_vector,mul_one]
  simp only [he]
  exact theta_squares _ _

theorem bandL_ge_dyadic_inv (j : ℕ) : (2 : ℝ)^j ≤ bandL j := by
  let : Nonempty (BandGrid j) := ⟨fun _ => ⟨0,by constructor; exact neg_nonpos.mpr (Int.natCast_nonneg _); exact Int.natCast_nonneg _⟩⟩
  have hc : (1 : ℝ) ≤ Fintype.card (BandGrid j) := by exact_mod_cast Fintype.card_pos
  simp only [bandL,NNReal.coe_mul,NNReal.coe_ofNat,NNReal.coe_natCast,NNReal.coe_pow]
  nlinarith [pow_pos (by norm_num : (0:ℝ)<2) j]

theorem bandVector_distance (j : ℕ) (ξ : BandGrid j) (s t : PrefixCube j) :
    |bandVector j ξ s-bandVector j ξ t| ≤ bandL j*dist s t := by
  exact ((bandVector_lipschitz j ξ).dist_le_mul s t).trans
    (mul_le_mul_of_nonneg_right (by exact_mod_cast bandL_ge_dyadic_inv j) dist_nonneg)

theorem theta_band_budget (J : ℕ) (j : Fin (J+1)) {r s δ D : ℝ}
    (hr : 0≤r) (hs : 0 ≤ s) (hδ : 0≤δ) (hD : D≤bandL j*δ) (hD0 : j.val=0 → D=0) :
    min r s*(theta J r j*D) ≤ (eta/4)*theta J r j*δ := by
  by_cases hj : j.val=0
  · rw [hD0 hj,mul_zero,mul_zero]
    exact mul_nonneg (mul_nonneg (div_nonneg eta_pos.le (by norm_num)) (theta_nonneg _ _ _)) hδ
  by_cases ht : theta J r j=0
  · simp only [ht,zero_mul,mul_zero,le_refl]
  have hm : min r s≤rho j := (min_le_left _ _).trans (theta_upper_support (by omega) (by omega) hr ht)
  have hL : min r s*bandL j≤eta/4 := by
    calc
      _ ≤ rho j*bandL j := mul_le_mul_of_nonneg_right hm (bandL j).coe_nonneg
      _ = bandL j*rho j := mul_comm _ _
      _ ≤ eta/4 := rho_lip_budget (by omega)
  calc
    _ ≤ min r s*(theta J r j*(bandL j*δ)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hD (theta_nonneg _ _ _)) (le_min hr hs)
    _ = (min r s*bandL j)*theta J r j*δ := by ring
    _ ≤ (eta/4)*theta J r j*δ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hL (theta_nonneg _ _ _)) hδ

theorem bandRow_scaled_difference {j : ℕ} (a b : ℝ) (ha : 0≤a) (s t : PrefixCube j) :
    (∑ ξ : BandGrid j,|a*bandRow j ξ s-b*bandRow j ξ t|) ≤
      |a-b|+a*(∑ ξ : BandGrid j,|bandRow j ξ s-bandRow j ξ t|) := by
  calc
    _ ≤ ∑ ξ : BandGrid j,(|a-b| *bandRow j ξ t+a*|bandRow j ξ s-bandRow j ξ t|) := by
      apply Finset.sum_le_sum
      intro ξ _
      rw [show a*bandRow j ξ s-b*bandRow j ξ t=(a-b)*bandRow j ξ t+a*(bandRow j ξ s-bandRow j ξ t) by ring]
      refine (abs_add_le _ _).trans_eq ?_
      simp only [abs_mul,abs_of_nonneg ha,abs_of_nonneg (bandRow_nonneg j ξ t)]
    _ = _ := by rw [Finset.sum_add_distrib,← Finset.mul_sum,← Finset.mul_sum,bandRow_sum,mul_one]

theorem blockRow_distance_decompose (lev : Level) (s t : C0Ball) :
    (∑ b : Block lev,|blockRow lev s b-blockRow lev t b|) ≤
      ∑ j : Fin (levelJ lev+1), (|theta (levelJ lev) (localRadius lev s.val) j-
        theta (levelJ lev) (localRadius lev t.val) j|+
          theta (levelJ lev) (localRadius lev s.val) j*
            ∑ ξ : BandGrid j,|bandRow j ξ (prefixRestrict j s)-bandRow j ξ (prefixRestrict j t)|) := by
  unfold blockRow
  rw [Fintype.sum_sigma]
  apply Finset.sum_le_sum
  intro j _
  exact bandRow_scaled_difference (j := j.val)
    (theta (levelJ lev) (localRadius lev s.val) j.val)
    (theta (levelJ lev) (localRadius lev t.val) j.val)
    (theta_nonneg _ _ _) (prefixRestrict j.val s) (prefixRestrict j.val t)

theorem blockRow_weighted_distance (lev : Level) (s t : C0Ball) :
    min (localRadius lev s.val) (localRadius lev t.val)*
      (∑ b : Block lev,|blockRow lev s b-blockRow lev t b|) ≤ eta*dist s t := by
  let J := levelJ lev
  let r := localRadius lev s.val
  let r' := localRadius lev t.val
  let δ := dist s t
  let D (j : Fin (J+1)) := ∑ ξ : BandGrid j,|bandRow j ξ (prefixRestrict j s)-bandRow j ξ (prefixRestrict j t)|
  have hr : 0≤r := finiteRadius_nonneg _ _
  have hr' : 0≤r' := finiteRadius_nonneg _ _
  have hrad : |r-r'|≤δ := by
    change dist (finiteRadius (radiusCoordinates lev) s.val) (finiteRadius (radiusCoordinates lev) t.val) ≤ dist s.val t.val
    simpa only [NNReal.coe_one,one_mul] using (finiteRadius_lipschitz (radiusCoordinates lev)).dist_le_mul s.val t.val
  have hD (j : Fin (J+1)) : D j≤bandL j*δ := by
    exact (bandRow_distance j _ _).trans (mul_le_mul_of_nonneg_left
      (by simpa only [NNReal.coe_one,one_mul] using (prefixRestrict_lipschitz j).dist_le_mul s t) (bandL j).coe_nonneg)
  have hD0 (j : Fin (J+1)) (hj : j.val=0) : D j=0 := by
    dsimp [D]
    have he : prefixRestrict j s=prefixRestrict j t := by rw [hj]; exact Subsingleton.elim _ _
    simp only [he,sub_self,abs_zero,Finset.sum_const_zero]
  have hsum := blockRow_distance_decompose lev s t
  have hschedule : min r r'*(∑ j : Fin (J+1),|theta J r j-theta J r' j|) ≤ (eta/2)*δ := by
    calc
      _ ≤ (Real.pi/scheduleH)*|r-r'| := theta_weighted_distance J hr hr'
      _ ≤ (eta/2)*δ := mul_le_mul schedule_speed hrad (abs_nonneg _) (div_nonneg eta_pos.le (by norm_num))
  calc
    _ ≤ min r r'*(∑ j : Fin (J+1),(|theta J r j-theta J r' j|+theta J r j*D j)) :=
      mul_le_mul_of_nonneg_left hsum (le_min hr hr')
    _ = min r r'*(∑ j : Fin (J+1),|theta J r j-theta J r' j|)+
        ∑ j : Fin (J+1),min r r'*(theta J r j*D j) := by
      simp only [Finset.sum_add_distrib,mul_add,Finset.mul_sum]
    _ ≤ (eta/2)*δ+∑ j : Fin (J+1),(eta/4)*theta J r j*δ :=
      add_le_add hschedule (Finset.sum_le_sum (fun j _ => theta_band_budget J j hr hr' dist_nonneg (hD j) (hD0 j)))
    _ = (eta/2)*δ+(eta/4)*(∑ j : Fin (J+1),theta J r j)*δ := by
      rw [← Finset.sum_mul,← Finset.mul_sum]
    _ ≤ (eta/2)*δ+(eta/4)*2*δ := add_le_add le_rfl (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (theta_sum_le J r) (show 0 ≤ eta/4 from div_nonneg eta_pos.le (by norm_num))) (show 0 ≤ δ from dist_nonneg))
    _ = eta*dist s t := by dsimp [δ]; ring

end
end C0Absorption

namespace C0Absorption
noncomputable section
open Set Filter Topology
open scoped NNReal BigOperators ZeroAtInfty

theorem product_difference_bound {a b u v : ℝ} (ha : 0≤a) (hv : |v|≤1) :
    |a*u-b*v| ≤ |a-b|+a*|u-v| := by
  calc
    _ = |(a-b)*v+a*(u-v)| := by congr 1; ring
    _ ≤ |(a-b)*v|+|a*(u-v)| := abs_add_le _ _
    _ = |a-b| *|v|+a*|u-v| := by rw [abs_mul,abs_mul,abs_of_nonneg ha]
    _ ≤ |a-b| *1+a*|u-v| := add_le_add (mul_le_mul_of_nonneg_left hv (abs_nonneg _)) le_rfl
    _ = _ := by rw [mul_one]

theorem theta_weighted_coordinate (J : ℕ) (j : Fin (J+1)) {r s : ℝ} (hr : 0≤r) (hs : 0 ≤ s) :
    min r s*|theta J r j-theta J s j| ≤ (Real.pi/scheduleH)*|r-s| := by
  apply le_trans _ (theta_weighted_distance J hr hs)
  apply mul_le_mul_of_nonneg_left _ (le_min hr hs)
  exact Finset.single_le_sum (fun (i : Fin (J+1)) _ => abs_nonneg (theta J r i-theta J s i)) (Finset.mem_univ j)

theorem blockVector_weighted_distance (lev : Level) (s t : C0Ball) (b : Block lev) :
    min (localRadius lev s.val) (localRadius lev t.val)*
      |blockVector lev s b-blockVector lev t b| ≤ eta*dist s t := by
  let J := levelJ lev
  let r := localRadius lev s.val
  let r' := localRadius lev t.val
  let δ := dist s t
  let D := |bandVector b.1 b.2 (prefixRestrict b.1 s)-bandVector b.1 b.2 (prefixRestrict b.1 t)|
  have hr : 0≤r := finiteRadius_nonneg _ _
  have hr' : 0≤r' := finiteRadius_nonneg _ _
  have hrad : |r-r'|≤δ := by
    change dist (finiteRadius (radiusCoordinates lev) s.val) (finiteRadius (radiusCoordinates lev) t.val) ≤ dist s.val t.val
    simpa only [NNReal.coe_one,one_mul] using (finiteRadius_lipschitz (radiusCoordinates lev)).dist_le_mul s.val t.val
  have hD : D≤bandL b.1*δ := by
    exact (bandVector_distance b.1 b.2 _ _).trans (mul_le_mul_of_nonneg_left
      (by simpa only [NNReal.coe_one,one_mul] using (prefixRestrict_lipschitz b.1).dist_le_mul s t) (bandL b.1).coe_nonneg)
  have hD0 (hj : b.1.val=0) : D=0 := by
    dsimp [D]
    have he : prefixRestrict b.1 s=prefixRestrict b.1 t := by rw [hj]; exact Subsingleton.elim _ _
    simp only [he,sub_self,abs_zero]
  have hschedule : min r r'*|theta J r b.1-theta J r' b.1| ≤ (eta/2)*δ := by
    calc
      _ ≤ (Real.pi/scheduleH)*|r-r'| := theta_weighted_coordinate J b.1 hr hr'
      _ ≤ (eta/2)*δ := mul_le_mul schedule_speed hrad (abs_nonneg _) (div_nonneg eta_pos.le (by norm_num))
  have hprod : |blockVector lev s b-blockVector lev t b| ≤
      |theta J r b.1-theta J r' b.1|+theta J r b.1*D :=
    product_difference_bound (theta_nonneg _ _ _) (by rw [abs_of_nonneg (bandVector_nonneg _ _ _)]; exact bandVector_le_one _ _ _)
  calc
    _ ≤ min r r'*(|theta J r b.1-theta J r' b.1|+theta J r b.1*D) :=
      mul_le_mul_of_nonneg_left hprod (le_min hr hr')
    _ = min r r'*|theta J r b.1-theta J r' b.1|+min r r'*(theta J r b.1*D) := mul_add _ _ _
    _ ≤ (eta/2)*δ+(eta/4)*theta J r b.1*δ :=
      add_le_add hschedule (theta_band_budget J b.1 hr hr' dist_nonneg hD hD0)
    _ ≤ (eta/2)*δ+(eta/4)*1*δ := add_le_add le_rfl
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (theta_le_one _ _ _)
        (show 0≤eta/4 from div_nonneg eta_pos.le (by norm_num))) dist_nonneg)
    _ ≤ eta*dist s t := by dsimp [δ]; nlinarith [eta_pos,mul_nonneg eta_pos.le (dist_nonneg (x := s) (y := t))]

end
end C0Absorption

end OAI


