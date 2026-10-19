-- Prove2me | Definitions.Def_OAI_Analysis_C0Absorption_Frozen
-- name    : OAI_Analysis_C0Absorption_Frozen
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T21:27:42.518906+00:00
-- url     : https://prove2.me/theorems/2188f1e7-e4ad-451b-9bd3-bd4d014afbbb
-- title:
--   Frozen weights, corrections and their Lipschitz control
-- statement:
--   These notions belong to the construction of a separable Banach space $Z$ that contains no linear copy of $c_0$, yet $Z\times c_0$ is bi-Lipschitz equivalent to $Z$ and $Z$ is Lipschitz-universal for separable metric spaces. $Z$ is a completion of the space of molecules on the unit ball of $c_0$ (finitely supported functions with total sum zero), normed by test functions from carefully chosen Lipschitz classes. Levels are pairs $(i,n)$ with $J(i,n)=i+n+2$ bands. A label is a level together with a band $j\le J$ and a grid tag in the band grid of $[-1,1]^j$. The coordinates of $c_0$ are re-indexed by $\mathbb N\sqcup\mathrm{Labels}$ (row coordinates and label coordinates).
--
--   1. **Frozen weights.** For each level, a frozen weight system consists of vectors $v_b\in[-1,1]$ and rows $w_b$ with $\sum_b|w_b|\le2$ and $\sum_bw_bv_b=1$. The state weights of a point $s$ of the unit ball are its block vectors and rows.
--   2. **Scalars.** $\mathrm{rowScalar}_{\mathrm{lev}}(x)=\sum_bw_b\,x_{\mathrm{label}(b)}$. The previous scalar is the row coordinate $x_{\mathrm{row}(i)}$ at $n=0$, and the row scalar of level $(i,n-1)$ otherwise.
--   3. **Frozen correction.** For a label $\gamma$ at level $\mathrm{lev}$ with block $b$,
--   $$
--   \mathrm{corr}_W(\gamma)(x)=v_b\bigl(\mathrm{previousScalar}(x)-\mathrm{rowScalar}(x)\bigr),
--   $$
--   bounded by $4\,\mathrm{localRadius}_{\mathrm{lev}}(x)$ and $4$-Lipschitz. The correction of a point $s$ uses its own state weights.
--   4. **Weight errors.** If two weight systems differ by at most $q$ after multiplication by local radii, their corrections differ by at most $6q$. Mixing the weights of $s$ and $t$ level by level, by taking the point of larger local radius, shows that each correction is $(4+12\eta)$-Lipschitz on the ball. It is supported where the prefix is near the tag and the local radius is at least $\ell_j$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/C0Absorption/Frozen.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/C0Absorption/Frozen.lean by skeleton subtraction
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
import Definitions.Def_OAI_Analysis_C0Absorption_Correction

namespace OAI

open Set Filter Topology
open scoped NNReal BigOperators ZeroAtInfty
open NormedSpace

namespace C0Absorption
noncomputable section
open Set Filter Topology
open scoped NNReal BigOperators ZeroAtInfty

structure FrozenWeights where
  vector : (lev : Level) → Block lev → ℝ
  row : (lev : Level) → Block lev → ℝ
  vector_bound : ∀ lev b, |vector lev b|≤1
  row_bound : ∀ lev, (∑ b : Block lev,|row lev b|)≤2
  pairing : ∀ lev, (∑ b : Block lev,row lev b*vector lev b)=1

def stateWeights (s : C0Ball) : FrozenWeights where
  vector := fun lev => blockVector lev s
  row := fun lev => blockRow lev s
  vector_bound := fun lev b => by rw [abs_of_nonneg (blockVector_nonneg _ _ _)]; exact blockVector_le_one _ _ _
  row_bound := fun lev => by simp only [abs_of_nonneg (blockRow_nonneg _ _ _)]; exact blockRow_sum lev s
  pairing := fun lev => blockRow_vector lev s

def blockInput (lev : Level) (x : C0) (b : Block lev) : ℝ := x (labelIndex (blockLabel lev b))

def rowScalar (W : FrozenWeights) (lev : Level) : C0 →L[ℝ] ℝ :=
  ∑ b : Block lev, (W.row lev b) • c0Eval (labelIndex (blockLabel lev b))

@[simp] theorem rowScalar_apply (W : FrozenWeights) (lev : Level) (x : C0) :
    rowScalar W lev x=∑ b : Block lev,W.row lev b*blockInput lev x b := by
  simp only [rowScalar,sum_apply,smul_apply,smul_eq_mul,c0Eval_apply,blockInput]

def previousScalar (W : FrozenWeights) (lev : Level) : C0 →L[ℝ] ℝ :=
  match lev.2 with
  | 0 => c0Eval (rowIndex lev.1)
  | n+1 => rowScalar W (lev.1,n)

def frozenCorrection (W : FrozenWeights) (γ : Label) : C0 →L[ℝ] ℝ :=
  W.vector γ.level ⟨γ.band,γ.tag⟩ • (previousScalar W γ.level-rowScalar W γ.level)

@[simp] theorem frozenCorrection_apply (W : FrozenWeights) (γ : Label) (x : C0) :
    frozenCorrection W γ x=W.vector γ.level ⟨γ.band,γ.tag⟩*(previousScalar W γ.level x-rowScalar W γ.level x) := rfl

def correction (γ : Label) (s : C0Ball) : ℝ := frozenCorrection (stateWeights s) γ s.val

theorem blockInput_abs_le (lev : Level) (x : C0) (b : Block lev) :
    |blockInput lev x b|≤finiteRadius (blockCoordinates lev) x := by
  apply coordinate_le_finiteRadius
  exact mem_blockCoordinates.mpr ⟨blockLabel lev b,rfl,rfl⟩

theorem finiteRadius_mono {I J : Finset ℕ} (h : I⊆J) (x : C0) : finiteRadius I x≤finiteRadius J x := by
  apply c0_norm_le _ (finiteRadius_nonneg _ _)
  intro k
  rw [finiteProjection_apply]
  split_ifs with hk
  · exact coordinate_le_finiteRadius x (h hk)
  · simpa using finiteRadius_nonneg J x

theorem blockInput_le_radius (lev : Level) (x : C0) (b : Block lev) :
    |blockInput lev x b|≤localRadius lev x :=
  (blockInput_abs_le lev x b).trans (finiteRadius_mono Finset.subset_union_right x)

theorem abs_finite_dot_le {A : Type*} [Fintype A] (u v : A → ℝ) {R : ℝ} (hv : ∀ a, |v a|≤R) :
    |∑ a,u a*v a| ≤ (∑ a,|u a|)*R := by
  calc
    _ ≤ ∑ a,|u a*v a| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ a,|u a| *R := by
      apply Finset.sum_le_sum
      intro a _
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hv a) (abs_nonneg _)
    _ = _ := (Finset.sum_mul _ _ _).symm

theorem rowScalar_bound (W : FrozenWeights) (lev : Level) (x : C0) {R : ℝ}
    (hR : 0≤R) (hv : ∀ b,|blockInput lev x b|≤R) : |rowScalar W lev x|≤2*R := by
  rw [rowScalar_apply]
  exact (abs_finite_dot_le _ _ hv).trans (mul_le_mul_of_nonneg_right (W.row_bound lev) hR)

theorem rowScalar_local (W : FrozenWeights) (lev : Level) (x : C0) :
    |rowScalar W lev x|≤2*localRadius lev x :=
  rowScalar_bound W lev x (finiteRadius_nonneg _ _) (blockInput_le_radius lev x)

theorem previousScalar_local (W : FrozenWeights) (lev : Level) (x : C0) :
    |previousScalar W lev x|≤2*localRadius lev x := by
  rcases lev with ⟨i,n⟩
  cases n with
  | zero =>
    change |x (rowIndex i)|≤2*localRadius (i,0) x
    have hle : |x (rowIndex i)|≤localRadius (i,0) x := by
      apply coordinate_le_finiteRadius
      exact Finset.mem_union_left _ (Finset.mem_singleton_self _)
    have hz : 0≤localRadius (i,0) x := finiteRadius_nonneg _ _
    linarith
  | succ n =>
    apply rowScalar_bound W (i,n) x (finiteRadius_nonneg _ _)
    intro b
    exact (blockInput_abs_le _ _ b).trans (finiteRadius_mono Finset.subset_union_left x)

theorem scalar_difference_bound (W : FrozenWeights) (lev : Level) (x : C0) :
    |previousScalar W lev x-rowScalar W lev x|≤4*localRadius lev x := by
  exact (abs_sub _ _).trans (by linarith [previousScalar_local W lev x,rowScalar_local W lev x])

theorem frozenCorrection_local (W : FrozenWeights) (γ : Label) (x : C0) :
    |frozenCorrection W γ x|≤4*localRadius γ.level x := by
  rw [frozenCorrection_apply,abs_mul]
  calc
    _ ≤ 1*(4*localRadius γ.level x) := mul_le_mul (W.vector_bound _ _) (scalar_difference_bound W _ x) (abs_nonneg _) zero_le_one
    _ = _ := one_mul _

theorem frozenCorrection_bound (W : FrozenWeights) (γ : Label) (x : C0) :
    |frozenCorrection W γ x|≤4*‖x‖ :=
  (frozenCorrection_local W γ x).trans (mul_le_mul_of_nonneg_left (finiteRadius_le _ _) (by norm_num))

theorem frozenCorrection_distance (W : FrozenWeights) (γ : Label) (x y : C0) :
    |frozenCorrection W γ x-frozenCorrection W γ y|≤4*dist x y := by
  rw [← map_sub,dist_eq_norm]
  exact frozenCorrection_bound W γ (x-y)

theorem rowScalar_weight_error (W V : FrozenWeights) (lev : Level) (x : C0) {q : ℝ}
    (h : localRadius lev x*(∑ b : Block lev,|W.row lev b-V.row lev b|)≤q) :
    |rowScalar W lev x-rowScalar V lev x|≤q := by
  rw [rowScalar_apply,rowScalar_apply,← Finset.sum_sub_distrib]
  simp only [← sub_mul]
  exact (abs_finite_dot_le _ _ (blockInput_le_radius lev x)).trans (by simpa only [mul_comm] using h)

structure WeightError (W V : FrozenWeights) (x : C0) (q : ℝ) : Prop where
  vector : ∀ lev b, localRadius lev x*|W.vector lev b-V.vector lev b|≤q
  row : ∀ lev, localRadius lev x*(∑ b : Block lev,|W.row lev b-V.row lev b|)≤q

theorem previousScalar_weight_error {W V : FrozenWeights} {x : C0} {q : ℝ}
    (hq : 0≤q) (h : WeightError W V x q) (lev : Level) :
    |previousScalar W lev x-previousScalar V lev x|≤q := by
  rcases lev with ⟨i,n⟩
  cases n with
  | zero => simpa only [previousScalar,sub_self,abs_zero] using hq
  | succ n => exact rowScalar_weight_error W V (i,n) x (h.row (i,n))

theorem correction_weight_error {W V : FrozenWeights} {x : C0} {q : ℝ}
    (hq : 0≤q) (h : WeightError W V x q) (γ : Label) :
    |frozenCorrection W γ x-frozenCorrection V γ x|≤6*q := by
  let b : Block γ.level := ⟨γ.band,γ.tag⟩
  let a := previousScalar W γ.level x-rowScalar W γ.level x
  let a' := previousScalar V γ.level x-rowScalar V γ.level x
  have hb : |a|≤4*localRadius γ.level x := scalar_difference_bound W γ.level x
  have hs : |a-a'|≤2*q := by
    calc
      _ = |(previousScalar W γ.level x-previousScalar V γ.level x)-
          (rowScalar W γ.level x-rowScalar V γ.level x)| := by dsimp [a,a']; congr 1; ring
      _ ≤ |previousScalar W γ.level x-previousScalar V γ.level x|+
          |rowScalar W γ.level x-rowScalar V γ.level x| := abs_sub _ _
      _ ≤ q+q := add_le_add (previousScalar_weight_error hq h _) (rowScalar_weight_error W V _ x (h.row _))
      _ = 2*q := by ring
  calc
    _ = |(W.vector γ.level b-V.vector γ.level b)*a+V.vector γ.level b*(a-a')| := by
      simp only [frozenCorrection_apply]; dsimp only [a,a',b]; congr 1; ring
    _ ≤ |W.vector γ.level b-V.vector γ.level b| *|a|+|V.vector γ.level b| *|a-a'| := by
      simpa only [abs_mul] using abs_add_le ((W.vector γ.level b-V.vector γ.level b)*a) (V.vector γ.level b*(a-a'))
    _ ≤ |W.vector γ.level b-V.vector γ.level b| *(4*localRadius γ.level x)+1*(2*q) :=
      add_le_add (mul_le_mul_of_nonneg_left hb (abs_nonneg _))
        (mul_le_mul (V.vector_bound _ _) hs (abs_nonneg _) zero_le_one)
    _ ≤ 4*q+2*q := by nlinarith [h.vector γ.level b]
    _ = 6*q := by ring

end
end C0Absorption

namespace C0Absorption
noncomputable section
open Set Filter Topology
open scoped NNReal BigOperators ZeroAtInfty

def mixedState (s t : C0Ball) (lev : Level) : C0Ball :=
  if localRadius lev t.val≤localRadius lev s.val then s else t

def mixedWeights (s t : C0Ball) : FrozenWeights where
  vector := fun lev => blockVector lev (mixedState s t lev)
  row := fun lev => blockRow lev (mixedState s t lev)
  vector_bound := fun lev b => (stateWeights (mixedState s t lev)).vector_bound lev b
  row_bound := fun lev => (stateWeights (mixedState s t lev)).row_bound lev
  pairing := fun lev => (stateWeights (mixedState s t lev)).pairing lev

theorem mixed_left_error (s t : C0Ball) :
    WeightError (stateWeights s) (mixedWeights s t) s.val (eta*dist s t) := by
  have hq : 0≤eta*dist s t := mul_nonneg eta_pos.le dist_nonneg
  constructor
  · intro lev b
    change localRadius lev s.val*|blockVector lev s b-blockVector lev (mixedState s t lev) b|≤_
    by_cases h : localRadius lev t.val≤localRadius lev s.val
    · simpa only [mixedState,h,↓reduceIte,sub_self,abs_zero,mul_zero] using hq
    · have hh := blockVector_weighted_distance lev s t b
      simpa only [mixedState,h,↓reduceIte,min_eq_left (le_of_not_ge h)] using hh
  · intro lev
    change localRadius lev s.val*(∑ b : Block lev,|blockRow lev s b-blockRow lev (mixedState s t lev) b|)≤_
    by_cases h : localRadius lev t.val≤localRadius lev s.val
    · simpa only [mixedState,h,↓reduceIte,sub_self,abs_zero,Finset.sum_const_zero,mul_zero] using hq
    · have hh := blockRow_weighted_distance lev s t
      simpa only [mixedState,h,↓reduceIte,min_eq_left (le_of_not_ge h)] using hh

theorem mixed_right_error (s t : C0Ball) :
    WeightError (stateWeights t) (mixedWeights s t) t.val (eta*dist s t) := by
  have hq : 0≤eta*dist s t := mul_nonneg eta_pos.le dist_nonneg
  constructor
  · intro lev b
    change localRadius lev t.val*|blockVector lev t b-blockVector lev (mixedState s t lev) b|≤_
    by_cases h : localRadius lev t.val≤localRadius lev s.val
    · have hh := blockVector_weighted_distance lev t s b
      simpa only [mixedState,h,↓reduceIte,min_eq_left h,dist_comm t s] using hh
    · simpa only [mixedState,h,↓reduceIte,sub_self,abs_zero,mul_zero] using hq
  · intro lev
    change localRadius lev t.val*(∑ b : Block lev,|blockRow lev t b-blockRow lev (mixedState s t lev) b|)≤_
    by_cases h : localRadius lev t.val≤localRadius lev s.val
    · have hh := blockRow_weighted_distance lev t s
      simpa only [mixedState,h,↓reduceIte,min_eq_left h,dist_comm t s] using hh
    · simpa only [mixedState,h,↓reduceIte,sub_self,abs_zero,Finset.sum_const_zero,mul_zero] using hq

theorem abs_sub_three (a b c d : ℝ) : |a-b|≤|a-c|+|c-d|+|d-b| :=
  (abs_sub_le a c b).trans (by linarith [abs_sub_le c d b])

def correctionL : ℝ≥0 := 4+12/1000

theorem correctionL_coe : (correctionL : ℝ)=4+12*eta := by norm_num [correctionL,eta]

theorem correction_lipschitz (γ : Label) : LipschitzWith correctionL (correction γ) := by
  apply LipschitzWith.of_dist_le_mul
  intro s t
  rw [Real.dist_eq,correctionL_coe]
  let W := mixedWeights s t
  let q := eta*dist s t
  have hq : 0≤q := mul_nonneg eta_pos.le dist_nonneg
  have h1 : |correction γ s-frozenCorrection W γ s.val|≤6*q := correction_weight_error hq (mixed_left_error s t) γ
  have h2 : |frozenCorrection W γ t.val-correction γ t|≤6*q := by
    rw [abs_sub_comm]
    exact correction_weight_error hq (mixed_right_error s t) γ
  have h3 : |frozenCorrection W γ s.val-frozenCorrection W γ t.val|≤4*dist s t := frozenCorrection_distance W γ s.val t.val
  have h := abs_sub_three (correction γ s) (correction γ t) (frozenCorrection W γ s.val) (frozenCorrection W γ t.val)
  dsimp only [q] at h1 h2
  nlinarith

theorem correction_bound (γ : Label) (s : C0Ball) : |correction γ s|≤4 := by
  have hs : ‖s.val‖≤1 := by simpa only [Metric.mem_closedBall,dist_zero_right] using s.property
  exact (frozenCorrection_bound (stateWeights s) γ s.val).trans (by linarith)

theorem correction_band_support {γ : Label} {s : C0Ball} (h : correction γ s≠0) :
    dist (prefixRestrict γ.band s) (bandPoint γ.band γ.tag) ≤ 2*dyadic γ.band := by
  have hv : bandVector γ.band γ.tag (prefixRestrict γ.band s)≠0 := by
    intro hv
    apply h
    simp only [correction,frozenCorrection_apply,stateWeights,blockVector,hv,mul_zero,zero_mul]
  exact (bandVector_support hv).le

theorem correction_radius_support {γ : Label} {s : C0Ball} (h : correction γ s≠0)
    (hj : γ.band.val<levelJ γ.level) : ell γ.band≤localRadius γ.level s.val := by
  have ht : theta (levelJ γ.level) (localRadius γ.level s.val) γ.band≠0 := by
    intro ht
    apply h
    simp only [correction,frozenCorrection_apply,stateWeights,blockVector,ht,zero_mul]
  exact theta_lower_support hj (finiteRadius_nonneg _ _) ht

end
end C0Absorption

end OAI


