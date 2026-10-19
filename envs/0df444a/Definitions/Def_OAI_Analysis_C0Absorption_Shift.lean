-- Prove2me | Definitions.Def_OAI_Analysis_C0Absorption_Shift
-- name    : OAI_Analysis_C0Absorption_Shift
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T21:36:57.997103+00:00
-- url     : https://prove2.me/theorems/abab76bd-e1f3-4bed-8120-b6f2a399cfb5
-- title:
--   Frozen shifts and their explicit inverses
-- statement:
--   These notions belong to the construction of a separable Banach space $Z$ that contains no linear copy of $c_0$, yet $Z\times c_0$ is bi-Lipschitz equivalent to $Z$ and $Z$ is Lipschitz-universal for separable metric spaces. $Z$ is a completion of the space of molecules on the unit ball of $c_0$ (finitely supported functions with total sum zero), normed by test functions from carefully chosen Lipschitz classes. Levels are pairs $(i,n)$, labels are (level, band, grid tag), and the coordinates of $c_0$ are split into row coordinates indexed by $\mathbb N$ and label coordinates indexed by labels. Let $W$ be frozen weights, with rows $w$ and vectors $v$ satisfying $\sum_bw_bv_b=1$ at each level.
--
--   1. **Frozen shift.** $\mathrm{shift}_W(x)_\gamma=x_{\mathrm{label}(\gamma)}+\mathrm{corr}_W(\gamma)(x)$, a bounded operator $c_0\to C_0(\mathrm{Labels})$ with norm at most $5$.
--   2. **Output scalars.** For $y\in C_0(\mathrm{Labels})$, $\mathrm{out}_{\mathrm{lev}}(y)=\sum_bw_by_{(\mathrm{lev},b)}$. These tend to zero along levels.
--   3. **Inverse.** The inverse candidate has rows $\mathrm{out}_{(i,0)}(y)$ and blocks
--   $$
--   y_\gamma-v_\gamma\bigl(\mathrm{out}_{\mathrm{lev}}(y)-\mathrm{out}_{\mathrm{succ}(\mathrm{lev})}(y)\bigr).
--   $$
--   The identity $\sum_aw_a(y_a-v_ab)=\sum_aw_ay_a-b$ makes the row scalars telescope along each chain of levels.
--   4. **Recomputed shift.** $\mathrm{recomputedShift}(x)=\mathrm{shift}_{W(x/\|x\|)}(x)$ uses the state weights of the normalized point. It is positively homogeneous and vanishes at $0$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/C0Absorption/Shift.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/C0Absorption/Shift.lean by skeleton subtraction
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
import Definitions.Def_OAI_Analysis_C0Absorption_Frozen
import Definitions.Def_OAI_Analysis_C0Absorption_Tags
import Definitions.Def_OAI_Analysis_C0Absorption_Operators

namespace OAI

open Set Filter Topology
open scoped NNReal BigOperators ZeroAtInfty
open NormedSpace

namespace C0Absorption
noncomputable section
open Set Filter Topology
open scoped NNReal BigOperators ZeroAtInfty

def frozenShift (W : FrozenWeights) : C0 →L[ℝ] BlockC0 := inputBlocks+frozenCorrectionL W

@[simp] theorem frozenShift_apply (W : FrozenWeights) (x : C0) (γ : Label) :
    frozenShift W x γ=x (labelIndex γ)+frozenCorrection W γ x := rfl

theorem frozenShift_bound (W : FrozenWeights) (x : C0) : ‖frozenShift W x‖≤5*‖x‖ := by
  apply cfun_norm_le _ (mul_nonneg (by norm_num) (norm_nonneg x))
  intro γ
  rw [frozenShift_apply]
  exact (abs_add_le _ _).trans (by linarith [c0_norm_apply_le x (labelIndex γ),frozenCorrection_bound W γ x])

def blockInclusion : BlockC0 →L[ℝ] C0 :=
  inputCoordinates.toContinuousLinearEquiv.toContinuousLinearMap.comp (ContinuousLinearMap.inr ℝ C0 BlockC0)

@[simp] theorem blockInclusion_apply (y : BlockC0) (γ : Label) : blockInclusion y (labelIndex γ)=y γ :=
  joinInputs_block (0,y) γ

def outputScalar (W : FrozenWeights) (lev : Level) : BlockC0 →L[ℝ] ℝ :=
  (rowScalar W lev).comp blockInclusion

@[simp] theorem outputScalar_apply (W : FrozenWeights) (lev : Level) (y : BlockC0) :
    outputScalar W lev y=∑ b : Block lev,W.row lev b*y (blockLabel lev b) := by
  simp only [outputScalar,ContinuousLinearMap.comp_apply,rowScalar_apply,blockInput,blockInclusion_apply]

theorem outputScalar_tendsto (W : FrozenWeights) (y : BlockC0) :
    Tendsto (fun lev => outputScalar W lev y) cofinite (nhds 0) := by
  apply squeeze_zero_norm (fun lev => rowScalar_local W lev (blockInclusion y)) _
  simpa only [mul_zero] using (localRadius_tendsto (blockInclusion y)).const_mul 2

def firstLevel (i : ℕ) : Level := (i,0)

theorem firstLevel_injective : Function.Injective firstLevel := fun _ _ h => congrArg Prod.fst h

theorem levelSuccessor_injective : Function.Injective levelSuccessor := by
  rintro ⟨i,n⟩ ⟨j,m⟩ h
  simp only [levelSuccessor,Prod.mk.injEq,Nat.add_right_cancel_iff] at h
  exact Prod.ext h.1 h.2

def inverseRows (W : FrozenWeights) (y : BlockC0) : C0 :=
  cfunOfTendsto (fun i => outputScalar W (i,0) y)
    ((outputScalar_tendsto W y).comp firstLevel_injective.tendsto_cofinite)

def inverseBlockFunction (W : FrozenWeights) (y : BlockC0) (γ : Label) : ℝ :=
  y γ-W.vector γ.level ⟨γ.band,γ.tag⟩*(outputScalar W γ.level y-outputScalar W (levelSuccessor γ.level) y)

theorem inverseBlockFunction_tendsto (W : FrozenWeights) (y : BlockC0) :
    Tendsto (inverseBlockFunction W y) cofinite (nhds 0) := by
  have hb : Tendsto (fun γ : Label => outputScalar W γ.level y-outputScalar W (levelSuccessor γ.level) y)
      cofinite (nhds 0) := by
    simpa only [sub_zero,Function.comp_def] using ((outputScalar_tendsto W y).comp labelLevel_tendsto).sub
      ((outputScalar_tendsto W y).comp (levelSuccessor_injective.tendsto_cofinite.comp labelLevel_tendsto))
  have hm : Tendsto (fun γ : Label => W.vector γ.level ⟨γ.band,γ.tag⟩*
      (outputScalar W γ.level y-outputScalar W (levelSuccessor γ.level) y)) cofinite (nhds 0) := by
    have hbound (γ : Label) : ‖W.vector γ.level ⟨γ.band,γ.tag⟩*
        (outputScalar W γ.level y-outputScalar W (levelSuccessor γ.level) y)‖≤
        |outputScalar W γ.level y-outputScalar W (levelSuccessor γ.level) y| := by
      simpa only [Real.norm_eq_abs,abs_mul,one_mul] using
        mul_le_mul_of_nonneg_right (W.vector_bound γ.level ⟨γ.band,γ.tag⟩)
          (abs_nonneg (outputScalar W γ.level y-outputScalar W (levelSuccessor γ.level) y))
    exact squeeze_zero_norm hbound (by simpa only [abs_zero] using hb.abs)
  change Tendsto (fun γ : Label => y γ-W.vector γ.level ⟨γ.band,γ.tag⟩*
    (outputScalar W γ.level y-outputScalar W (levelSuccessor γ.level) y)) cofinite (nhds 0)
  simpa only [sub_zero] using (cfun_tendsto y).sub hm

def inverseBlocks (W : FrozenWeights) (y : BlockC0) : BlockC0 :=
  cfunOfTendsto (inverseBlockFunction W y) (inverseBlockFunction_tendsto W y)

def frozenInverse (W : FrozenWeights) (y : BlockC0) : C0 := joinInputs (inverseRows W y,inverseBlocks W y)

@[simp] theorem frozenInverse_row (W : FrozenWeights) (y : BlockC0) (i : ℕ) :
    frozenInverse W y (rowIndex i)=outputScalar W (i,0) y := joinInputs_row _ i

@[simp] theorem frozenInverse_block (W : FrozenWeights) (y : BlockC0) (γ : Label) :
    frozenInverse W y (labelIndex γ)=inverseBlockFunction W y γ := joinInputs_block _ γ

theorem finite_row_cancel {A : Type*} [Fintype A] (w v y : A → ℝ) (h : (∑ a,w a*v a)=1) (b : ℝ) :
    (∑ a,w a*(y a-v a*b))=(∑ a,w a*y a)-b := by
  simp only [mul_sub,← mul_assoc,Finset.sum_sub_distrib,← Finset.sum_mul,h,one_mul]

theorem finite_row_shift {A : Type*} [Fintype A] (w v x : A → ℝ) (h : (∑ a,w a*v a)=1) (b : ℝ) :
    (∑ a,w a*(x a+v a*b))=(∑ a,w a*x a)+b := by
  simp only [mul_add,← mul_assoc,Finset.sum_add_distrib,← Finset.sum_mul,h,one_mul]

end
end C0Absorption

namespace C0Absorption
noncomputable section
open Set Filter Topology NormedSpace
open scoped NNReal BigOperators ZeroAtInfty

def recomputedShift (x : C0) : BlockC0 := frozenShift (stateWeights (normalizedBall x)) x

@[simp] theorem recomputedShift_zero : recomputedShift 0=0 := map_zero _

end
end C0Absorption

end OAI


