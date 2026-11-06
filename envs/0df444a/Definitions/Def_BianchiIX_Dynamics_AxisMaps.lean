-- Prove2me | Definitions.Def_BianchiIX_Dynamics_AxisMaps
-- name    : BianchiIX_Dynamics_AxisMaps
-- status  : Definition
-- author  : @trppppp
-- created : 2026-11-05T05:28:50.939282+00:00
-- url     : https://prove2.me/theorems/3192cb8c-ebac-4691-957f-5714a40ddce2
-- title:
--   Cyclic and transposition maps of the physical axes
-- statement:
--   For real variables $p,s,a,b,c$, set
--   $$K=a^2+b^2+c^2-2(ab+bc+ca),\qquad S=p^2+s^2,\qquad C=S+K.$$
--   The shear components and wall rates are
--   $$P=Kp-2a^2+b^2+c^2+ab-2bc+ac,$$
--   $$Q=Ks+\sqrt{3}(-b^2+c^2+ab-ac),$$
--   $$r_1=-S+2p,\qquad r_2=-S-p+\sqrt{3}s,\qquad r_3=-S-p-\sqrt{3}s.$$
--   These functions define the normalized vacuum Bianchi IX vector field
--   $(P,Q,r_1a,r_2b,r_3c)$.
--
--   Let $X=\mathbb R^5$ with coordinates $x=(p,s,a,b,c)$ and the sup norm. Write
--   $$F(x)=(P,Q,r_1a,r_2b,r_3c),\qquad \mathcal C(x)=C(p,s,a,b,c),$$
--   and let $W=\{(p,s,a,b,c)\in X:a>0,\ b>0,\ c>0\}$.
--
--   Define the linear maps
--   $$R(p,s,a,b,c)=((-p+\sqrt3s)/2,(-\sqrt3p-s)/2,b,c,a),$$
--   $$S_0(p,s,a,b,c)=(p,-s,a,c,b).$$
--   Their linear-map and continuous-linear-equivalence realizations use
--   $R^{-1}=R^2$ and $S_0^{-1}=S_0$.
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Dynamics/AxisMaps.lean

import Definitions.Def_BianchiIX_Dynamics_Normalized
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FunProp
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Determinant

noncomputable section

namespace BianchiIX

/-- New axes `(1,2,3)` are old axes `(2,3,1)`. -/
def axisCycle (x : NormalizedState) : NormalizedState :=
  ![(-x 0 + Real.sqrt 3 * x 1) / 2, (-Real.sqrt 3 * x 0 - x 1) / 2, x 3, x 4, x 2]

/-- Exchange the second and third axes, including their shear components. -/
def axisSwap (x : NormalizedState) : NormalizedState := ![x 0, -x 1, x 2, x 4, x 3]

theorem axisCycle_twice (x : NormalizedState) :
    axisCycle (axisCycle x) =
      ![(-x 0 - Real.sqrt 3 * x 1) / 2, (Real.sqrt 3 * x 0 - x 1) / 2, x 4, x 2, x 3] := by
  have hs : (Real.sqrt 3) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  ext i
  fin_cases i <;> dsimp [axisCycle] <;> ring_nf <;> norm_num [hs] <;> ring

theorem axisCycle_three (x : NormalizedState) : axisCycle (axisCycle (axisCycle x)) = x := by
  have hs : (Real.sqrt 3) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  rw [axisCycle_twice]
  ext i
  fin_cases i <;> dsimp [axisCycle] <;> ring_nf <;> norm_num [hs] <;> ring

@[simp] theorem axisSwap_twice (x : NormalizedState) : axisSwap (axisSwap x) = x := by
  ext i
  fin_cases i <;> simp [axisSwap]

def axisCycleLinear : NormalizedState →ₗ[ℝ] NormalizedState where
  toFun := axisCycle
  map_add' x y := by
    ext i
    fin_cases i <;> simp [axisCycle] <;> ring
  map_smul' r x := by
    ext i
    fin_cases i <;> simp [axisCycle] <;> ring

def axisSwapLinear : NormalizedState →ₗ[ℝ] NormalizedState where
  toFun := axisSwap
  map_add' x y := by
    ext i
    fin_cases i <;> simp [axisSwap]
    ring
  map_smul' r x := by
    ext i
    fin_cases i <;> simp [axisSwap]

def axisCycleEquiv : NormalizedState ≃L[ℝ] NormalizedState :=
  ({ axisCycleLinear with
    invFun := fun x => axisCycle (axisCycle x)
    left_inv := axisCycle_three
    right_inv := axisCycle_three } : NormalizedState ≃ₗ[ℝ] NormalizedState).toContinuousLinearEquiv

def axisSwapEquiv : NormalizedState ≃L[ℝ] NormalizedState :=
  ({ axisSwapLinear with
    invFun := axisSwap
    left_inv := axisSwap_twice
    right_inv := axisSwap_twice } : NormalizedState ≃ₗ[ℝ] NormalizedState).toContinuousLinearEquiv
























end BianchiIX


