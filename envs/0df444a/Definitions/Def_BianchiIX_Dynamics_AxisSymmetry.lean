-- Prove2me | Definitions.Def_BianchiIX_Dynamics_AxisSymmetry
-- name    : BianchiIX_Dynamics_AxisSymmetry
-- status  : Definition
-- author  : @trppppp
-- created : 2026-11-05T05:34:13.06246+00:00
-- url     : https://prove2.me/theorems/827cc7e4-dd92-4afb-b012-0e3361e9c358
-- title:
--   Normalized symmetries and transformed solutions
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
--   Write $N_1(x)=a$, $N_2(x)=b$, and $N_3(x)=c$. For initial data $(x_0,t_0)$,
--   let $I_{\max}(x_0,t_0)$ be the union of all open convex domains of solutions
--   with these initial data, and let $\alpha_{x_0,t_0}$ be their compatible curve.
--   A solution $S$ has such a domain $I_S$, a curve $\alpha_S$, and
--   $\alpha_S(t_0)=x_0$.
--
--   Let $\mathcal L(X,X)$ be the continuous linear operators on $X$ and set
--   $$A(x)=dF_x,\qquad \widetilde F(x,J)=(F(x),A(x)\circ J).$$
--
--   For a fixed initial time $t_0$, put
--   $$\mathcal D_{t_0}=\{(x,t):t\in I_{\max}(x,t_0)\},\qquad
--   \Phi_{t_0}(x,t)=\alpha_{x,t_0}(t),\qquad
--   J_{x,t_0}(t)=d_x\Phi_{t_0}(x,t).$$
--
--   Write $\lambda_x=d\mathcal C_x:X\to\mathbb R$ for the constraint differential.
--
--   For $x=(p,s,a,b,c)$, define
--   $$H(x)=(abc)^{2/3},\quad w(x)=abc(1+4H(x)),\quad
--   \delta(x)=2K-3S,\quad \bar\delta(x)=\frac{2(K+4H(x))}{1+4H(x)},$$
--   $$V(x,t_0,t)=\frac{w(x)\det J_{x,t_0}(t)}{w(\alpha_{x,t_0}(t))}.$$
--   Write $[L]$ for the matrix of a continuous linear operator $L:X\to X$
--   in the standard basis. Set $\Omega(v_0,\ldots,v_4)=\det(v_0,\ldots,v_4)$,
--   $$\omega_x(v_0,\ldots,v_3)=\frac{\Omega(x/2,v_0,\ldots,v_3)}{w(x)},\qquad
--   \varphi_x(v_0,v_1,v_2)=\omega_x(F(x),v_0,v_1,v_2).$$
--
--   A normalized symmetry is a continuous linear equivalence $L:X\to X$ satisfying
--   $$\mathcal C(Lx)=\mathcal C(x),\quad Lx\in W\ \Longleftrightarrow\ x\in W,
--   \quad F(Lx)=LF(x),\quad w(Lx)=w(x),\quad\det L=1.$$
--   These symmetries include the identity, composition, inverse, and the two maps
--   $$R(p,s,a,b,c)=((-p+\sqrt3s)/2,(-\sqrt3p-s)/2,b,c,a),\qquad
--   S_0(p,s,a,b,c)=(p,-s,a,c,b).$$
--   Transforming a solution replaces its curve $\alpha$ by $L\alpha$ and
--   keeps its time domain.
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Dynamics/AxisSymmetry.lean

import Definitions.Def_BianchiIX_Dynamics_Normalized
import Definitions.Def_BianchiIX_Algebra_Flux
import Definitions.Def_BianchiIX_Dynamics_AxisMaps
import Definitions.Def_BianchiIX_Dynamics_MaximalFlow
import Definitions.Def_BianchiIX_Dynamics_CorrectedVolume
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
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.Calculus.FDeriv.Partial
import Mathlib.Topology.Instances.Matrix
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Topology.Algebra.Module.Determinant
import Mathlib.Analysis.Calculus.Deriv.Pi
import Mathlib.Data.Real.Basic

section
noncomputable section
open BianchiIX

private theorem BianchiIX.axisCycle_constraint (x : NormalizedState) : stateConstraint (axisCycle x) = stateConstraint x := by
  have hs : (Real.sqrt 3) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  dsimp [stateConstraint, constraint, shearSq, curvature, axisCycle]
  ring_nf
  norm_num [hs]
  ring

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.axisSwap_constraint (x : NormalizedState) : stateConstraint (axisSwap x) = stateConstraint x := by
  dsimp [stateConstraint, constraint, shearSq, curvature, axisSwap]
  ring

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.axisCycle_positive (x : NormalizedState) : positiveWalls (axisCycle x) ↔ positiveWalls x := by
  dsimp [positiveWalls, axisCycle]
  tauto

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.axisSwap_positive (x : NormalizedState) : positiveWalls (axisSwap x) ↔ positiveWalls x := by
  dsimp [positiveWalls, axisSwap]
  tauto

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.axisCycle_field (x : NormalizedState) : normalizedField (axisCycle x) = axisCycle (normalizedField x) := by
  have hs : (Real.sqrt 3) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  ext i
  fin_cases i <;> dsimp [normalizedField, axisCycle, shearPlus, shearMinus,
    rateOne, rateTwo, rateThree, shearSq, curvature] <;> ring_nf <;> norm_num [hs] <;> ring

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.axisSwap_field (x : NormalizedState) : normalizedField (axisSwap x) = axisSwap (normalizedField x) := by
  ext i
  fin_cases i <;> dsimp [normalizedField, axisSwap, shearPlus, shearMinus,
    rateOne, rateTwo, rateThree, shearSq, curvature] <;> ring

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.axisCycle_wall_product (x : NormalizedState) :
    axisCycle x 2 * axisCycle x 3 * axisCycle x 4 = x 2 * x 3 * x 4 := by
  dsimp [axisCycle]
  ring

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.axisSwap_wall_product (x : NormalizedState) :
    axisSwap x 2 * axisSwap x 3 * axisSwap x 4 = x 2 * x 3 * x 4 := by
  dsimp [axisSwap]
  ring

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.axisCycle_det : axisCycleEquiv.toLinearMap.det = 1 := by
  have hs : (Real.sqrt 3) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  rw [← LinearMap.det_toMatrix']
  have hm : LinearMap.toMatrix' axisCycleEquiv.toLinearMap =
      !![-1 / 2, Real.sqrt 3 / 2, 0, 0, 0; -Real.sqrt 3 / 2, -1 / 2, 0, 0, 0;
        0, 0, 0, 1, 0; 0, 0, 0, 0, 1; 0, 0, 1, 0, 0] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [LinearMap.toMatrix'_apply, axisCycleEquiv, axisCycleLinear, axisCycle, Pi.single_apply, Fin.ext_iff]
  rw [hm]
  norm_num [Matrix.det_succ_row_zero, Fin.sum_univ_succ, Matrix.det_fin_two,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.vecHead, Matrix.vecTail, hs]
  change (1 : ℝ) / 4 + -(Real.sqrt 3 / 2 * (-Real.sqrt 3 / 2 * 1)) = 1
  nlinarith [hs]

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.axisSwap_det : axisSwapEquiv.toLinearMap.det = 1 := by
  rw [← LinearMap.det_toMatrix']
  have hm : LinearMap.toMatrix' axisSwapEquiv.toLinearMap =
      !![1, 0, 0, 0, 0; 0, -1, 0, 0, 0; 0, 0, 1, 0, 0; 0, 0, 0, 0, 1; 0, 0, 0, 1, 0] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [LinearMap.toMatrix'_apply, axisSwapEquiv, axisSwapLinear, axisSwap, Pi.single_apply, Fin.ext_iff]
  rw [hm]
  norm_num [Matrix.det_succ_row_zero, Fin.sum_univ_succ, Matrix.det_fin_two,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.vecHead, Matrix.vecTail]

end
end


noncomputable section

namespace BianchiIX

open Set

/-- Linear changes of physical axes with their verified dynamical and volume identities. -/
structure NormalizedSymmetry where
  map : NormalizedState ≃L[ℝ] NormalizedState
  constraint : ∀ x, stateConstraint (map x) = stateConstraint x
  positive : ∀ x, positiveWalls (map x) ↔ positiveWalls x
  field : ∀ x, normalizedField (map x) = map (normalizedField x)
  weight : ∀ x, normalizedVolumeWeight (map x) = normalizedVolumeWeight x
  det : map.toLinearMap.det = 1

namespace NormalizedSymmetry

def refl : NormalizedSymmetry where
  map := ContinuousLinearEquiv.refl ℝ NormalizedState
  constraint _ := rfl
  positive _ := Iff.rfl
  field _ := rfl
  weight _ := rfl
  det := LinearMap.det_id

def trans (A B : NormalizedSymmetry) : NormalizedSymmetry where
  map := A.map.trans B.map
  constraint x := (B.constraint (A.map x)).trans (A.constraint x)
  positive x := (B.positive (A.map x)).trans (A.positive x)
  field x := by
    change normalizedField (B.map (A.map x)) = B.map (A.map (normalizedField x))
    rw [B.field, A.field]
  weight x := (B.weight (A.map x)).trans (A.weight x)
  det := by
    change (B.map.toLinearMap.comp A.map.toLinearMap).det = 1
    rw [LinearMap.det_comp, B.det, A.det, one_mul]

def symm (A : NormalizedSymmetry) : NormalizedSymmetry where
  map := A.map.symm
  constraint x := by simpa using (A.constraint (A.map.symm x)).symm
  positive x := by simpa using (A.positive (A.map.symm x)).symm
  field x := by
    apply A.map.injective
    rw [← A.field]
    simp
  weight x := by simpa using (A.weight (A.map.symm x)).symm
  det := by
    have H : A.map.toLinearMap.comp A.map.symm.toLinearMap = LinearMap.id := by
      ext x
      simp
    have hd := congrArg LinearMap.det H
    rw [LinearMap.det_comp, A.det, one_mul, LinearMap.det_id] at hd
    exact hd

def cycle : NormalizedSymmetry where
  map := axisCycleEquiv
  constraint := axisCycle_constraint
  positive := axisCycle_positive
  field := axisCycle_field
  weight x := by
    change normalizedVolumeWeight (axisCycle x) = normalizedVolumeWeight x
    simp only [normalizedVolumeWeight, wallAmplitude, axisCycle_wall_product]
  det := axisCycle_det

def swap : NormalizedSymmetry where
  map := axisSwapEquiv
  constraint := axisSwap_constraint
  positive := axisSwap_positive
  field := axisSwap_field
  weight x := by
    change normalizedVolumeWeight (axisSwap x) = normalizedVolumeWeight x
    simp only [normalizedVolumeWeight, wallAmplitude, axisSwap_wall_product]
  det := axisSwap_det

end NormalizedSymmetry

def NormalizedSolution.transform {x : NormalizedState} {t₀ : ℝ}
    (S : NormalizedSolution x t₀) (A : NormalizedSymmetry) : NormalizedSolution (A.map x) t₀ where
  domain := S.domain
  isOpen_domain := S.isOpen_domain
  convex_domain := S.convex_domain
  initial_mem := S.initial_mem
  curve := fun t => A.map (S.curve t)
  initial_eq := by rw [S.initial_eq]
  hasDerivAt t ht := by
    have H := A.map.hasFDerivAt.comp_hasDerivAt t (S.hasDerivAt t ht)
    rw [A.field]
    convert! H using 1

namespace NormalizedSymmetry













end NormalizedSymmetry

end BianchiIX


