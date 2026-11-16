-- Prove2me | Definitions.Def_HamSimTradeoff_AncillaDepth_Supplement_Jacobi
-- name    : HamSimTradeoff_AncillaDepth_Supplement_Jacobi
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T17:49:43.298639+00:00
-- url     : https://prove2.me/theorems/41e91c94-1605-426a-bc7c-01d9ba78ba6a
-- title:
--   Periodic Jacobi families and general query estimation
-- statement:
--   Jacobi data consist of real $a_j$ and strictly positive real $b_j$. The matrices $A_\theta$ are the sums in (8.3), with cyclic edges added even when the dimension is one or two. The bit family uses the same coefficients and a sign $(-1)^{x_j}$ on edge $j$, as in (8.5). The discriminant convention is
--   $$\det(zI-A_\theta)=2\prod_jb_j\,(\Delta(z)-\cos\theta).$$
--   The normalized trace is $d^{-1}\operatorname{Re}\operatorname{Tr}[f(A)]$, using the real continuous functional calculus. The endpoints have operator norm at most one whenever JacobiBounded is assumed. Query estimation uses the published QueryAlg XOR oracle layer: on each input, a real output estimate is within tolerance with probability at least $2/3$. QueryLowerBound quantifies over all finite workspaces, algorithms and output maps. It does not assume the lower bound it will be used to state.
-- source:
--   Yuxin Zhang, Changpeng Shao, STOC 2027 submission #334 (October 2026), p. 37, Eqs. (8.3)–(8.7), Definition 8.7

import Definitions.Def_HamSimTradeoff_AncillaDepth_Supplement_Approximation
import Definitions.Def_HamSimTradeoff_AncillaDepth_Architecture
import Definitions.Def_QAlgorithms_Defs_Query
open scoped BigOperators Matrix.Norms.L2Operator

namespace HamSimTradeoff.AncillaDepth.Supplement
noncomputable section

structure JacobiData (d : ℕ) where
  diagonal : Fin d → ℝ
  edge : Fin d → ℝ
  edge_pos : ∀ j, 0 < edge j

def matrixUnit {d : ℕ} (i j : Fin d) : Mat d :=
  fun u v => if u = i ∧ v = j then 1 else 0

def nextIndex {d : ℕ} (j : Fin d) : Fin d :=
  ⟨(j.val+1)%d, Nat.mod_lt _ (Nat.zero_lt_of_lt j.isLt)⟩

def jacobi {d : ℕ} (J : JacobiData d) (theta : ℝ) : Mat d :=
  Matrix.diagonal (fun j => (J.diagonal j : ℂ)) + ∑ j : Fin d,
    if j.val+1 < d then (J.edge j : ℂ) •
      (matrixUnit j (nextIndex j) + matrixUnit (nextIndex j) j)
    else (J.edge j : ℂ) •
      (Complex.exp (-Complex.I*(theta : ℂ)) • matrixUnit j (nextIndex j) +
       Complex.exp (Complex.I*(theta : ℂ)) • matrixUnit (nextIndex j) j)

def bitJacobi {d : ℕ} (J : JacobiData d) (x : Fin d → Bool) : Mat d :=
  Matrix.diagonal (fun j => (J.diagonal j : ℂ)) + ∑ j : Fin d,
    ((J.edge j : ℂ) * (if x j then -1 else 1)) •
      (matrixUnit j (nextIndex j) + matrixUnit (nextIndex j) j)

def normalizedTrace {d : ℕ} (f : ℝ → ℝ) (A : Mat d) : ℝ :=
  (Matrix.trace (cfc f A)).re / d

def traceGap {d : ℕ} (f : ℝ → ℝ) (J : JacobiData d) : ℝ :=
  |normalizedTrace f (jacobi J 0) - normalizedTrace f (jacobi J Real.pi)|

def traceFunction {d : ℕ} (f : ℝ → ℝ) (J : JacobiData d) (x : Fin d → Bool) : ℝ :=
  normalizedTrace f (bitJacobi J x)

def JacobiBounded {d : ℕ} (J : JacobiData d) : Prop :=
  ‖jacobi J 0‖ ≤ 1 ∧ ‖jacobi J Real.pi‖ ≤ 1

/-- (8.4) for all real x and theta, fixing the discriminant convention. -/
def IsDiscriminant {d : ℕ} (J : JacobiData d) (Delta : Polynomial ℝ) : Prop :=
  ∀ x theta : ℝ, Matrix.det ((x : ℂ) • (1 : Mat d) - jacobi J theta) =
    ((2 * (∏ j, J.edge j) * (Delta.eval x - Real.cos theta) : ℝ) : ℂ)

/-- Measurement of an arbitrary output estimate; input-dependent success event only. -/
def Estimates {d T : ℕ} {W : Type} [Fintype W] [DecidableEq W]
    (A : QAlgorithms.QueryAlg (Fin d) Bool W T)
    (out : (Fin d × Bool) × W → ℝ) (tau : (Fin d → Bool) → ℝ) (delta : ℝ) : Prop :=
  ∀ x : Fin d → Bool,
    A.outputProb (QAlgorithms.xorOracle x)
      (fun z => decide (|out z - tau x| ≤ delta)) true ≥ (2:ℝ)/3

/-- All finite workspaces, all oracle-independent algorithms and real-valued output maps. -/
def QueryLowerBound {d : ℕ} (tau : (Fin d → Bool) → ℝ) (delta bound : ℝ) : Prop :=
  ∀ T : ℕ, ∀ (W : Type) [Fintype W] [DecidableEq W],
    ∀ A : QAlgorithms.QueryAlg (Fin d) Bool W T,
    ∀ out : (Fin d × Bool) × W → ℝ, Estimates A out tau delta → bound ≤ T

end
end HamSimTradeoff.AncillaDepth.Supplement


