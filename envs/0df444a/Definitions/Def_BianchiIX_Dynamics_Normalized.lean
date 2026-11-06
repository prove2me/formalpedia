-- Prove2me | Definitions.Def_BianchiIX_Dynamics_Normalized
-- name    : BianchiIX_Dynamics_Normalized
-- status  : Definition
-- author  : @trppppp
-- created : 2026-11-04T13:53:19.863435+00:00
-- url     : https://prove2.me/theorems/462a060a-16d3-427e-866d-c921d2bc6add
-- title:
--   State space and normalized Bianchi IX equations
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
--   The autonomous equation $\dot x=F(x)$ describes the normalized flow.
--   The constraint function $\mathcal C$ and the positive-wall domain $W$ are
--   defined on the full state space $X$.
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Dynamics/Normalized.lean

import Definitions.Def_BianchiIX_Algebra_Flow
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

noncomputable section

namespace BianchiIX

open Set

/-- Coordinates are `(p, s, N₁, N₂, N₃)`, with the finite-dimensional sup norm. -/
abbrev NormalizedState := Fin 5 → ℝ

def normalizedField (x : NormalizedState) : NormalizedState :=
  ![shearPlus (x 0) (x 2) (x 3) (x 4),
    shearMinus (x 1) (x 2) (x 3) (x 4),
    rateOne (x 0) (x 1) * x 2,
    rateTwo (x 0) (x 1) * x 3,
    rateThree (x 0) (x 1) * x 4]

def stateConstraint (x : NormalizedState) : ℝ := constraint (x 0) (x 1) (x 2) (x 3) (x 4)

def positiveWalls (x : NormalizedState) : Prop := 0 < x 2 ∧ 0 < x 3 ∧ 0 < x 4













end BianchiIX


