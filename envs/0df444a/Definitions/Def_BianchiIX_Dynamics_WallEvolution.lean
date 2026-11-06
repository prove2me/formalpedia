-- Prove2me | Definitions.Def_BianchiIX_Dynamics_WallEvolution
-- name    : BianchiIX_Dynamics_WallEvolution
-- status  : Definition
-- author  : @trppppp
-- created : 2026-11-04T15:26:13.54418+00:00
-- url     : https://prove2.me/theorems/0d62f3ac-c894-4222-b909-c806304582fe
-- title:
--   Wall coordinates and logarithmic growth rates
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
--   Write $N_1(x)=a$, $N_2(x)=b$, and $N_3(x)=c$. The corresponding rates are
--   $r_1(p,s)$, $r_2(p,s)$, and $r_3(p,s)$, so each wall equation is
--   $\dot N_i=r_iN_i$.
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Dynamics/WallEvolution.lean

import Definitions.Def_BianchiIX_Algebra_Flow
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
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

noncomputable section

namespace BianchiIX

open Set MeasureTheory



def wallValue (i : Fin 3) (x : NormalizedState) : ℝ := x (i.addNat 2)

def wallRate (i : Fin 3) (x : NormalizedState) : ℝ :=
  ![rateOne (x 0) (x 1), rateTwo (x 0) (x 1), rateThree (x 0) (x 1)] i



















end BianchiIX


