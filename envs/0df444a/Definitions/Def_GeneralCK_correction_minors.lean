-- Prove2me | Definitions.Def_GeneralCK_correction_minors
-- name    : GeneralCK_correction_minors
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-09-24T21:19:31.140997+00:00
-- url     : https://prove2.me/theorems/01ecac24-4fc5-4868-8a4c-1943cb9f197e
-- title:
--   The entropy correction matrix entries and determinant
-- statement:
--   For real entropy coordinates $e,f$, use the previously defined correction quantities $g=\operatorname{gap}(e,f)$, $s=\operatorname{mid}(e,f)$, $q_e=q(e)$, $q_f=q(f)$, and $A_l,A_r,Z_l,Z_r$. Let $\lambda=2\log2\,\frac{d^2}{dr^2}F(r,s)|_{r=g}$. The four definitions are $$M_l=A_l-\lambda Z_l^2,\qquad M_{lr}=-(q_e+q_f)-\lambda Z_lZ_r,\qquad M_r=A_r-\lambda Z_r^2,$$ $$M_{\det}=M_lM_r-M_{lr}^2.$$ The formal names are Mleft, Mcross, Mright, and Mdet. Regional certificates state positivity of Mleft and Mdet on their specified domains. This bundle provides only the exact mathematical interface, without numerical certificate data or positivity assumptions.
-- source:
--   https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/CorrectionHessianPSD.lean#L5-L11

import Mathlib.Analysis.Calculus.Deriv.Inverse
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Order.MonotoneContinuity
import Definitions.Def_GeneralCK_statement
import Definitions.Def_GeneralCK_bellman
import Definitions.Def_GeneralCK_correction_entries

namespace GeneralCK.Correction

noncomputable def Mleft (e f : ℝ) : ℝ := Aleft e f-2*Real.log 2*
  deriv (deriv (fun r => F r (mid e f))) (gap e f)*(Zleft e f)^2
noncomputable def Mcross (e f : ℝ) : ℝ := -(q e+q f)-2*Real.log 2*
  deriv (deriv (fun r => F r (mid e f))) (gap e f)*Zleft e f*Zright e f
noncomputable def Mright (e f : ℝ) : ℝ := Aright e f-2*Real.log 2*
  deriv (deriv (fun r => F r (mid e f))) (gap e f)*(Zright e f)^2
noncomputable def Mdet (e f : ℝ) : ℝ := Mleft e f*Mright e f-(Mcross e f)^2




















end GeneralCK.Correction


