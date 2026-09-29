-- Prove2me | Definitions.Def_GeneralCK_correction_entries
-- name    : GeneralCK_correction_entries
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-09-24T21:19:07.907726+00:00
-- url     : https://prove2.me/theorems/161d0c84-556a-408b-ab3d-9efb4bf27971
-- title:
--   Algebraic entries of the entropy correction matrix
-- statement:
--   For real entropy coordinates $e,f$, let $u=\operatorname{entropyInverse}(e)$ and $v=\operatorname{entropyInverse}(f)$, using the lower entropy inverse from the Bellman interface. Put $g=v-u$, $s=(e+f)/2$, $t=g/s$, $q_e=u(1-u)$, and $q_f=v(1-v)$. With $L=\log2$, $a=J(u)$, $b=J(v)$, and $D=\frac{d}{dr}F(r,1)|_{r=t}$, the bundle defines $$Z_l=-q_e-tq_ea/2,\qquad Z_r=q_f(1-tb/2),$$ $$A_l=\frac{q_eL(a+b+2D)+g(La(1-2u)-1)}{La},\qquad A_r=\frac{q_fL(a+b-2D)+g(1-Lb(1-2v))}{Lb}.$$ Here $J$ and $F$ are the previously defined entropy-slope and radial profiles. These eight exact definitions are the source's algebraic ingredients for the correction matrix; no positivity or Hessian identity is asserted by this bundle.
-- source:
--   https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/CorrectionHessian.lean#L26-L342

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

namespace GeneralCK
open Set Filter
open scoped Topology



namespace Correction

noncomputable def gap (e f : ℝ) : ℝ := entropyInverse f-entropyInverse e
noncomputable def mid (e f : ℝ) : ℝ := (e+f)/2
noncomputable def normalized (e f : ℝ) : ℝ := gap e f/mid e f















































noncomputable def q (e : ℝ) : ℝ := entropyInverse e*(1-entropyInverse e)
noncomputable def Zleft (e f : ℝ) : ℝ :=
  -q e-normalized e f*q e*J (entropyInverse e)/2
noncomputable def Zright (e f : ℝ) : ℝ :=
  q f*(1-normalized e f*J (entropyInverse f)/2)
noncomputable def Aleft (e f : ℝ) : ℝ :=
  (q e*(Real.log 2*J (entropyInverse e)+Real.log 2*J (entropyInverse f)+
     2*Real.log 2*deriv (fun r => F r 1) (normalized e f))+
   gap e f*(Real.log 2*J (entropyInverse e)*(1-2*entropyInverse e)-1)) /
     (Real.log 2*J (entropyInverse e))





















noncomputable def Aright (e f : ℝ) : ℝ :=
  (q f*(Real.log 2*J (entropyInverse e)+Real.log 2*J (entropyInverse f)-
     2*Real.log 2*deriv (fun r => F r 1) (normalized e f))+
   gap e f*(1-Real.log 2*J (entropyInverse f)*(1-2*entropyInverse f))) /
     (Real.log 2*J (entropyInverse f))












end Correction
end GeneralCK


