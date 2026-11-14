-- Prove2me | Definitions.Def_NarrowDNF_HatamiCrossTerms
-- name    : NarrowDNF_HatamiCrossTerms
-- status  : Definition
-- author  : @chenghua.liu
-- created : 2026-11-13T08:01:39.719255+00:00
-- url     : https://prove2.me/theorems/a78636d3-b875-460e-800d-823b148b5c4f
-- title:
--   Inactive-fiber kernels and off-diagonal residual correlations
-- statement:
--   Let $J$ be a local activation family on a finite Boolean cube, and let $\mu_p^T(x_T)$ denote the Bernoulli mass of the labels restricted to $T$. The inactive-fiber kernel is
--   $$K_p(J,T)=\mathbb E_p\!\left[\mathbf1_{\{J_T(X)=0\}}\,\bigl(\mu_p^T(X_T)\bigr)^{-2}\right].$$
--   The code writes this as zero on firing inputs and the reciprocal square on inactive inputs. For $0<p<1$, all local masses are positive.
--
--   For a real-valued function $f$, let $\widetilde F_S$ be its Fourier component conditioned on the adaptive partition formed from activations indexed inside $S$. Given a finite retained family $A$, define
--   $$\operatorname{CrossEnvelope}_p(J,f,A)=\sum_{S\in A}\sum_{R\in A,\ R\ne S}\max\{0,\mathbb E_p[\widetilde F_S(X)\widetilde F_R(X)]\}.$$
--   The sum uses ordered pairs and discards negative correlations. It is the nonnegative off-diagonal quantity controlled by the corrected residual estimate; the estimate itself is not part of these definitions.
-- source:
--   https://github.com/liuchliuch/narrow-dnf-lean/blob/eecadd6a5ea0a331d6cf9fd5cb39fc6ec854b372/NarrowDNF/HatamiCrossTerms.lean#L234-L238
--   https://github.com/liuchliuch/narrow-dnf-lean/blob/eecadd6a5ea0a331d6cf9fd5cb39fc6ec854b372/NarrowDNF/HatamiCrossTerms.lean#L23-L25

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Bool.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Image
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Real.Basic
import Mathlib.Logic.Equiv.Prod
import Mathlib.Order.Monotone.Basic
import Mathlib.Tactic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_NarrowDNF_Adaptive
import Definitions.Def_NarrowDNF_HatamiActivation
import Definitions.Def_NarrowDNF_HatamiResidual
import Definitions.Def_NarrowDNF_ProductMeasure

namespace NarrowDNF.HatamiActivation
end NarrowDNF.HatamiActivation

namespace NarrowDNF.HatamiCrossTerms
end NarrowDNF.HatamiCrossTerms

namespace NarrowDNF.HatamiResidual
end NarrowDNF.HatamiResidual

namespace NarrowDNF.ProductMeasure
end NarrowDNF.ProductMeasure


/-!
# Hatami's corrected cross-term estimate

Finite cross-term estimates for the exact restricted-activation conditional
components. The repaired coefficient factor is retained explicitly.
-/

noncomputable section
open scoped BigOperators

namespace NarrowDNF.HatamiCrossTerms

open ProductMeasure HatamiResidual HatamiActivation
attribute [local instance] Classical.propDecidable
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The inactive overlap-fiber kernel used in Hatami's cross-term sum. -/
def inactiveKernel (p : ℝ) (J : Activation ι) (T : Finset ι) : ℝ :=
  expectation p (fun x => if J.fires T x then 0 else 1 / localMass p T x ^ 2)





















/-- Nonnegative envelope of the off-diagonal conditional-component correlations. -/
def crossEnvelope (p : ℝ) (J : Activation ι) (f : Cube ι → ℝ)
    (A : Finset (Finset ι)) : ℝ :=
  ∑ S ∈ A, ∑ R ∈ A, if S = R then 0 else
    max 0 (expectation p (fun x => approxComponent p J f S x * approxComponent p J f R x))



























end NarrowDNF.HatamiCrossTerms


