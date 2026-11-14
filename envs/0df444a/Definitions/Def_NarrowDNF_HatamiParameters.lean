-- Prove2me | Definitions.Def_NarrowDNF_HatamiParameters
-- name    : NarrowDNF_HatamiParameters
-- status  : Definition
-- author  : @chenghua.liu
-- created : 2026-11-13T07:59:04.574245+00:00
-- url     : https://prove2.me/theorems/a1d025ad-47b2-4f6e-ab7c-4225052a7497
-- title:
--   Explicit threshold, tail, load, and corrected cross-term parameters
-- statement:
--   For real parameters $k$ and $e_0$, define
--   $$\delta(k)=2^{-100k^2},\qquad\epsilon_1(k,e_0)=3^{-10k^2}e_0^{10k}.$$
--   The load expression and corrected cross-term expression are the explicit functions
--   $$L(k,e_0)=\frac{k\,2^{2k}}{\delta(k)\epsilon_1(k,e_0)^2},\qquad Q(k,e_0)=\frac{2^{9k}\delta(k)}{\epsilon_1(k,e_0)^2}.$$
--   The powers use real exponentiation, as in the numerical parameter choices of the paper. Conditions ensuring positivity or bounds on these expressions are hypotheses of the later arithmetic lemmas, not restrictions silently imposed by the definitions.
--
--   These functions coordinate the degree cutoff, activation threshold, retained Fourier tails, multiplicity-counted load, and residual-error budget. The factor $2^{9k}$ in $Q$ records the corrected coefficient estimate, including the support-size factor retained in the formal proof. Subsequent numerical estimates compare these actual expressions with the paper's final error and exponential-load budgets.
-- source:
--   https://github.com/liuchliuch/narrow-dnf-lean/blob/eecadd6a5ea0a331d6cf9fd5cb39fc6ec854b372/NarrowDNF/HatamiParameters.lean#L71-L74
--   https://github.com/liuchliuch/narrow-dnf-lean/blob/eecadd6a5ea0a331d6cf9fd5cb39fc6ec854b372/NarrowDNF/HatamiParameters.lean#L13-L13
--   https://github.com/liuchliuch/narrow-dnf-lean/blob/eecadd6a5ea0a331d6cf9fd5cb39fc6ec854b372/NarrowDNF/HatamiParameters.lean#L14-L14
--   https://github.com/liuchliuch/narrow-dnf-lean/blob/eecadd6a5ea0a331d6cf9fd5cb39fc6ec854b372/NarrowDNF/HatamiParameters.lean#L15-L15

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace NarrowDNF.HatamiParameters
end NarrowDNF.HatamiParameters


/-! Explicit numerical bounds for the parameters in Appendix A. -/
noncomputable section
namespace NarrowDNF.HatamiParameters

def delta (k : ℝ) : ℝ := (2 : ℝ) ^ (-(100 : ℝ) * k^2)
def epsilonOne (k e0 : ℝ) : ℝ := (3 : ℝ) ^ (-(10 : ℝ)*k^2) * e0 ^ ((10 : ℝ)*k)
def loadExpression (k e0 : ℝ) : ℝ := k * (2 : ℝ) ^ ((2 : ℝ)*k) / (delta k * (epsilonOne k e0)^2)












/-- Corrected cross-term expression after retaining the missing 2^|S| factor
in the external Hatami coefficient bound. -/
def correctedCrossExpression (k e0 : ℝ) : ℝ :=
  (2 : ℝ)^((9:ℝ)*k) * delta k / (epsilonOne k e0)^2



end NarrowDNF.HatamiParameters


