-- Prove2me | Definitions.Def_HamSimTradeoff_AncillaDepth_ExponentialSums
-- name    : HamSimTradeoff_AncillaDepth_ExponentialSums
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T20:43:19.701016+00:00
-- url     : https://prove2.me/theorems/40072aa9-4071-416b-b6c7-a7770e3a8841
-- title:
--   Complex exponential sums and compact-interval uniform norms
-- statement:
--   For an integer $M\ge0$, complex coefficients $b,a_1,\ldots,a_M$, and real frequencies $\lambda_1,\ldots,\lambda_M$, put
--   $$f(t)=bt+\sum_{j=1}^{M}a_je^{i\lambda_jt}.$$
--   For a complex-valued function $f$ and real $l,u$, define
--   $$\|f\|_{[l,u]}=\sup\{|f(t)|:l\le t\le u\}.$$
--   Only continuous functions on the nonempty compact intervals $[0,1]$ and $[-1,1]$ enter the theorems. This reusable definition supplies the exact norms and exponential sums in the Markov-type estimates.
--
--   **Formalization Note** The real supremum returns Lean's default value on empty or unbounded sets; none of those sets occurs in a theorem application here. Distinctness of frequencies is a hypothesis of Lemma 3.4, rather than a restriction built into the general definition. Complex modulus is the usual norm on $\mathbb C$.
-- source:
--   Yuxin Zhang, Changpeng Shao, Time-space tradeoffs for Hamiltonian simulation, STOC 2027 submission #334 (October 2026), p.17, Lemma 3.4 and Eq. (3.7); pp.18–19, Lemma 3.5 and Eq. (3.8)

import Mathlib
open scoped BigOperators

namespace HamSimTradeoff.AncillaDepth
noncomputable section

/-- Pointwise supremum on a compact real interval; only used for continuous functions. -/
def intervalNorm (f : ℝ → ℂ) (lo hi : ℝ) : ℝ :=
  sSup ((fun t => ‖f t‖) '' Set.Icc lo hi)

def exponentialSum {M : ℕ} (b : ℂ) (a : Fin M → ℂ) (freq : Fin M → ℝ) (t : ℝ) : ℂ :=
  b * (t : ℂ) + ∑ j, a j * Complex.exp (Complex.I * (freq j : ℂ) * (t : ℂ))

end
end HamSimTradeoff.AncillaDepth


