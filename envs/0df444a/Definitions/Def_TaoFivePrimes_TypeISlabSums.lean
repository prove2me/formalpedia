-- Prove2me | Definitions.Def_TaoFivePrimes_TypeISlabSums
-- name    : TaoFivePrimes_TypeISlabSums
-- status  : Definition
-- author  : @andreaskapfer
-- created : 2026-09-22T14:52:20.311414+00:00
-- url     : https://prove2.me/theorems/57e00a54-fe81-4ab0-bb5c-d58bf340ee4e
-- title:
--   Type I slab sums for the sharp transfer gap (TaoFivePrimes child3 reduction)
-- statement:
--   ## Type I slab sums for the sharp transfer gap
--
--   For $x,\alpha\in\mathbb R$ and an integer $d$, these are the four Type I slab quantities used in the reduction of the Type I envelope comparison (`TaoFivePrimes.eta0VaughanTypeISum_le_theorem51TypeI`, Tao arXiv:1201.6656v4 Lemma 4.11):
--
--   * $S_1(d)=\sum_w (\log w)\,\eta_0(dw/x)\,e(\alpha dw)$ over the *full inner support* (odd $w$ with $x/4<dw<x$),
--   * $S_0(d)=\sum_w \eta_0(dw/x)\,e(\alpha dw)$ over the same support,
--   * $K(d)=\sum_w (\log w)\,\eta_0(dw/x)\,e(\alpha dw)$ over the *transferred* support ($w>\lfloor V\rfloor$),
--   * $S_3'=\sum_{d\in D,\ \lfloor U\rfloor<d} \tfrac12\mu(d)K(d)$, the transferred half-logarithmic block as a single global Moebius-weighted sum (keeping the cancellation), where $D$ is the set of odd divisors $d\le UV$ from `TaoFivePrimes.theorem51Divisors`.
-- source:
--   Terence Tao, arXiv:1201.6656v4, Section 4 Lemma 4.11 and Section 5; the slab decomposition is from the reduction of TaoFivePrimes node 62275301 (eta0VaughanTypeISum_le_theorem51TypeI, 'child3').

/-
Type I slab sums used in the sharp reduction of the Type I envelope comparison
for the centred Vaughan Type I part (child3, TaoFivePrimes node 62275301).
-/
import Definitions.Def_TaoFivePrimes_TypeIEnvelopeInterfaces

open scoped BigOperators ArithmeticFunction.Moebius
open ArithmeticFunction

namespace TaoFivePrimes

open TypeIOuterDAssembly

/-- Type I slab sum with the logarithmic weight `log w` over the full inner support. -/
noncomputable def typeISlabS1 (x alpha : ℝ) (d : ℕ) : ℂ :=
  ∑ w ∈ fullInnerSupport x d,
    ((Real.log (w : ℝ) : ℂ) * eta0VaughanTest x alpha (d * w))

/-- Type I slab sum with weight `1` over the full inner support. -/
noncomputable def typeISlabS0 (x alpha : ℝ) (d : ℕ) : ℂ :=
  ∑ w ∈ fullInnerSupport x d, eta0VaughanTest x alpha (d * w)

/-- Type I slab sum with weight `log w` over the transferred support (`w > ⌊V⌋`). -/
noncomputable def typeISlabK (x alpha V : ℝ) (d : ℕ) : ℂ :=
  ∑ w ∈ transferredInnerSupport x V d,
    ((Real.log (w : ℝ) : ℂ) * eta0VaughanTest x alpha (d * w))

/-- The transferred half-logarithmic block as a single global Möbius-weighted sum. -/
noncomputable def typeISlabS3 (x alpha U V : ℝ) : ℂ :=
  ∑ d ∈ (theorem51Divisors U V).filter (fun d => ⌊U⌋₊ < d),
    ((μ d : ℂ) * (1 / 2 : ℂ)) * typeISlabK x alpha V d

end TaoFivePrimes


