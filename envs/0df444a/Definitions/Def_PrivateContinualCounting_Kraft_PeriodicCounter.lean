-- Prove2me | Definitions.Def_PrivateContinualCounting_Kraft_PeriodicCounter
-- name    : PrivateContinualCounting_Kraft_PeriodicCounter
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T12:00:01.086219+00:00
-- url     : https://prove2.me/theorems/9d4046dd-da35-4777-ab32-c75da5a30337
-- title:
--   Fixed-period counters with countable internal coordinates
-- statement:
--   Fix $p\ge1$ and a countable set $I_0$. A periodic counter is a full Gaussian counter with internal indices $(b',i)\in\mathbb N\times I_0$ and block Toeplitz coefficients. For source time $t=pb+a+1$, where $0\le a<p$, its matrices satisfy
--   $$L_{(b,a),(b',i)}=\mathbf1_{b'\le b}L^{(b-b')}_{a,i},\qquad
--   R_{(b',i),(b'',c)}=\mathbf1_{b''\le b'}R^{(b'-b'')}_{i,c}.$$
--   The underlying counter supplies square-summable rows and columns, exact prefix factorisation, finite global sensitivity, and the L² Gaussian sums. Consequently its product has the lower-triangular all-ones matrix at lag zero and the all-ones matrix at every positive lag. The phase energy is $E_{a,n}=\sum_{d<n}\sum_i(L^{(d)}_{a,i})^2$. The definition keeps every phase and allows infinitely many internal coordinates; the fixed period cannot vary with time. These are the precise periodic objects in the divergence statements.
-- source:
--   Kisung Park, STOC 2027 submission #86 (October 2026), p. 18, PDF p. 20, Appendix A, Periodic counters, preamble to Lemma A.1

import Definitions.Def_PrivateContinualCounting_Kraft_GaussianCounter

open MeasureTheory ProbabilityTheory Filter

set_option autoImplicit false

namespace PrivateContinualCounting.Kraft

/-- Appendix A: coefficients on an arbitrary countable internal index set I₀.
The counter itself carries square-summable rows/columns, exact factorisation and its L² sums.
No cutoff depending on the within-block phase is imposed. -/
structure PeriodicCounter (p : ℕ) (I₀ : Type) [Countable I₀] where
  positive_period : 0 < p
  counter : GaussianCounter (ℕ × I₀)
  Lblock : ℕ → Fin p → I₀ → ℝ
  Rblock : ℕ → I₀ → Fin p → ℝ
  decoder_toeplitz : ∀ b (a : Fin p) b' i,
    counter.factors.L (p * b + a.val) (b', i) =
      if b' ≤ b then Lblock (b - b') a i else 0
  strategy_toeplitz : ∀ b' i b (c : Fin p),
    counter.factors.R (b', i) (p * b + c.val) =
      if b ≤ b' then Rblock (b' - b) i c else 0

/-- Phase energy up to block n, used in the Appendix A extension of Theorem 3.1. -/
noncomputable def PeriodicCounter.phaseEnergy {p : ℕ} {I₀ : Type} [Countable I₀]
    (M : PeriodicCounter p I₀) (a : Fin p) (n : ℕ) : ℝ :=
  ∑ d ∈ Finset.range n, ∑' i, (M.Lblock d a i) ^ 2

end PrivateContinualCounting.Kraft


