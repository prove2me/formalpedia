-- Prove2me | Definitions.Def_GradedReserve_saleProb
-- name    : GradedReserve_saleProb
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:34:06.663107+00:00
-- url     : https://prove2.me/theorems/d7847138-00ba-43bc-9400-fb9ae2a99d06
-- title:
--   Probability of sale $s(v)$ in a symmetric equilibrium
-- statement:
--   In a symmetric equilibrium of $G_\pi$, type $v$ wins with probability $Q(v)s(v)$, where $s(v)=\pi(\beta(v))$ is its **probability of sale**; $s=0$ where the type does not trade.
--
--   **Formalization Note** For mixed strategies, $s(v)=q(v)/Q(v)$ (interim allocation divided by $Q$), which is $\pi(\beta(v))$ almost everywhere on the trading region and $0$ off it.
-- source:
--   Chen–Wang, Optimal Auctions for Anchored Bidders under a Rational Revenue Guarantee, manuscript (STOC 2027 submission; PDF sha256 6b1da440…1bab), Section 3.2, p.5 (PDF 6); proof of Lemma 3.2, p.14 (PDF 15)

import Mathlib
import Definitions.Def_GradedReserve_oppCdf
import Definitions.Def_GradedReserve_interimAlloc
open MeasureTheory ProbabilityTheory Set Filter Topology

namespace GradedReserve

/-- The probability of sale `s(v)` of type `v` in a symmetric equilibrium `σ` of `G_π` (Chen–Wang, *Optimal Auctions for Anchored Bidders under a Rational Revenue Guarantee*, manuscript (STOC 2027 submission),
Section 3.2, p.5, PDF 6: `s(v) = π(β(v))`, and type `v` wins with probability `Q(v) s(v)`).

**Formalization Note.** For mixed strategies `s` is the interim allocation divided by `Q(v)`; on
the trading region this is `π(β(v))` almost everywhere (proof of Lemma 3.3, (10), p.14) and it is
`0` where the type does not trade (proof of Lemma 3.2, p.14). At `v = 0`, `Q(0) = 0` and Lean's
`x / 0 = 0` gives `0`. -/
noncomputable def saleProb (f : ℝ → ℝ) (n : ℕ) (π : ℝ → ℝ) (σ : Kernel ℝ ℝ) (v : ℝ) : ℝ :=
  interimAlloc f n π σ v / oppCdf f n v

end GradedReserve


