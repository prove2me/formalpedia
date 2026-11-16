-- Prove2me | Definitions.Def_GradedReserve_Supplement_rMinus
-- name    : GradedReserve_Supplement_rMinus
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T03:45:38.512011+00:00
-- url     : https://prove2.me/theorems/a0b88e58-cc6e-49e2-925a-43917c60e354
-- title:
--   Lowest admissible hard reserve $r^-_\varepsilon=\min\Phi_\varepsilon$
-- statement:
--   With $\tau=(1-\varepsilon)R^*$ and $\Phi_\varepsilon=\{r: R_n(r)\ge\tau\}=[r^-_\varepsilon,r^+_\varepsilon]$,
--   $$r^-_\varepsilon=\min\Phi_\varepsilon=\inf\{r\in[0,1]:\ R_n(r)\ge\tau\}.$$
--
--   **Formalization Note** The set contains $r^*$ for $\varepsilon\ge0$, so it is nonempty and bounded.
-- source:
--   Chen–Wang, Optimal Auctions for Anchored Bidders under a Rational Revenue Guarantee, manuscript (STOC 2027 submission; PDF sha256 6b1da440…1bab), Section 2, p.4 (PDF 5)

import Mathlib
import Definitions.Def_GradedReserve_revCurve
import Definitions.Def_GradedReserve_optRevenue
open MeasureTheory ProbabilityTheory Set Filter Topology

namespace GradedReserve.Supplement

/-- `r⁻_ε = min Φ_ε`, where `Φ_ε = {r : R_n(r) ≥ τ} = [r⁻_ε, r⁺_ε]` and `τ = (1 − ε) R*`
(Chen–Wang, *Optimal Auctions for Anchored Bidders under a Rational Revenue Guarantee*, manuscript (STOC 2027 submission), Section 2, p.4, PDF 5). The lowest reserve whose standard auction meets the guarantee.

**Formalization Note.** The infimum is over reserves `r ∈ [0, 1]`. The set contains `r*` when
`ε ≥ 0` (`R_n(r*) = R*`), so it is nonempty and bounded, and `sInf` is not a junk value. -/
noncomputable def rMinus (f : ℝ → ℝ) (n : ℕ) (ε : ℝ) : ℝ :=
  sInf {r ∈ Icc (0:ℝ) 1 | (1 - ε) * optRevenue f n ≤ revCurve f n r}

end GradedReserve.Supplement


