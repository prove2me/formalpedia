-- Prove2me | Definitions.Def_DRBaseline_IsLeastRebateOptimal
-- name    : DRBaseline_IsLeastRebateOptimal
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:42:28.254994+00:00
-- url     : https://prove2.me/theorems/0a9e1fa0-1aa0-43ce-a27a-64f26b489d67
-- title:
--   Least-rebate maximizer $(b^*,r^*)$
-- statement:
--   $(b,r)$ is the **least-rebate maximizer** if it is firm-optimal and $r\le r'$ for every firm-optimal $(b',r')$.
--
--   This is the selection the paper makes: for $\Delta c\ge4\Omega c_s$ every point of the ridge $rb=2\Omega^2c_s$, $r\ge2\Omega c_s$ maximizes $C$, and the paper takes $r^*=2\Omega c_s$, $b^*=\Omega$. Below $4\Omega c_s$ the maximizer is unique.
-- source:
--   Agrawal, Yücel, Design of Electricity Demand-Response Programs, manuscript of May 26, 2021, §5.2, p.15; Online Appendix, p.OA3; note to Figure 2, p.16

import Mathlib
import Definitions.Def_DRBaseline_IsFirmOptimal

namespace DRBaseline

/-- **`(b∗, r∗)` is the least-rebate maximizer of the firm's net savings.**
Agrawal, Yücel, *Design of Electricity Demand-Response Programs*, manuscript of May 26, 2021, §5.2, p.15 ("Let (b∗,r∗) .= arg max_{b,r} C(b,r)") and the Online Appendix, Proof of
Lemma 3 and 4, and Propositions 2, 3, and 4, p.OA3 ("This implies r∗(·) = rC .= 2Ωcs and
b∗(·) = B2(rC) = Ω"), together with the note to Figure 2, p.16.

`(b, r)` maximizes `C` over the quadrant and its rebate is the smallest among all maximizers.

**Formalization Note** For `Δc ≥ 4Ωc_s` every point of the ridge `rb = 2Ω²c_s`,
`r ≥ 2Ωc_s` is a maximizer, and the paper selects `(Ω, 2Ωc_s)`, the one with the least
rebate. Below that the maximizer is unique and this is just `IsFirmOptimal`. -/
def IsLeastRebateOptimal (Ω ρ Δc : ℝ) (s : ℝ → ℝ → ℝ → ℝ) (b r : ℝ) : Prop :=
  IsFirmOptimal Ω ρ Δc s b r ∧ ∀ b' r' : ℝ, IsFirmOptimal Ω ρ Δc s b' r' → r ≤ r'

end DRBaseline


