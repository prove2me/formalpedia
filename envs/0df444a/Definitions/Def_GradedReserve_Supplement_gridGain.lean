-- Prove2me | Definitions.Def_GradedReserve_Supplement_gridGain
-- name    : GradedReserve_Supplement_gridGain
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T03:48:22.983686+00:00
-- url     : https://prove2.me/theorems/033977bd-f0f6-4222-8aca-37e5b2b87e1d
-- title:
--   Gain from a grid deviation against the rounded profile
-- statement:
--   When every opponent plays the pure strategy $b$ (values i.i.d. with law $F$), the gain of type $v$ of bidder $i$ from the grid action $g$ is
--   $$u_i(v,g)-u_i\big(v,b(v)\big),$$
--   the utility from $g$ minus the utility from its prescribed action. A profile is a **$\delta$-BNE type by type** for bidder $i$ when this gain is at most $\delta$ for every grid action.
-- source:
--   Chen–Wang, Optimal Auctions for Anchored Bidders under a Rational Revenue Guarantee, manuscript (STOC 2027 submission; PDF sha256 6b1da440…1bab), Theorem 6.1 part 2, p.11 (PDF 12); proof p.34 (PDF 35)

import Mathlib
import Definitions.Def_GradedReserve_typeMeasure
import Definitions.Def_GradedReserve_Supplement_payoffAgainst
open MeasureTheory ProbabilityTheory Set Filter Topology

namespace GradedReserve.Supplement

/-- The gain of type `v` of bidder `i` from the grid deviation `g`, relative to its prescribed
action `b v`, when every opponent plays the pure strategy `b` with values i.i.d. `typeMeasure f`
(Chen–Wang, *Optimal Auctions for Anchored Bidders under a Rational Revenue Guarantee*, manuscript (STOC 2027 submission), Theorem 6.1 part 2, p.11, PDF 12, "play a `δ`-BNE, type by type"; proof p.34, PDF 35:
`Ug(g; v)`, the utility from the grid bid `g` when opponents use `β̃`). A profile is a `δ`-BNE
type by type for bidder `i` when this gain is at most `δ` for every grid action `g`.

**Formalization Note.** The opponents' action law is the image of the value law under `b`; for the
rounded strategies of Theorem 6.1, `b` is measurable. -/
noncomputable def gridGain {n : ℕ} (M : Mechanism n) (f : ℝ → ℝ) (b : ℝ → ℝ) (i : Fin n)
    (v g : ℝ) : ℝ :=
  payoffAgainst M (Measure.pi fun _ => (typeMeasure f).map b) i v g
    - payoffAgainst M (Measure.pi fun _ => (typeMeasure f).map b) i v (b v)

end GradedReserve.Supplement


