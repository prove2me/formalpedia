-- Prove2me | Definitions.Def_HRRPIncentives_SchemeI_box
-- name    : HRRPIncentives_SchemeI_box
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T03:12:30.95186+00:00
-- url     : https://prove2.me/theorems/009e4691-f9fe-4185-b72e-e747a246c7e8
-- title:
--   Action box $[r_{\min},r_{\max}]\times[c_{\min},c_{\max}]$
-- statement:
--   Each hospital chooses a readmission rate $r$ and a marginal treatment cost $c$ from the box
--
--   $$B=[r_{\min},r_{\max}]\times[c_{\min},c_{\max}]\subseteq\mathbb R^2 .$$
--
--   A point of $B$ is a pair $(r,c)$, first coordinate the readmission rate, second the cost. This set is the strategy space of every hospital in the HRRP game and the domain of the investment cost $R$.
--
--   **Formalization Note** The bounds on $r_{\min},r_{\max},c_{\min},c_{\max}$ are not part of this definition; they are recorded in the standing assumptions.
-- source:
--   Arifoğlu, Ren, Tezcan, Hospital Readmissions Reduction Program does not provide the right incentives: Issues and remedies, Management Science 67(4) (2021), author-accepted manuscript, unnumbered, p. 10 ("we assume that r ∈ [rmin, rmax] and c ∈ [cmin, cmax]")

import Mathlib

namespace HRRPIncentives.SchemeI

/-- The action box of a hospital: readmission rate `r ∈ [rmin, rmax]` and marginal treatment
cost `c ∈ [cmin, cmax]`.

Source: Arifoğlu, Ren, Tezcan, Hospital Readmissions Reduction Program does not provide the
right incentives: Issues and remedies, Management Science 67(4) (2021), author-accepted
manuscript, unnumbered, p. 10 ("we assume that r ∈ [rmin, rmax] and c ∈ [cmin, cmax]").

**Formalization Note.** A point is a pair `(r, c)`: `.1` is the readmission rate `r`, `.2` is
the marginal cost `c`. The bounds on `rmin, rmax, cmin, cmax` are not part of this definition;
they are fields of `Standing`. -/
def box (rmin rmax cmin cmax : ℝ) : Set (ℝ × ℝ) :=
  Set.Icc rmin rmax ×ˢ Set.Icc cmin cmax

end HRRPIncentives.SchemeI


