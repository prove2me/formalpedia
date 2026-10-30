-- Prove2me | Definitions.Def_HRRPIncentives_SchemeI_Standing
-- name    : HRRPIncentives_SchemeI_Standing
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T03:13:06.121811+00:00
-- url     : https://prove2.me/theorems/9ba68ecc-4543-4dc5-8639-3de67bd17941
-- title:
--   Standing assumptions of the HRRP model
-- statement:
--   The standing assumptions of the model on the arrival rate $\lambda$, the box $B=[r_{\min},r_{\max}]\times[c_{\min},c_{\max}]$ and the investment cost $R(r,c)$, i.e. the fixed cost a hospital pays to bring its readmission rate down to $r$ and its marginal treatment cost down to $c$:
--
--   1. $\lambda>0$;
--   2. $0<r_{\min}<r_{\max}<1$ and $0\le c_{\min}<c_{\max}$;
--   3. $R$ is decreasing (non-increasing) in $r$ for each fixed $c$, and in $c$ for each fixed $r$, on $B$;
--   4. $R$ is jointly convex on $B$;
--   5. $R$ is twice differentiable on $B$ (it and its derivative are differentiable within $B$);
--   6. $R$ is sufficiently convex: at every point of $B$,
--   $$R_{rr}R_{cc}>(R_{rc}+\lambda)^2;$$
--   7. $R_{cr}\ge 0$ on $B$: readmission reduction is more costly when the treatment cost is low.
--
--   Here $R_r,R_c$ are the partial derivatives within $B$, $R_{rc}=\partial_c(\partial_rR)$ and $R_{cr}=\partial_r(\partial_cR)$. The paper uses these assumptions throughout; every theorem of this mission takes them as a hypothesis.
--
--   **Formalization Note** The page prints $r_{\min}\le r_{\max}$; the strict inequality is used because Lemma 1 (p. 11) puts the first best strictly inside $(r_{\min},r_{\max})$, so the paper's assumptions already exclude equality, and the box then has nonempty interior. "Decreasing" is read in the non-strict sense. The paper also imposes boundary conditions from its Appendix A to make optimal actions interior; Appendix A is not part of the source artifact and those conditions are **not** included here.
-- source:
--   Arifoğlu, Ren, Tezcan, Hospital Readmissions Reduction Program does not provide the right incentives: Issues and remedies, Management Science 67(4) (2021), author-accepted manuscript, unnumbered, p. 10 ("for some 0 < rmin ≤ rmax < 1 and 0 ≤ cmin < cmax < ∞"; "We assume that R(r, c) is decreasing and jointly convex in r and c, and is twice differentiable. Also we assume that RrrRcc > (Rrc + λ)² … and Rcr ⩾ 0"); λ the arrival rate, p. 9

import Mathlib
import Definitions.Def_HRRPIncentives_SchemeI_box
import Definitions.Def_HRRPIncentives_SchemeI_partialDeriv

namespace HRRPIncentives.SchemeI

/-- The standing assumptions of the HRRP model on the arrival rate `lam = λ`, the action box
`[rmin, rmax] × [cmin, cmax]` and the investment cost function `R(r, c)`.

Source: Arifoğlu, Ren, Tezcan, Hospital Readmissions Reduction Program does not provide the
right incentives: Issues and remedies, Management Science 67(4) (2021), author-accepted
manuscript, unnumbered, p. 10: "for some 0 < rmin ≤ rmax < 1 and 0 ≤ cmin < cmax < ∞", and
"We assume that R(r, c) is decreasing and jointly convex in r and c, and is twice
differentiable. Also we assume that RrrRcc > (Rrc + λ)², … and Rcr ⩾ 0"; λ is the patients'
arrival rate (p. 9).

**Formalization Note.**
* `lam_pos`: the arrival rate is positive (reading of p. 9).
* `rmin_lt_rmax`: strict, where the page prints `rmin ≤ rmax`; Lemma 1 (p. 11) places the
  first best strictly inside `(rmin, rmax)`, so the paper's assumptions already exclude
  `rmin = rmax`. It makes the box's interior nonempty so that derivatives within the box are
  unique.
* "Decreasing" is read as antitone (non-increasing) in each argument on the box, the weaker
  (more general) reading.
* "Twice differentiable" is differentiability of `R` and of its derivative within the box, on
  the closed box. Partial derivatives are `partialDeriv` along `(1,0)` (r) and `(0,1)` (c);
  `R_rc` is `∂_c(∂_r R)` and `R_cr` is `∂_r(∂_c R)`, in the printed order.
* The "additional boundary conditions" of Appendix A (p. 10) are **not** included: Appendix A
  is not in the artifact. -/
structure Standing (lam rmin rmax cmin cmax : ℝ) (R : ℝ × ℝ → ℝ) : Prop where
  lam_pos : 0 < lam
  rmin_pos : 0 < rmin
  rmin_lt_rmax : rmin < rmax
  rmax_lt_one : rmax < 1
  cmin_nonneg : 0 ≤ cmin
  cmin_lt_cmax : cmin < cmax
  antitone_r : ∀ c ∈ Set.Icc cmin cmax,
    AntitoneOn (fun r => R (r, c)) (Set.Icc rmin rmax)
  antitone_c : ∀ r ∈ Set.Icc rmin rmax,
    AntitoneOn (fun c => R (r, c)) (Set.Icc cmin cmax)
  convex : ConvexOn ℝ (box rmin rmax cmin cmax) R
  diff : DifferentiableOn ℝ R (box rmin rmax cmin cmax)
  diff2 : DifferentiableOn ℝ (fderivWithin ℝ R (box rmin rmax cmin cmax))
    (box rmin rmax cmin cmax)
  hessian : ∀ x ∈ box rmin rmax cmin cmax,
    (partialDeriv (partialDeriv R (box rmin rmax cmin cmax) (1, 0))
        (box rmin rmax cmin cmax) (0, 1) x + lam) ^ 2 <
      partialDeriv (partialDeriv R (box rmin rmax cmin cmax) (1, 0))
          (box rmin rmax cmin cmax) (1, 0) x *
        partialDeriv (partialDeriv R (box rmin rmax cmin cmax) (0, 1))
          (box rmin rmax cmin cmax) (0, 1) x
  cross : ∀ x ∈ box rmin rmax cmin cmax,
    0 ≤ partialDeriv (partialDeriv R (box rmin rmax cmin cmax) (0, 1))
      (box rmin rmax cmin cmax) (1, 0) x

end HRRPIncentives.SchemeI


