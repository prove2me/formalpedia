-- Prove2me | Definitions.Def_AnchoredEP_psi
-- name    : AnchoredEP_psi
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:39:00.456362+00:00
-- url     : https://prove2.me/theorems/37969aac-3f71-4476-8edc-1e1cde03a875
-- title:
--   Merit function $\psi_k$ of the line search
-- statement:
--   With $M_p=(p+1)L_p$, the **merit function** of the line search at outer iteration $k$ is
--   $$
--   \psi_k(a)=M_p\,a\,\|z_{k+1}(a)-z_{k+\frac12}(a)\|^{p-1}\quad(a>0),\qquad \psi_k(0)=0 .
--   $$
--   A step $a$ satisfies the acceptance window (84) exactly when $p!\rho/\sqrt2\le\psi_k(a)\le p!\rho$ with $\rho=1/\sqrt2$.
-- source:
--   Jiang–Yoon, Anchored Extra-Proximal Methods: Optimal Higher-Order Methods for Monotone Inclusion Problems, arXiv:2609.30212, Appendix G.2, Eq. (89), p.37

import Mathlib
import Definitions.Def_AnchoredEP_IterState
import Definitions.Def_AnchoredEP_trialDisp

namespace AnchoredEP

/-- **The merit function `ψ_k`.** Jiang–Yoon, arXiv:2609.30212, Appendix G.2, Eq. (89), p.37: "For
`a > 0`, define the merit function `ψ_k(a) := M_p a ‖z_{k+1}(a) − z_{k+½}(a)‖^{p−1}`, `ψ_k(0) := 0`",
where `M_p = (p + 1)L_p` (p.37).

**Formalization Note.** Defined by cases at `a = 0`, as in (89); for `a ≠ 0`,
`trialDisp … a = z_{k+1}(a) − z_{k+½}(a)`. The power `p − 1` is a natural-number power. -/
noncomputable def psi {d : ℕ} (F : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (p : ℕ) (L : ℝ)
    (sol : ℝ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (z0 : EuclideanSpace ℝ (Fin d)) (s : IterState d) (a : ℝ) : ℝ :=
  if a = 0 then 0 else ((p : ℝ) + 1) * L * a * ‖trialDisp F sol z0 s a‖ ^ (p - 1)

end AnchoredEP


