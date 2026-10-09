-- Prove2me | Definitions.Def_CompositeLB_DetSmooth_Construction
-- name    : CompositeLB_DetSmooth_Construction
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T06:30:58.477929+00:00
-- url     : https://prove2.me/theorems/c4406130-8926-4b53-ad00-04dc68cfb9a0
-- title:
--   Equation (8) and Appendix B.3, pp. 6, 14–15 — quadratic hard functions and their minimizers
-- statement:
--   Fix orthonormal directions $v_0,\ldots,v_k$, binary indicators $\delta_{i,r}$, and a scalar $a$. The smooth hard component is the quadratic in equation (8):
--
--   $$f_i(x)=\frac18\left[\delta_{i,1}(\langle x,v_0\rangle^2-2a\langle x,v_0\rangle)+\sum_{r=1}^k\delta_{i,r}(\langle x,v_{r-1}\rangle-\langle x,v_r\rangle)^2+\delta_{i,k}\langle x,v_k\rangle^2\right].$$
--
--   The file also defines its round-$t$ truncation $f_i^t$, the aggregate quadratic $F^t$ from the second display on p. 14, and the explicit candidate minimizer $x_t^*=a\sum_{r=0}^{t-1}(1-(r+1)/(t+1))v_r$. These are the concrete instances used in the milestone statements.
--
--   **Formalization Note** The sum over $r=1,\ldots,k$ uses a closed interval and the truncated sum over $r=1,\ldots,t-1$ uses a half-open interval. The first displayed line for $F^t$ on p. 14 has a misplaced $\delta_{i,t}$ outside the component sum; the coherent second line is encoded. The definitions are algebraic for every input, while the results using $F^t$ impose $t\ge1$.
-- source:
--   Woodworth & Srebro, arXiv:1605.08003v3, Eq. (8), p. 6; Appendix B.3, pp. 14–15

import Mathlib
import Definitions.Def_CompositeLB_DetSmooth_Model

namespace CompositeLB.DetSmooth

/-- The component hard function `f_i` of (8) and Appendix B.3, p. 14, at the
normalisation `γ = B = 1`; `δ r` is the indicator `δ_{i,r}` of component `i`. -/
noncomputable def hardF {d : ℕ} (a : ℝ) (k : ℕ) (v : ℕ → CompositeLB.DetLip.E d) (δ : ℕ → ℝ)
    (x : CompositeLB.DetLip.E d) : ℝ :=
  1 / 8 * (δ 1 * ((inner ℝ x (v 0)) ^ 2 - 2 * a * (inner ℝ x (v 0))) +
    (∑ r ∈ Finset.Icc 1 k,
      δ r * (inner ℝ x (v (r - 1)) - inner ℝ x (v r)) ^ 2) +
    δ k * (inner ℝ x (v k)) ^ 2)

/-- The partial component hard function `f^t_i` used to answer queries during
round `t` in Appendix B.3, p. 14 (`k` is unused and kept for uniformity). -/
noncomputable def hardFt {d : ℕ} (a : ℝ) (_k : ℕ) (v : ℕ → CompositeLB.DetLip.E d) (δ : ℕ → ℝ)
    (t : ℕ) (x : CompositeLB.DetLip.E d) : ℝ :=
  1 / 8 * (δ 1 * ((inner ℝ x (v 0)) ^ 2 - 2 * a * (inner ℝ x (v 0))) +
    (∑ r ∈ Finset.Ico 1 t,
      δ r * (inner ℝ x (v (r - 1)) - inner ℝ x (v r)) ^ 2))

/-- `F^t` of p. 14, for `1 ≤ t`. The first line of the page's display puts
`δ_{i,t}⟨x, v_{t-1}⟩²` outside the sum over `i`; the second line, encoded here, is
the definition. At `t = 0` the index `t - 1` is truncated and the value is not used. -/
noncomputable def Fsum {d : ℕ} (m : ℕ) (a : ℝ) (v : ℕ → CompositeLB.DetLip.E d)
    (t : ℕ) (x : CompositeLB.DetLip.E d) : ℝ :=
  ((m / 2 : ℕ) : ℝ) / (8 * (m : ℝ)) *
    ((inner ℝ x (v 0)) ^ 2 - 2 * a * (inner ℝ x (v 0)) +
      (∑ r ∈ Finset.Ico 1 t,
        (inner ℝ x (v (r - 1)) - inner ℝ x (v r)) ^ 2) +
      (inner ℝ x (v (t - 1))) ^ 2)

/-- The explicit minimizer `x^*_t` on p. 15. -/
noncomputable def xstarT {d : ℕ} (a : ℝ) (v : ℕ → CompositeLB.DetLip.E d) (t : ℕ) : CompositeLB.DetLip.E d :=
  a • ∑ r ∈ Finset.range t,
    (1 - ((r : ℝ) + 1) / ((t : ℝ) + 1)) • v r

end CompositeLB.DetSmooth


