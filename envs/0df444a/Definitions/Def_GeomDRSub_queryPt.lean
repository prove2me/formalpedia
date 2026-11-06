-- Prove2me | Definitions.Def_GeomDRSub_queryPt
-- name    : GeomDRSub_queryPt
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:14:25.68886+00:00
-- url     : https://prove2.me/theorems/6af7f88d-09cf-4484-a252-578d25a8c1a3
-- title:
--   The query point $Y$ of (49)
-- statement:
--   Given a state $x$ with $p=h_\zeta(x)$, a coordinate $i$, a number $s\in[0,1]$ and a coin $u\in[0,1]$, the query point is
--   $$
--   Y=\begin{cases}u_{i,s},& u<p_i,\\ \ell_{i,s},& \text{otherwise}.\end{cases}
--   $$
--   With $I$ uniform on $[d]$, $S$ uniform on $[0,1]$ and an independent uniform coin $U$, this is the paper's rule (49): $Y=\ell_{I,S}$ with probability $1-p_I$ and $Y=u_{I,S}$ with probability $p_I$.
--
--   **Formalization Note** The branch is drawn through the uniform coin $u$; the resulting conditional law is the one of (49).
-- source:
--   Aggarwal–Lu, Geometry-Dependent Online and Offline Approximation for Non-Monotone DR-Submodular Maximization, arXiv:2610.00545, Section 5.1, p.17, Eq. (49)

import Mathlib
import Definitions.Def_GeomDRSub_hAct
import Definitions.Def_GeomDRSub_lowerPt
import Definitions.Def_GeomDRSub_upperPt

namespace GeomDRSub

/-- **The query point `Y`** of Eq. (49). Aggarwal–Lu, arXiv:2610.00545, Section 5.1, p.17: "Draw a
coordinate `I` uniformly from `[d]` and a number `S` uniformly from `[0, 1]`. Choose the query point
`Y` on the lower or the upper segment with probabilities `1 − p_I` and `p_I` … `Y = ℓ_{I,S}` with
probability `1 − p_I`, `u_{I,S}` with probability `p_I`".

`queryPt ζ x i s u` is `u_{i,s}` if `u < pᵢ` and `ℓ_{i,s}` otherwise, where `p = h_ζ(x)`.

**Formalization Note.** The branch is selected by a coin `u`: when `u` is uniform on `[0,1]`
(independently of `I, S`), the upper branch has probability `p_I` and the lower `1 − p_I`, which is
the conditional law of (49). -/
noncomputable def queryPt {d : ℕ} (ζ : ℝ) (x : EuclideanSpace ℝ (Fin d)) (i : Fin d)
    (s u : ℝ) : EuclideanSpace ℝ (Fin d) :=
  if u < hAct ζ x i then upperPt ζ x i s else lowerPt ζ x i s

end GeomDRSub


