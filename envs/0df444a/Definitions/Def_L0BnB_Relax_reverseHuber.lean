-- Prove2me | Definitions.Def_L0BnB_Relax_reverseHuber
-- name    : L0BnB_Relax_reverseHuber
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T02:40:51.940385+00:00
-- url     : https://prove2.me/theorems/a3dda188-44aa-4c73-be4b-ef12006311d1
-- title:
--   Reverse Huber penalty $\mathcal B$, eq. (4)
-- statement:
--   The **reverse Huber penalty** $\mathcal B:\mathbb R\to\mathbb R$ is
--
--   $$\mathcal B(t)=\begin{cases}|t|, & |t|\le 1,\\ (t^2+1)/2, & |t|\ge 1.\end{cases}$$
--
--   It is a hybrid of the $\ell_1$ penalty (near the origin) and the squared $\ell_2$ penalty (far from it). It appears in the reduced form (6) of the perspective relaxation.
--
--   **Formalization Note** The two cases agree at $|t|=1$; the definition takes the first case there.
-- source:
--   Hazimeh, Mazumder, Saab, Sparse Regression at Scale: Branch-and-Bound rooted in First-Order Optimization, arXiv:2004.06152v2, eq. (4), p. 6

import Mathlib

namespace L0BnB.Relax

/-- **Reverse Huber penalty `B`**, eq. (4).
Hazimeh, Mazumder, Saab, *Sparse Regression at Scale: Branch-and-Bound rooted in First-Order
Optimization*, arXiv:2004.06152v2, eq. (4), p. 6: "The reverse Huber penalty `B : ℝ → ℝ`, is given by:
`B(t) = |t|` if `|t| ≤ 1`, `(t² + 1)/2` if `|t| ≥ 1`."

**Formalization Note.** The two printed cases overlap at `|t| = 1`, where they agree
(`1 = (1 + 1)/2`); the definition takes the first case there. -/
noncomputable def reverseHuber (t : ℝ) : ℝ :=
  if |t| ≤ 1 then |t| else (t ^ 2 + 1) / 2

end L0BnB.Relax


