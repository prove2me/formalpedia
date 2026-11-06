-- Prove2me | Definitions.Def_IAFTRL_perpBasis
-- name    : IAFTRL_perpBasis
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:44:39.458584+00:00
-- url     : https://prove2.me/theorems/32720447-0e9d-41f4-a20c-27a8f6292374
-- title:
--   An orthonormal basis matrix $U_b$ of $b^\perp$
-- statement:
--   For a nonzero vector $b\in\mathbb R^d$, $U_b$ is a $d\times(d-1)$ real matrix whose columns are orthonormal and orthogonal to $b$:
--   $$
--   U_b^\top U_b=I_{d-1},\qquad U_b^\top b=0 .
--   $$
--   Its columns form an orthonormal basis of the hyperplane $b^\perp=u_b^\perp$, $u_b=b/\|b\|$. It is the coordinate system used in Definition C.1 of the interpolation constant $G_{\mathcal A}$.
--
--   **Formalization Note** One such matrix is fixed by a choice principle (`Classical.epsilon`); for $b\ne0$ such matrices exist, and by Lemma C.1 of the paper the constant $G_{\mathcal A}$ does not depend on the choice. For $b=0$ the value is never used.
-- source:
--   Zhao–Tan, Best-of-Both-Worlds FTRL for Linear Bandits, arXiv:2611.01299, Definition C.1, p.56

import Mathlib

namespace IAFTRL

open Matrix

/-- **An orthonormal basis matrix of `b^⊥`.** Zhao–Tan, *Best-of-Both-Worlds FTRL for Linear Bandits*, arXiv:2611.01299, Definition C.1, p.56: "For each nonzero
action `b`, set `u_b = b/‖b‖` and let `U_b` be an orthonormal basis matrix of `u_b^⊥`."

`perpBasis b` is a `d × (d − 1)` real matrix `U` with orthonormal columns (`U^⊤U = I_{d−1}`) all
orthogonal to `b` (`U^⊤b = 0`). For `b ≠ 0` such matrices exist, and their `d − 1` columns form an
orthonormal basis of `b^⊥`.

**Formalization Note.** One such matrix is chosen with `Classical.epsilon`. Lemma C.1 (p.57) shows
that the constant `G_𝒜` built from it does not depend on the choice. For `b = 0` the value is
unspecified and never used. -/
noncomputable def perpBasis {d : ℕ} (b : Fin d → ℝ) : Matrix (Fin d) (Fin (d - 1)) ℝ :=
  Classical.epsilon fun U : Matrix (Fin d) (Fin (d - 1)) ℝ => Uᵀ * U = 1 ∧ Uᵀ *ᵥ b = 0

end IAFTRL


