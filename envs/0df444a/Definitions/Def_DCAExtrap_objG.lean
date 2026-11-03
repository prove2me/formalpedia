-- Prove2me | Definitions.Def_DCAExtrap_objG
-- name    : DCAExtrap_objG
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:22:30.457436+00:00
-- url     : https://prove2.me/theorems/cb4534f1-2e96-49ac-9547-a14d823d1d9b
-- title:
--   First DC component $G = L\varphi + g$
-- statement:
--   For $\varphi:E\to\mathbb R$, $g:E\to(-\infty,+\infty]$ and $L>0$, the first DC component of (1) is
--
--   $$
--   G(x) := L\varphi(x) + g(x).
--   $$
--
--   DCAe computes $x^{k+1}$ by minimizing $G$ minus a linear function, see (9).
--
--   **Formalization Note** $G$ is `EReal`-valued.
-- source:
--   Phan, Le Thi, DCA based algorithm with extrapolation for nonconvex nonsmooth optimization, arXiv:2106.04743v1, (4), p.2, G(x) = Lφ(x) + g(x)

import Mathlib

namespace DCAExtrap

/-- **First DC component** (Phan–Le Thi, arXiv:2106.04743v1, (4), p.2): `G(x) := Lφ(x) + g(x)`.

**Formalization Note.** `φ : E → ℝ` is real-valued and `g : E → EReal` may be `+∞`, so `G` is
`EReal`-valued. -/
noncomputable def objG {E : Type*} (φ : E → ℝ) (g : E → EReal) (L : ℝ) (x : E) : EReal :=
  ((L * φ x : ℝ) : EReal) + g x

end DCAExtrap


