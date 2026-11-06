-- Prove2me | Definitions.Def_UCalibDirichlet_fRestr
-- name    : UCalibDirichlet_fRestr
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:24:07.58717+00:00
-- url     : https://prove2.me/theorems/19899802-c27f-4405-9da4-3dbd701773ce
-- title:
--   One-dimensional restriction $f_{i,r}(x)=F(xe_i+(1-x)r)$
-- statement:
--   For $i\in[K]$ and $r\in\Delta_K$ with $r_i=0$, the function $f_{i,r}:[0,1]\to\mathbb R$ is
--   $$f_{i,r}(x)=F\big(xe_i+(1-x)r\big),$$
--   the restriction of $F$ to the segment from $r$ (at $x=0$) to the vertex $e_i$ (at $x=1$). It tracks the effect of label $i$ alone with the direction of the other labels fixed, and its derivative enters the curvature $W^i_F$.
--
--   **Formalization Note** Defined for all real $x$ and all vectors $r$; the paper only uses $x\in[0,1]$ and $r$ on the face $r_i=0$ of the simplex, where the argument lies in $\Delta_K$.
-- source:
--   Frongillo, Luo, Mehta & Schneider, Near-Optimal Regret in U-Calibration for Every Proper Loss (manuscript, STOC 2027 submission), display (10), p.4

import Mathlib

namespace UCalibDirichlet

/-- **The one-dimensional restriction `f_{i,r}`, display (10).** Frongillo, Luo, Mehta & Schneider
(manuscript, STOC 2027 submission), p.4: "for any `i ∈ [K]` and `r ∈ Δ_K` such that `r_i = 0`,
define `f_{i,r} : [0, 1] → ℝ` as `f_{i,r}(x) = F(x e_i + (1 − x) r)`. (10)"

`fRestr F i r x = F(x e_i + (1 − x) r)`, with `e_i = Pi.single i 1`.

**Formalization Note.** Defined for every real `x` and every vector `r`; the paper uses it for
`r ∈ Δ_K` with `r_i = 0` and `x ∈ [0, 1]`, where `x e_i + (1 − x) r ∈ Δ_K`. Its derivative
`f′_{i,r}` at a point `x ∈ (0, 1)` only involves values of `F` on the simplex. -/
def fRestr {K : ℕ} (F : (Fin K → ℝ) → ℝ) (i : Fin K) (r : Fin K → ℝ) (x : ℝ) : ℝ :=
  F (x • Pi.single i 1 + (1 - x) • r)

end UCalibDirichlet


