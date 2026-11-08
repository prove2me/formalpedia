-- Prove2me | Definitions.Def_TightClock_firstBest
-- name    : TightClock_firstBest
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T04:38:22.57561+00:00
-- url     : https://prove2.me/theorems/6206f939-d640-4839-b4f7-748c1a60c554
-- title:
--   First-best welfare $f(v)$, (3.1)
-- statement:
--   For a valuation profile $v$ and a family $\mathcal F$ of feasible sets, the **first-best welfare** is
--
--   $$f(v)=\max_{S\in\mathcal F}v(S),\qquad v(S)=\sum_{i\in S}v_i .$$
--
--   It is the benchmark inside $\mathrm{FB}$.
--
--   **Formalization Note** The maximum over an empty family is set to $0$. This case never arises, since every use has $\mathcal F$ downward closed and therefore nonempty.
-- source:
--   Afshinmehr, Ascher, Ashuri, Gkatzelis, Mahmoudkhan, Rubinstein, Schoepflin, Tight Approximation Bounds for Clock Auctions, manuscript (STOC 2027 submission; held artifact sha256 29bccd9c…b31b, preprint basis), §3, p.13 (PDF p.16), eq. (3.1)

import Mathlib

set_option autoImplicit false

namespace TightClock

/-- The first-best welfare `f(v) = max_{S ∈ F} v(S)`, display (3.1). Afshinmehr et al., manuscript
(STOC 2027 submission), §3, p.13 (PDF 16).

**Formalization Note** The maximum over the empty family is set to `0`. It never arises: every use has
`F` downward closed, hence nonempty. -/
noncomputable def firstBest {n : ℕ} (F : Finset (Finset (Fin n))) (v : Fin n → ℝ) : ℝ :=
  if h : F.Nonempty then F.sup' h (fun S => ∑ i ∈ S, v i) else 0

end TightClock


