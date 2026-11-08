-- Prove2me | Definitions.Def_EuclidDiamStream_hardDim
-- name    : EuclidDiamStream_hardDim
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T07:55:28.791957+00:00
-- url     : https://prove2.me/theorems/36cdb953-0597-4aab-99db-f28cbee55b59
-- title:
--   The hard dimension $d(n,c)$, radius $\tau$ and scale $r$
-- statement:
--   For $n\in\mathbb N$ and $c>1$, $d=d(n,c)$ is the largest positive integer with
--   $$1+\sum_{j=0}^{\lfloor d/(12c^2)\rfloor}\binom dj\le n.$$
--   It comes with the radius $\tau=\lfloor d/(12c^2)\rfloor$ and the scale $r=\sqrt d/(c\sqrt3)$.
--
--   The choice of $d$ guarantees that a Hamming ball of radius $\tau$ together with one more point has at most $n$ points. The scale separates pairs within such a ball from typical pairs of hypercube points.
--
--   **Formalization Note** For $n\ge2$ and $c>1$ the defining set is nonempty and bounded, which is checked in the mission's verification file; for $n\le1$ the value is $0$ and no theorem uses it. Definition 3.1 prints $r=2\sqrt\tau=\sqrt d/(c\sqrt3)$. These agree only when $12c^2$ divides $d$, and $2\sqrt\tau$ vanishes at $\tau=0$, so the value fixed by Lemma 3.9 is used.
-- source:
--   Padaki, Singal, Waingarten, A Near-Optimal Space Lower Bound for Euclidean Diameter Estimation in Dynamic Streams, arXiv:2609.19089 (held version of Nov 3, 2026, sha256 3fd06a3f…), p.7, Def. 3.1; p.13, Lemma 3.9

import Mathlib

namespace EuclidDiamStream

/-- The dimension `d = d(n,c)` of Definition 3.1 of Padaki, Singal, Waingarten, *A Near-Optimal Space Lower Bound for Euclidean Diameter Estimation in Dynamic Streams*, arXiv:2609.19089 (held version of Nov 3, 2026, sha256 3fd06a3f…), p.7: the largest positive integer `d` with
`1 + ∑_{j=0}^{d/(12c²)} (d choose j) ≤ n`, where the sum runs over integers `j ≤ d/(12c²)`.

**Formalization Note.** For `n ≥ 2` and `c > 1` the defining set is nonempty and bounded (checked in the
mission's verification file), so the natural-number `sSup` is its maximum. For `n ≤ 1` the set is empty and
the value is `0`; no theorem of the mission uses that case. -/
noncomputable def hardDim (n : ℕ) (c : ℝ) : ℕ :=
  sSup {d : ℕ | 0 < d ∧ 1 + ∑ j ∈ Finset.range (⌊(d : ℝ) / (12 * c ^ 2)⌋₊ + 1), d.choose j ≤ n}

/-- The radius `τ = ⌊d/(12c²)⌋` of Definition 3.1, p.7. -/
noncomputable def hardTau (n : ℕ) (c : ℝ) : ℕ :=
  ⌊(hardDim n c : ℝ) / (12 * c ^ 2)⌋₊

/-- The scale `r = √d/(c√3)`, fixed by Lemma 3.9, p.13.

**Formalization Note.** Definition 3.1, p.7, prints `r = 2√τ = √d/(c√3)`, which is an equality only when
`12c²` divides `d`; `2√τ = 0` when `τ = 0`, which would violate `r > 0`. Both values separate the two cases
of the hard distribution, and the value here is the one Lemma 3.9 states. -/
noncomputable def hardScale (n : ℕ) (c : ℝ) : ℝ :=
  Real.sqrt (hardDim n c) / (c * Real.sqrt 3)

end EuclidDiamStream


