-- Prove2me | Definitions.Def_MetricMinTest_IsRCover
-- name    : MetricMinTest_IsRCover
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T03:04:53.331173+00:00
-- url     : https://prove2.me/theorems/d2c62487-0984-4737-9918-76c9c00ae6fe
-- title:
--   $r$-cover $Z$ (Definition 7.1)
-- statement:
--   For $r\in[0,\gamma)$ and a nonempty set $Z$ of indices, the screening region is $S(Z,r)=\bigcup_{z\in Z}B(z,r)$. The pair is an **$r$-cover** if $S(Z,r)$ is the whole index set: every index lies within distance $r$ of some $z\in Z$.
--
--   **Formalization Note** The range of $r$ is a hypothesis of the results that use the predicate.
-- source:
--   Chen–Fang, Minimum-Mean Testing under Metric Constraints: Shared Information, Certificates, and Adaptivity, STOC 2027 submission (manuscript sha256 dcece1939edb1fcf752ab6152794f04d8762928ada557c99626997db01ad32bb), Definition 7.1, p.15

import Mathlib

namespace MetricMinTest

/-- **`r`-cover** (Definition 7.1). Chen–Fang, *Minimum-Mean Testing under Metric Constraints*,
STOC 2027 submission (manuscript sha256 dcece193…ad32bb), Definition 7.1, p.15: for a nonempty
`Z ⊆ [k]` the screening region is `S(Z, r) = ⋃_{z ∈ Z} B(z, r)`, and the pair is an `r`-cover if
`S(Z, r) = [k]`.

**Formalization Note.** The range `r ∈ [0, γ)` of Definition 7.1 is a hypothesis of each result
that uses the predicate. -/
def IsRCover {ι : Type} (d : ι → ι → ℝ) (Z : Finset ι) (r : ℝ) : Prop :=
  Z.Nonempty ∧ ∀ i, ∃ z ∈ Z, d i z ≤ r

end MetricMinTest


