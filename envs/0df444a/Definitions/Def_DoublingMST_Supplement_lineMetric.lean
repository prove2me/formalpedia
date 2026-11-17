-- Prove2me | Definitions.Def_DoublingMST_Supplement_lineMetric
-- name    : DoublingMST_Supplement_lineMetric
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T06:16:23.414029+00:00
-- url     : https://prove2.me/theorems/30c2167e-df12-4061-af84-6c43c66ae070
-- title:
--   Labelled points on the real line: $d(u,v)=|x_u-x_v|$
-- statement:
--   For positions $x:\{0,\dots,n-1\}\to\mathbb R$, the **line metric** of the labelled points is
--
--   $$d_x(u,v)=|x_u-x_v|.$$
--
--   When $x$ is injective this is a labelled set of $n$ points on the real line, the inputs of the comparison lower bound (Theorem 6.3); the relabeled path metrics $d_\pi(u,v)=|\pi(u)-\pi(v)|$ of §6.2.2 are the case $x=\pi$.
--
--   **Formalization Note** Labels are the points of `Fin n`; injectivity is a hypothesis of the theorems, not part of the definition.
-- source:
--   Höckendorff–Hommelsheim–Sohler–Yue, Tight Bounds for (1+ϵ)-Approximation for Minimum Spanning Trees in Doubling Metrics, STOC 2027 submission (manuscript sha256 4855d6b3…be759), Theorem 6.3, p.31 (PDF p.33); §6.2.2, p.33 (PDF p.35)

import Mathlib

namespace DoublingMST.Supplement

/-- **Labelled points on the real line.**
Höckendorff–Hommelsheim–Sohler–Yue, *Tight Bounds for (1+ϵ)-Approximation for Minimum Spanning
Trees in Doubling Metrics*, STOC 2027 submission (manuscript sha256 4855d6b3…be759), Theorem 6.3,
p.31 (PDF p.33): "every labeled set of n points on the real line"; §6.2.2, p.33: "dπ(u, v) =
|π(u) − π(v)|".

`lineMetric x u v = |x u − x v|`: point `u : Fin n` sits at position `x u ∈ ℝ`.

**Formalization Note.** The labels are the points of `Fin n`; a labelled set of `n` points is an
injective `x : Fin n → ℝ`, which the theorems assume. -/
def lineMetric {n : ℕ} (x : Fin n → ℝ) : Fin n → Fin n → ℝ :=
  fun u v => |x u - x v|

end DoublingMST.Supplement


