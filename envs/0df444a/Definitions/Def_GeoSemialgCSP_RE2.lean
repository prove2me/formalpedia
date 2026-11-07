-- Prove2me | Definitions.Def_GeoSemialgCSP_RE2
-- name    : GeoSemialgCSP_RE2
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:48:17.847219+00:00
-- url     : https://prove2.me/theorems/1eddaae8-330f-4483-a235-4a05be8e0763
-- title:
--   Item 2 of Lemma 4.2: uniform marginals
-- statement:
--   A random map $L:[m]\to[M]$, $M=k^H$, has **uniform marginals** if for every leaf $a\in[m]$ and every $b\in[M]$,
--   $$\Pr\bigl(L(a)=b\bigr)=\frac1M .$$
-- source:
--   Arvanitakis, Chatziafratis, Makarychev, Hardness of Approximation for Semialgebraic CSPs, manuscript (STOC 2027 submission, held version sha256 ee702c42…), Lemma 4.2, p.10 (PDF p.11)

import Mathlib
import Definitions.Def_GeoSemialgCSP_Wd

namespace GeoSemialgCSP

/-- **Item 2 of Lemma 4.2.** Arvanitakis, Chatziafratis, Makarychev, *Hardness of Approximation for Semialgebraic CSPs*,
manuscript (STOC 2027 submission, held version sha256 ee702c42…), Lemma 4.2, printed p.10 (PDF p.11): for every
`a ∈ [m]`, `L_{m,M}(a)` is uniform on `[M]`, `M = k^H`. -/
def RE2 {k h H : ℕ} (L : PMF ((Fin h → Fin k) → Wd k H)) : Prop :=
  ∀ (a : Fin h → Fin k) (b : Wd k H), L.toOuterMeasure {g | g a = b} = ((k : ENNReal) ^ H)⁻¹

end GeoSemialgCSP


