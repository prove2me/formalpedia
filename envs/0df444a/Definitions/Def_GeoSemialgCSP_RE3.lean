-- Prove2me | Definitions.Def_GeoSemialgCSP_RE3
-- name    : GeoSemialgCSP_RE3
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:49:19.519124+00:00
-- url     : https://prove2.me/theorems/aac23df0-2829-4b83-a1f4-368d751720af
-- title:
--   Item 3 of Lemma 4.2: cousins are preserved
-- statement:
--   A random map $L:[m]\to[M]$ **preserves cousins up to error** $\varepsilon_L$ if for every cousins tuple $(a_1,\dots,a_k)$ of $T_m$,
--   $$\Pr\bigl(\mathrm{cousins}(L(a_1),\dots,L(a_k))=1\text{ in }T_M\bigr)\ \ge\ 1-\varepsilon_L .$$
-- source:
--   Arvanitakis, Chatziafratis, Makarychev, Hardness of Approximation for Semialgebraic CSPs, manuscript (STOC 2027 submission, held version sha256 ee702c42…), Lemma 4.2, pp.10–11 (PDF pp.11–12)

import Mathlib
import Definitions.Def_GeoSemialgCSP_Wd
import Definitions.Def_GeoSemialgCSP_cousinsW

namespace GeoSemialgCSP

/-- **Item 3 of Lemma 4.2.** Arvanitakis, Chatziafratis, Makarychev, *Hardness of Approximation for Semialgebraic CSPs*,
manuscript (STOC 2027 submission, held version sha256 ee702c42…), Lemma 4.2, printed pp.10–11 (PDF pp.11–12): if
`a₁, …, a_k` are cousins in `T_m`, then
`Pr(cousins(L_{m,M}(a₁), …, L_{m,M}(a_k)) = 1 in T_M) ≥ 1 − ε_L`. -/
def RE3 {k h H : ℕ} (L : PMF ((Fin h → Fin k) → Wd k H)) (εL : ℝ) : Prop :=
  ∀ l : Fin k → (Fin h → Fin k), cousinsW l →
    ENNReal.ofReal (1 - εL) ≤ L.toOuterMeasure {g | cousinsW (g ∘ l)}

end GeoSemialgCSP


