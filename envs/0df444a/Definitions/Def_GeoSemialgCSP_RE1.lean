-- Prove2me | Definitions.Def_GeoSemialgCSP_RE1
-- name    : GeoSemialgCSP_RE1
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:47:44.78221+00:00
-- url     : https://prove2.me/theorems/8d5771aa-f8c7-4440-95de-0d6129fec698
-- title:
--   Item 1 of Lemma 4.2: injective realizations
-- statement:
--   A finitely supported random map $L:[m]\to[M]$ from the leaves of $T_m$ to the leaves of $T_M$ has **injective realizations** if every map in its support is injective.
-- source:
--   Arvanitakis, Chatziafratis, Makarychev, Hardness of Approximation for Semialgebraic CSPs, manuscript (STOC 2027 submission, held version sha256 ee702c42…), Lemma 4.2, p.10 (PDF p.11)

import Mathlib
import Definitions.Def_GeoSemialgCSP_Wd

namespace GeoSemialgCSP

/-- **Item 1 of Lemma 4.2.** Arvanitakis, Chatziafratis, Makarychev, *Hardness of Approximation for Semialgebraic CSPs*,
manuscript (STOC 2027 submission, held version sha256 ee702c42…), Lemma 4.2, printed p.10 (PDF p.11): every realization of
the random map `L_{m,M} : [m] → [M]` is injective.

**Formalization Note.** The finitely supported random map is a `PMF` on the finite type of maps
from the leaves of `T_m` to the leaves of `T_M`. -/
def RE1 {k h H : ℕ} (L : PMF ((Fin h → Fin k) → Wd k H)) : Prop :=
  ∀ g ∈ L.support, Function.Injective g

end GeoSemialgCSP


