-- Prove2me | Definitions.Def_PrivLittlestone_selDesc
-- name    : PrivLittlestone_selDesc
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T03:35:33.764167+00:00
-- url     : https://prove2.me/theorems/41517719-01c7-4561-9288-e6c6a9d41525
-- title:
--   Descending-rank selection $D_{\ge s}(V)$
-- statement:
--   For a version space $V$, process $s = d, d-1, \dots, 0$ and select
--   $$
--   T_s(V) = \Big\{ h \in V : \rho(h) = s,\ h \notin \bigcup_{g \in D_{>s}(V)} W_g \Big\},\qquad D_{>s}(V) = \bigcup_{t=s+1}^{d} T_t(V).
--   $$
--   This definition is the cumulative union $D_{\ge d-k}(V) = \bigcup_{t=d-k}^{d} T_t(V)$, built by adding one layer at a time.
-- source:
--   He–He, Private Online Learning of Littlestone Classes and Matroid Flats, STOC 2027 submission (manuscript sha256 21480556…c562), (20), p.18

import Mathlib
import Definitions.Def_PrivLittlestone_rankOf
import Definitions.Def_PrivLittlestone_witnessSpace

namespace PrivLittlestone

/-- **Descending-rank selection**, cumulative form (He–He, *Private Online Learning of Littlestone
Classes and Matroid Flats*, STOC 2027 submission manuscript (sha256 21480556…c562), (20),
p.18): `selDesc V k = D_{≥ d−k}(V) = ⋃_{t = d−k}^{d} T_t(V)`, where, processing `s = d, d − 1, …, 0`,
`T_s(V) = {h ∈ V : ρ(h) = s, h ∉ ⋃_{g ∈ D_{>s}(V)} W_g}`. So `selDesc V 0 = T_d(V)` (as `D_{>d}(V) = ∅`)
and `selDesc V (k + 1) = selDesc V k ∪ T_{d−k−1}(V)` for `k + 1 ≤ d`.

**Formalization Note** For `k ≥ d` the set is constant (`= D(V)`). -/
def selDesc {X : Type*} (H : Set (X → Bool)) (d : ℕ) (Aw : (X → Bool) → Finset X)
    (V : Set (X → Bool)) : ℕ → Set (X → Bool)
  | 0 => {h ∈ V | rankOf H d h = d}
  | k + 1 =>
    if k + 1 ≤ d then
      selDesc H d Aw V k ∪
        {h ∈ V | rankOf H d h = d - (k + 1) ∧ ∀ g ∈ selDesc H d Aw V k, h ∉ witnessSpace H d Aw g}
    else selDesc H d Aw V k

end PrivLittlestone


