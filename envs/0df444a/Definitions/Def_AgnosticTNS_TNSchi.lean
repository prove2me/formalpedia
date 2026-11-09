-- Prove2me | Definitions.Def_AgnosticTNS_TNSchi
-- name    : AgnosticTNS_TNSchi
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T16:35:20.342488+00:00
-- url     : https://prove2.me/theorems/97dec78f-bcef-47c9-a5d6-6c2051c2f3ae
-- title:
--   Tensor network state class $S_d(G,\chi)$
-- statement:
--   For a graph $G=([n],E)$ and $\chi\in\mathbb N$,
--   $$
--   S_d(G,\chi):=\bigcup_{w:E\to[\chi]} S_d(G,w),\qquad [\chi]=\{1,\dots,\chi\}.
--   $$
--   For an edgeless graph the union contains only the empty weight function and the class consists of the pure product states. For a path this is the class of open-boundary MPSs, for a tree the class of TTNs, of bond dimension at most $\chi$.
-- source:
--   Caro–McHugh–Strelchuk, Efficient Agnostic Learning of Tensor Network States, STOC 2027 submission (manuscript sha256 d69077bb…abec0), Definition 2.1, Eq. (2.3), p.12

import Mathlib
import Definitions.Def_AgnosticTNS_TNS

namespace AgnosticTNS

/-- **The class `S_d(G, χ)`**, Definition 2.1, Eq. (2.3), p.12 (Caro–McHugh–Strelchuk, *Efficient Agnostic Learning of Tensor Network States*, STOC 2027 submission manuscript (sha256 d69077bb…abec0)):
`S_d(G, χ) := ⋃_{w : E → [χ]} S_d(G, w)` with `[χ] = {1, …, χ}`. For an edgeless graph the union
contains only the empty weight function and the class is the set of pure product states.

**Formalization Note** `w` ranges over all functions `G.edgeSet → ℕ` with `1 ≤ w e ≤ χ` for every
edge, i.e. over `E → [χ]`. -/
def TNSchi {n : ℕ} (d : ℕ) (G : SimpleGraph (Fin n)) (χ : ℕ) : Set ((Fin n → Fin d) → ℂ) :=
  ⋃ (w : G.edgeSet → ℕ) (_ : ∀ e, 1 ≤ w e ∧ w e ≤ χ), TNS d G w

end AgnosticTNS


