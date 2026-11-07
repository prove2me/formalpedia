-- Prove2me | Definitions.Def_Max3CutHard_gadgetN
-- name    : Max3CutHard_gadgetN
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:46:22.404027+00:00
-- url     : https://prove2.me/theorems/a95b1e0a-3bc5-43d7-9d74-4f43546deb14
-- title:
--   The N-gadget
-- statement:
--   The N-gadget $N$ has $k=3$, a unit-weight triangle on $p_1,p_2,p_3$ and one auxiliary vertex $q$ joined to each of $p_1,p_2,p_3$ by an edge of weight $3$; its total weight is $12$. Its three global vertices carry no edges.
-- source:
--   Ni, Improved NP-Hardness of Approximation for Max-3-Cut and for Max-k-Cut with Small k, arXiv:2611.01402, Section 3, p.5

import Mathlib
import Definitions.Def_Max3CutHard_Gadget

namespace Max3CutHard

/-- **The N-gadget.** Ni, *Improved NP-Hardness of Approximation for Max-3-Cut and for Max-k-Cut with Small k*, arXiv:2611.01402, Section 3, p.5: "The N-gadget `N` (Fig. 4) consists of a unit-weight
triangle on `p1, p2, p3` and one auxiliary vertex `q` joined to `p1, p2, p3` by edges of weight 3
(total weight 12)."

**Formalization Note.** `k = 3`; primaries ↦ `0, 1, 2`, `q` ↦ auxiliary `0`; the globals are
isolated (Section 3). -/
noncomputable def gadgetN : Gadget 3 :=
  ⟨1,
    let p : Fin 3 → Fin 3 ⊕ Fin 3 ⊕ Fin 1 := fun j => Sum.inl j
    let q : Fin 3 ⊕ Fin 3 ⊕ Fin 1 := Sum.inr (Sum.inr 0)
    [((p 0, p 1), 1), ((p 0, p 2), 1), ((p 1, p 2), 1),
     ((q, p 0), 3), ((q, p 1), 3), ((q, p 2), 3)]⟩

end Max3CutHard


