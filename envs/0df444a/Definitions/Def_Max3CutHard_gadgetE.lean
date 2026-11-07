-- Prove2me | Definitions.Def_Max3CutHard_gadgetE
-- name    : Max3CutHard_gadgetE
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:45:56.93827+00:00
-- url     : https://prove2.me/theorems/1554e605-1355-497e-a4e9-cb680d035a20
-- title:
--   The E-gadget
-- statement:
--   The E-gadget $E$ (the type-0 gadget of Nagda–Raghavan–Thakurta, Lemma C.1) has $k=3$, auxiliary vertices $a_1,\dots,a_6$ and the 18 unit-weight edges
--
--   $$p_1a_1,p_1a_2,p_1a_3,p_1a_4,\ p_2a_3,p_2a_4,p_2a_5,p_2a_6,\ p_3a_1,p_3a_2,p_3a_5,p_3a_6,\ a_1a_6,a_1a_4,a_2a_3,a_2a_5,a_3a_6,a_4a_5.$$
--
--   Its three global vertices carry no edges.
--
--   **Formalization Note** $p_1,p_2,p_3$ are indexed $0,1,2$ and $a_1,\dots,a_6$ are indexed $0,\dots,5$.
-- source:
--   Ni, Improved NP-Hardness of Approximation for Max-3-Cut and for Max-k-Cut with Small k, arXiv:2611.01402, Section 3, p.5

import Mathlib
import Definitions.Def_Max3CutHard_Gadget

namespace Max3CutHard

/-- **The E-gadget.** Ni, *Improved NP-Hardness of Approximation for Max-3-Cut and for Max-k-Cut with Small k*, arXiv:2611.01402, Section 3, p.5: "The E-gadget `E` (Fig. 4(a)) is the type-0 gadget of
[NRT25, Lemma C.1]: auxiliary vertices `a1, …, a6` and the 18 unit-weight edges `p1a1, p1a2, p1a3,
p1a4, p2a3, p2a4, p2a5, p2a6, p3a1, p3a2, p3a5, p3a6, a1a6, a1a4, a2a3, a2a5, a3a6, a4a5`."

**Formalization Note.** `k = 3`; primaries `p1, p2, p3` ↦ `0, 1, 2`, auxiliaries `a1, …, a6` ↦
`0, …, 5`. Section 3: "the gadgets do not use their global vertices at all", so the three globals
are isolated. -/
noncomputable def gadgetE : Gadget 3 :=
  ⟨6,
    let p : Fin 3 → Fin 3 ⊕ Fin 3 ⊕ Fin 6 := fun j => Sum.inl j
    let a : Fin 6 → Fin 3 ⊕ Fin 3 ⊕ Fin 6 := fun j => Sum.inr (Sum.inr j)
    [((p 0, a 0), 1), ((p 0, a 1), 1), ((p 0, a 2), 1), ((p 0, a 3), 1),
     ((p 1, a 2), 1), ((p 1, a 3), 1), ((p 1, a 4), 1), ((p 1, a 5), 1),
     ((p 2, a 0), 1), ((p 2, a 1), 1), ((p 2, a 4), 1), ((p 2, a 5), 1),
     ((a 0, a 5), 1), ((a 0, a 3), 1), ((a 1, a 2), 1), ((a 1, a 4), 1),
     ((a 2, a 5), 1), ((a 3, a 4), 1)]⟩

end Max3CutHard


