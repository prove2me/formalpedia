-- Prove2me | Definitions.Def_Max3CutHard_Gadget_scale
-- name    : Max3CutHard_Gadget_scale
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:45:28.737349+00:00
-- url     : https://prove2.me/theorems/0d1e1763-813d-475b-b6bb-5dd2bff20725
-- title:
--   A gadget with all weights multiplied by $c$
-- statement:
--   For a real $c$ and a gadget $I$, the gadget $cI$ has the same vertices and every edge weight multiplied by $c$. The family of Theorem 1.1 uses $2E$, the E-gadget with all weights doubled.
-- source:
--   Ni, Improved NP-Hardness of Approximation for Max-3-Cut and for Max-k-Cut with Small k, arXiv:2611.01402, Proof of Theorem 1.1, p.6

import Mathlib
import Definitions.Def_Max3CutHard_Gadget

namespace Max3CutHard

/-- **A gadget with all weights multiplied by `c`.** Ni, *Improved NP-Hardness of Approximation for Max-3-Cut and for Max-k-Cut with Small k*, arXiv:2611.01402, Proof of Theorem 1.1, p.6: "`2E`,
i.e. `E` with all weights doubled". -/
noncomputable def Gadget.scale {k : ℕ} (c : ℝ) (I : Gadget k) : Gadget k :=
  ⟨I.aux, I.edges.map fun e => (e.1, c * e.2)⟩

end Max3CutHard


