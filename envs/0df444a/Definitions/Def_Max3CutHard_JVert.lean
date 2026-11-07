-- Prove2me | Definitions.Def_Max3CutHard_JVert
-- name    : Max3CutHard_JVert
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:47:02.851474+00:00
-- url     : https://prove2.me/theorems/dc3b2548-ea62-43dd-94b2-88c467dde1b9
-- title:
--   Vertices of the reduction graph $J(\Phi)$
-- statement:
--   The graph $J(\Phi)$ has a vertex for every variable of $\Phi$ (in $U$ and in $W$), $k$ global vertices, and, for every equation $e$ of $\Phi$, a new copy of the auxiliary vertices of the gadget $I_{t_e}$.
--
--   **Formalization Note** The equations are indexed by their position in the list of $\Phi$.
-- source:
--   Ni, Improved NP-Hardness of Approximation for Max-3-Cut and for Max-k-Cut with Small k, arXiv:2611.01402, Section 2, The reduction, p.5

import Mathlib
import Definitions.Def_Max3CutHard_WInst
import Definitions.Def_Max3CutHard_Family

namespace Max3CutHard

/-- **Vertices of the reduction graph `J(Φ)`.** Ni, *Improved NP-Hardness of Approximation for Max-3-Cut and for Max-k-Cut with Small k*, arXiv:2611.01402, Section 2, The reduction, p.5: "`J = J(Φ)`
has a vertex for every variable of `Φ`, `k` global vertices, and for every equation `e` a copy of
`I_{t_e}` … whose auxiliary vertices are new."

**Formalization Note.** `U ⊕ W ⊕ Fin k ⊕ Σ i, Fin (aux of I_{t_i})`, where `i` indexes the list of
equations of `Φ`. -/
abbrev JVert {U W : Type} {k : ℕ} (Φ : WInst U W) (F : Family k) : Type :=
  U ⊕ W ⊕ Fin k ⊕ (Σ i : Fin Φ.eqs.length, Fin (F (Φ.eqs.get i).1.t).aux)

end Max3CutHard


