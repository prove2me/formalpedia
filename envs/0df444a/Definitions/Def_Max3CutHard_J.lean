-- Prove2me | Definitions.Def_Max3CutHard_J
-- name    : Max3CutHard_J
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:48:20.504409+00:00
-- url     : https://prove2.me/theorems/daf59126-71d9-440e-a79b-dbeeb0e1958e
-- title:
--   The reduction graph $J(\Phi)$
-- statement:
--   Given a role-separated instance $\Phi$ and a family $(I_0,I_1,I_2)$, the graph $J=J(\Phi)$ has a vertex for every variable of $\Phi$, $k$ global vertices, and for every equation $e$ a copy of $I_{t_e}$ with every weight multiplied by $\lambda_e$, whose primaries $p_1,p_2,p_3$ are identified with $u_e,w_e,w'_e$, whose global vertices are identified with the global vertices of $J$, and whose auxiliary vertices are new.
--
--   This is the gadget reduction from 3Lin($\mathbb Z_3$) to Max-$k$-Cut.
-- source:
--   Ni, Improved NP-Hardness of Approximation for Max-3-Cut and for Max-k-Cut with Small k, arXiv:2611.01402, Section 2, The reduction, p.5

import Mathlib
import Definitions.Def_Max3CutHard_JVert

namespace Max3CutHard

/-- **The reduction graph `J(Φ)`.** Ni, *Improved NP-Hardness of Approximation for Max-3-Cut and for Max-k-Cut with Small k*, arXiv:2611.01402, Section 2, The reduction, p.5: "Given a role-separated
`Φ` and a family, the graph `J = J(Φ)` (Fig. 2) has a vertex for every variable of `Φ`, `k` global
vertices, and for every equation `e` a copy of `I_{t_e}` scaled by `λ_e`, whose primaries
`p1, p2, p3` are identified with `u_e, w_e, w′_e`, whose global vertices are identified with the
global vertices of `J`, and whose auxiliary vertices are new."

**Formalization Note.** For the `i`-th listed equation `(e, λ)`, every edge `((a, b), c)` of
`I_{t_e}` contributes `((v a, v b), λ·c)`, where `v` sends `p1, p2, p3` to `u_e, w_e, w′_e`, the
global `g_j` to the shared global `j`, and the auxiliary vertex `a` to the new vertex `(i, a)`. -/
noncomputable def J {U W : Type} {k : ℕ} (Φ : WInst U W) (F : Family k) : RGraph (JVert Φ F) :=
  (List.finRange Φ.eqs.length).flatMap fun i =>
    (F (Φ.eqs.get i).1.t).edges.map fun e =>
      let v : Fin 3 ⊕ Fin k ⊕ Fin (F (Φ.eqs.get i).1.t).aux → JVert Φ F :=
        Sum.elim (fun j => ![Sum.inl (Φ.eqs.get i).1.u, Sum.inr (Sum.inl (Φ.eqs.get i).1.w),
            Sum.inr (Sum.inl (Φ.eqs.get i).1.w')] j)
          (Sum.elim (fun g => Sum.inr (Sum.inr (Sum.inl g))) fun a => Sum.inr (Sum.inr (Sum.inr ⟨i, a⟩)))
      ((v e.1.1, v e.1.2), (Φ.eqs.get i).2 * e.2)

end Max3CutHard


