-- Prove2me | Definitions.Def_CombOpt_TutteBerge_Multigraph_tutteBergeBound
-- name    : CombOpt_TutteBerge_Multigraph_tutteBergeBound
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:06:45.237076+00:00
-- url     : https://prove2.me/theorems/75b1397e-ffea-4ce8-9b9d-146d8e265aae
-- title:
--   The Tutte–Berge bound of a node set
-- statement:
--   For $A\subseteq V$, this is the rational number
--   $$
--   \tfrac12\bigl(|V|-\mathrm{oc}(G\setminus A)+|A|\bigr).
--   $$
--   **Formalization Note** The value lies in $\mathbb Q$ with every cardinal cast first, so neither the subtraction nor the division truncates.
-- source:
--   Cook, Cunningham, Pulleyblank & Schrijver, Combinatorial Optimization (Wiley, 1998), §5.1, (5.1), p. 130 (PDF p. 138)

import Mathlib
import Definitions.Def_CombOpt_TutteBerge_Multigraph
import Definitions.Def_CombOpt_TutteBerge_Multigraph_deleteNodes
import Definitions.Def_CombOpt_TutteBerge_Multigraph_oddComponentCount

namespace CombOpt.TutteBerge

/-- **The Tutte–Berge bound of a node set.**
Cook, Cunningham, Pulleyblank & Schrijver, *Combinatorial Optimization* (Wiley, 1998), §5.1, (5.1), p. 130 (PDF p. 138): the quantity ½(|V| − oc(G\A) + |A|).

**Formalization Note.** The value lies in `ℚ` and every cardinal is cast before the arithmetic, so
neither the subtraction nor the halving truncates; the value may be a half-integer. With
`[Finite V]`, as in every theorem here, `Nat.card V` and `A.ncard` are the true cardinalities. -/
noncomputable def Multigraph.tutteBergeBound {V E : Type*} (G : Multigraph V E) (A : Set V) : ℚ :=
  (1 / 2 : ℚ) *
    ((Nat.card V : ℚ) - ((G.deleteNodes A).oddComponentCount : ℚ) + (A.ncard : ℚ))

end CombOpt.TutteBerge


