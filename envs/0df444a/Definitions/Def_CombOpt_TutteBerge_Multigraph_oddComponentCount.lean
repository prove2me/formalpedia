-- Prove2me | Definitions.Def_CombOpt_TutteBerge_Multigraph_oddComponentCount
-- name    : CombOpt_TutteBerge_Multigraph_oddComponentCount
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:05:27.529018+00:00
-- url     : https://prove2.me/theorems/8ac16c86-2245-48ed-bb24-4858a52488a4
-- title:
--   $\mathrm{oc}(H)$: the number of odd components
-- statement:
--   For a graph $H$, $\mathrm{oc}(H)$ is the number of connected components of $H$ having an odd number of nodes.
--
--   **Formalization Note** Components are those of the underlying simple graph, as Mathlib's `ConnectedComponent`, and the odd ones are Mathlib's `oddComponents`.
-- source:
--   Cook, Cunningham, Pulleyblank & Schrijver, Combinatorial Optimization (Wiley, 1998), §5.1, p. 130 (PDF p. 138)

import Mathlib
import Definitions.Def_CombOpt_TutteBerge_Multigraph
import Definitions.Def_CombOpt_TutteBerge_Multigraph_toSimple

namespace CombOpt.TutteBerge

/-- **oc(H), the number of odd components.**
Cook, Cunningham, Pulleyblank & Schrijver, *Combinatorial Optimization* (Wiley, 1998), §5.1, p. 130 (PDF p. 138): "We denote by oc(H) the number of odd components of a graph H",
the odd components being the components "having an odd number of nodes".

**Formalization Note.** A component of `H` is a connected component of `H.toSimple` (Mathlib's
`SimpleGraph.ConnectedComponent`, a class of nodes, so it is never empty), and
`SimpleGraph.oddComponents` is the set of those with an odd number of nodes. With `[Finite V]`, as
in every theorem here, the `ncard`s are true cardinalities. -/
noncomputable def Multigraph.oddComponentCount {V E : Type*} (H : Multigraph V E) : ℕ :=
  H.toSimple.oddComponents.ncard

end CombOpt.TutteBerge


