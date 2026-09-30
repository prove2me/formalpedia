-- Prove2me | Definitions.Def_SeymourMFMC_Binary_point
-- name    : SeymourMFMC_Binary_point
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-29T02:31:31.232616+00:00
-- url     : https://prove2.me/theorems/5db00d4b-7d1e-470a-95f9-a49be3e67622
-- title:
--   ⟨x⟩: the point (parallel class) of x in a binary clutter
-- statement:
--   Two elements $x, y$ of a binary clutter $\mathbf L$ are **parallel** if $\{x, y\}$ is a circuit of $\mathbf L$. The **point** $\langle x \rangle$ containing $x$ is its parallel class:
--
--   $$
--   \langle x \rangle = \{x\} \cup \{ y \in E(\mathbf L) : \{x, y\} \text{ is a circuit of } \mathbf L \}.
--   $$
--
--   Points are used in the definition of $x \to y$ and in the counting functions $n(\mathbf L)$, $m(\mathbf L)$ of the paper's minimal counterexample.
--
--   **Formalization Note** The page writes "equivalence classes of elements of $E(G)$"; $E(G)$ is a misprint for $E(\mathbf L)$.
-- source:
--   Seymour, The Matroids with the Max-Flow Min-Cut Property, J. Combin. Theory Ser. B 23 (1977), p. 201, Section 3

import Mathlib
import Definitions.Def_SeymourMFMC_Binary_ground
import Definitions.Def_SeymourMFMC_Binary_IsCircuit

namespace SeymourMFMC.Binary

/-- `point L x` is the **point** `⟨x⟩` of `L` containing `x` (Seymour 1977, p. 201): `x` together
with every `y ∈ E(L)` parallel to `x`, where `x` and `y` are parallel if `{x, y}` is a circuit
of `L`. -/
def point {α : Type*} [DecidableEq α] (L : Finset (Finset α)) (x : α) : Finset α :=
  insert x ((ground L).filter (fun y => IsCircuit L {x, y}))

end SeymourMFMC.Binary


