-- Prove2me | Definitions.Def_SeymourMFMC_Binary_IsCircuit
-- name    : SeymourMFMC_Binary_IsCircuit
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-29T02:20:10.421801+00:00
-- url     : https://prove2.me/theorems/f9b35a9e-116f-4c4c-8ca5-006c8ad79c5d
-- title:
--   Circuit of a binary clutter: a minimal nonempty cycle
-- statement:
--   A **circuit** of the binary clutter $\mathbf L$ is a nonempty set $C \subseteq E(\mathbf L)$ such that $|C \cap B|$ is even for every $B \in b(\mathbf L)$, and no nonempty proper subset of $C$ has this property.
--
--   The paper defines the circuits of $\mathbf L = \Omega(M)$, for $M$ a connected binary matroid, as the circuits of $M$ not containing $\Omega$. Circuits describe the linear dependencies among the elements and drive the structure theory of Section 4.
--
--   **Formalization Note** The definition here is intrinsic. By (3.6)(ii) and (3.6)(iii)(a), p. 202, the circuits of $M$ avoiding $\Omega$ are exactly the minimal nonempty sets described above, so (3.6)(ii) holds by definition.
-- source:
--   Seymour, The Matroids with the Max-Flow Min-Cut Property, J. Combin. Theory Ser. B 23 (1977), p. 201, Section 3 (circuits of L), with (3.6)(ii),(iii)(a), p. 202

import Mathlib
import Definitions.Def_SeymourMFMC_Binary_IsCycle

namespace SeymourMFMC.Binary

/-- `IsCircuit L C`: `C` is a **circuit of the binary clutter** `L` (Seymour 1977, p. 201): a
minimal nonempty subset of `E(L)` having even intersection with every member of `b(L)`. The
paper defines the circuits of `L = Ω(M)` (`M` a connected binary matroid) as the circuits of `M`
not containing `Ω`; by (3.6)(ii) and (3.6)(iii)(a) these are exactly the minimal nonempty sets
`C ⊆ E(L)` with `|C ∩ B|` even for all `B ∈ b(L)`, which is the intrinsic definition used here. -/
def IsCircuit {α : Type*} [DecidableEq α] (L : Finset (Finset α)) (C : Finset α) : Prop :=
  C.Nonempty ∧ IsCycle L C ∧ ∀ C' ∈ C.ssubsets, C'.Nonempty → ¬ IsCycle L C'

instance {α : Type*} [DecidableEq α] (L : Finset (Finset α)) (C : Finset α) :
    Decidable (IsCircuit L C) := by
  unfold IsCircuit; infer_instance

end SeymourMFMC.Binary


