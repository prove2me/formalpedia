-- Prove2me | Definitions.Def_BlockSSM_IrrepDegreesLE
-- name    : BlockSSM_IrrepDegreesLE
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:19:24.431511+00:00
-- url     : https://prove2.me/theorems/110ebe6f-b75a-4720-9641-f3c8fd53e4d9
-- title:
--   All irreducible degrees of a representation are at most $b$
-- statement:
--   A complex representation $V$ of a group $H$ has **all irreducible degrees at most $b$** if every irreducible subrepresentation of $V$ has dimension at most $b$. This is the side condition in the minimum defining $D_b(G)$.
--
--   **Formalization Note** For a finite group and a finite-dimensional $V$, Maschke's theorem writes $V$ as a direct sum of irreducible subrepresentations, and every irreducible constituent is isomorphic to one of them, so this is the source's condition.
-- source:
--   C. Geng, The State Complexity of Block-Diagonal State Space Models, STOC 2027 submission manuscript (sha256 f9071794…), Definition 2, p.2 (PDF p.3)

import Mathlib

namespace BlockSSM

/-- **All irreducible degrees are at most `b`.** Geng, *The State Complexity of Block-Diagonal State Space Models*, STOC 2027 submission manuscript (sha256 f9071794…), Definition 2, p.2 (PDF p.3): the side
condition "all irreducible degrees in V ≤ b" of the minimum defining `D_b(G)`.

**Formalization Note.** Stated as: every irreducible subrepresentation of `V` has dimension at most
`b`. For a finite group and a finite-dimensional complex `V`, Maschke's theorem makes `V` a direct
sum of irreducible subrepresentations and every irreducible constituent isomorphic to one of them,
so this is the paper's condition. -/
def IrrepDegreesLE {H V : Type*} [Group H] [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ H V) (b : ℕ∞) : Prop :=
  ∀ W : Subrepresentation ρ, W.toRepresentation.IsIrreducible →
    (Module.finrank ℂ W.toSubmodule : ℕ∞) ≤ b

end BlockSSM


