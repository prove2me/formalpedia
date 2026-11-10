-- Prove2me | Definitions.Def_TetraOT_Msg
-- name    : TetraOT_Msg
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T22:25:05.042603+00:00
-- url     : https://prove2.me/theorems/f104a95c-866f-4169-8dd0-be3cace12807
-- title:
--   Alice's message alphabet $\{X, Y, Z\}$ in the Tetrahedral Protocol
-- statement:
--   In the Tetrahedral Protocol Alice sends Bob a single message $M$ drawn from the three-letter alphabet
--   $$
--   M \in \{X, Y, Z\}.
--   $$
--   The message is computed from Alice's hand by her lookup table $A$ (Fig. 2) and read by Bob as a row index of his lookup table $B$ (Fig. 3).
--
--   **Formalization Note** A three-constructor inductive type with decidable equality and an explicit finite-type instance listing its three elements.
-- source:
--   Beaver, Correlated Group Interactions: Founding Cryptography on S4 and Sn, STOC 2027 submission (preprint, sha256 3dc88c598213707cd4cd52311a9b058999deef19d5aa9eed05208ba8092d65b7), §3 and Figs. 1–3, p.3 (p. = PDF page; the PDF has no printed page numbers)

import Mathlib

set_option autoImplicit false

namespace TetraOT

/-- **Alice's message alphabet `{X, Y, Z}`** (Beaver, *Correlated Group Interactions: Founding Cryptography on S4 and Sn*, STOC 2027 submission (held preprint, sha256 3dc88c59…92d65b7), §3, p.3: "Alice announces a message
`M ∈ {X, Y, Z}`"; Fig. 1–3, p.3). Here p. = PDF page; the PDF has no printed page numbers.

**Formalization Note.** A three-constructor inductive type with decidable equality and a `Fintype`
instance (its three elements listed), so that tables indexed by it can be evaluated. -/
inductive Msg
  | X
  | Y
  | Z
  deriving DecidableEq, Repr

/-- The three messages, listed. -/
instance : Fintype Msg where
  elems := {Msg.X, Msg.Y, Msg.Z}
  complete := fun m => by cases m <;> simp

end TetraOT


