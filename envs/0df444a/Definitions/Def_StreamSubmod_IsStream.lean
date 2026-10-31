-- Prove2me | Definitions.Def_StreamSubmod_IsStream
-- name    : StreamSubmod_IsStream
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:25:15.401284+00:00
-- url     : https://prove2.me/theorems/4c5e6809-7bcf-40fb-8b45-1c403b7892d7
-- title:
--   A stream over the ground set
-- statement:
--   A stream over the finite ground set $V$ is an enumeration $e_1,e_2,\dots,e_n$ of the elements of $V$ in the order of their arrival. Each element arrives exactly once, and the order is arbitrary.
--
--   All guarantees of this development hold for every such order.
--
--   **Formalization Note** A stream is a duplicate-free list containing every element of the ground set.
-- source:
--   Alaluf, Ene, Feldman, Nguyen & Suh, An Optimal Streaming Algorithm for Submodular Maximization with a Cardinality Constraint, arXiv:1911.12959v3, p.14, "let us denote by e1, e2, . . . , en the elements of V in the order of their arrival"

import Mathlib

namespace StreamSubmod

/-- `σ` is a stream over the ground set `E`: "let us denote by `e₁, e₂, …, eₙ` the elements of `V`
in the order of their arrival" (Alaluf, Ene, Feldman, Nguyen & Suh, arXiv:1911.12959v3, p.14).

**Formalization Note.** A stream is a duplicate-free list containing every element of `E`, so each
element arrives exactly once. The arrival order is arbitrary (adversarial): every theorem of this
development quantifies over all such lists. -/
def IsStream {E : Type} (σ : List E) : Prop :=
  σ.Nodup ∧ ∀ e : E, e ∈ σ

end StreamSubmod


