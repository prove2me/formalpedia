-- Prove2me | Definitions.Def_ObliviousRSP_IsPOVM
-- name    : ObliviousRSP_IsPOVM
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T15:21:04.625745+00:00
-- url     : https://prove2.me/theorems/41c9bf07-4ba1-49d2-8c0a-462af00087b6
-- title:
--   POVM with an arbitrary outcome set
-- statement:
--   A family $(E_m)_{m\in M}$ of complex $\alpha\times\alpha$ matrices, indexed by an arbitrary outcome set $M$, is a **POVM** when every $E_m$ is positive semidefinite and
--   $$
--   \sum_{m\in M} E_m = I ,
--   $$
--   the sum being unconditionally convergent (entrywise) with value the identity.
--
--   Alice's measurement in the original protocol (after the paper's reduction of her operation to a POVM) and the modified measurement $\mathcal M$ are POVMs in this sense.
--
--   **Formalization Note** The outcome set is an arbitrary type (no finiteness or countability), as messages may have variable length (p.5), so the sum is Mathlib's `HasSum`, which also asserts convergence; it is not a `tsum`, whose junk value $0$ would hide non-summability. Positive semidefinite includes Hermitian.
-- source:
--   Leung–Shor, Oblivious remote state preparation, arXiv:quant-ph/0201008v1, p.2, "Alice's operation E_φ, with only classical output, is just a POVM"

import Mathlib

open scoped ComplexOrder

namespace ObliviousRSP

/-- Leung–Shor, *Oblivious remote state preparation*, arXiv:quant-ph/0201008v1, p.2 ("Alice's operation `E_φ`, with only classical output, is just a POVM"): a POVM on
`ℂ^α` with outcome set `M` is a family `E : M → Matrix α α ℂ` of positive semidefinite
matrices summing to the identity.

**Formalization Note.** The outcome type `M` is arbitrary (no `Fintype`, no `Countable`;
the paper's p.5 allows messages of variable length), so the sum is Mathlib's unconditional
`HasSum` in the product topology of `Matrix α α ℂ`, not a finite sum and not a `tsum` (whose
junk value `0` would hide non-summability). -/
def IsPOVM {M α : Type} [Fintype α] [DecidableEq α] (E : M → Matrix α α ℂ) : Prop :=
  (∀ m, (E m).PosSemidef) ∧ HasSum E 1

end ObliviousRSP


