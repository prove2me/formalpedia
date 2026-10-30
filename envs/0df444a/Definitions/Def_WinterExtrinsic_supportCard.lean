-- Prove2me | Definitions.Def_WinterExtrinsic_supportCard
-- name    : WinterExtrinsic_supportCard
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T03:17:40.903503+00:00
-- url     : https://prove2.me/theorems/06cb4de5-17a1-4851-b94a-a65e743460c3
-- title:
--   Support size of a measurement
-- statement:
--   Let $A = (A_o)_{o \in O}$ be a family of operators indexed by a finite outcome set $O$ (for instance a POVM). Its **support size** is the number of outcomes with a nonzero operator,
--
--   $$\#\{\, o \in O : A_o \neq 0 \,\}.$$
--
--   A measurement "supported on a set of cardinality at most $M$" is one whose support size is at most $M$: it produces at most $M$ different outcomes. In Winter's theorem each component POVM $A^{(\nu)}$ on $[m]^l$ has support size at most $2^{l I(\lambda;\hat\rho) + O(\sqrt l)}$.
--
--   **Formalization Note** Decidability of $A_o \ne 0$ is classical.
-- source:
--   Winter, "Extrinsic" and "intrinsic" data in quantum measurements, arXiv:quant-ph/0109050v3, §II, p.3 ("having a small number M of sequences on which it is supported (i.e. where A(ν) jl ≠ 0)")

import Mathlib

namespace WinterExtrinsic

open Classical in
/-- The size of the support of a measurement `A = (A_o)_{o ∈ O}`: the number of outcomes `o`
with `A_o ≠ 0`.

Winter, *"Extrinsic" and "intrinsic" data in quantum measurements*, arXiv:quant-ph/0109050v3,
§II, p.3 ("having a small number M of sequences on which it is supported (i.e. where
A^{(ν)}_{j^l} ≠ 0)").

**Formalization Note.** The outcome set `O` is any finite type; in this mission it is the set of
words `Fin l → Fin m`. Decidability of `A_o ≠ 0` is classical. -/
noncomputable def supportCard {O ι : Type} [Fintype O] (A : O → Matrix ι ι ℂ) : ℕ :=
  (Finset.univ.filter fun o => A o ≠ 0).card

end WinterExtrinsic


