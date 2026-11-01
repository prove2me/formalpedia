-- Prove2me | Definitions.Def_BaconThesis_OSRUnitary_osrApply
-- name    : BaconThesis_OSRUnitary_osrApply
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T15:58:04.224988+00:00
-- url     : https://prove2.me/theorems/78823101-0d86-47d3-98cf-354d2754a6dc
-- title:
--   Operator-sum representation $\rho \mapsto \sum_i A_i \rho A_i^\dagger$
-- statement:
--   Let the system Hilbert space be $\mathbb C^d$ for a finite index set $d$, and let $(A_i)_{i\in\iota}$ be a finite family of $d\times d$ complex matrices, the **OSR operators**. The **operator-sum representation** (OSR) they define is the linear map on $d\times d$ matrices
--
--   $$
--   \rho \;\longmapsto\; \sum_{i\in\iota} A_i\,\rho\,A_i^\dagger ,
--   $$
--
--   where $A_i^\dagger$ is the conjugate transpose of $A_i$. This is eq. (2.10) of the thesis: the evolution of the system's density matrix from time $0$ to time $t$ when the system and its environment start in a product state, with $A_i = A_i(t)$ at a fixed time $t$.
--
--   The OSR is the basic object of the thesis's treatment of open quantum systems; together with the normalization (2.12) it is the trace-preserving OSR.
--
--   **Formalization Note** Operators are `Matrix d d ℂ`. The OSR index $\iota$ is any finite type (the thesis's pairs $i=(\mu,\nu)$ of (2.11) are one instance). The map is defined on every matrix, not only on density matrices; the normalization is the separate predicate `IsTracePreservingOSR`.
-- source:
--   Bacon, Decoherence, Control, and Symmetry in Quantum Computers, arXiv:quant-ph/0305025v1, §2.2.1, eq. (2.10), p.16 (PDF p.33)

import Mathlib

open scoped Matrix

namespace BaconThesis.OSRUnitary

/-- Bacon, *Decoherence, Control, and Symmetry in Quantum Computers*, arXiv:quant-ph/0305025v1,
§2.2.1, eq. (2.10), p.16 (PDF p.33): the **operator-sum representation** (OSR) of an evolution
of the system, `ρ ↦ ∑_i A_i ρ A_i†`, for a finite family of OSR operators `A_i`.

**Formalization Note.** The system Hilbert space is `d → ℂ` for a finite type `d`, operators are
`Matrix d d ℂ`, and `A_i†` is the conjugate transpose `(A i)ᴴ`. The OSR index `ι` is any finite
type (the book's pairs `i = (μ, ν)` of (2.11) are one instance). The map is defined on every
matrix `ρ`, not only on density matrices; the time dependence `A_i(t)` of the book is fixed at
one time. The normalization (2.12) is the separate predicate `IsTracePreservingOSR`. -/
def osrApply {d ι : Type} [Fintype d] [Fintype ι] (A : ι → Matrix d d ℂ)
    (ρ : Matrix d d ℂ) : Matrix d d ℂ :=
  ∑ i, A i * ρ * (A i)ᴴ

end BaconThesis.OSRUnitary


