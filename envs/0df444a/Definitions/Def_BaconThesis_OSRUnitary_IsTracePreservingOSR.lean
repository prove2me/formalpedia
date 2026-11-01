-- Prove2me | Definitions.Def_BaconThesis_OSRUnitary_IsTracePreservingOSR
-- name    : BaconThesis_OSRUnitary_IsTracePreservingOSR
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T15:58:09.826991+00:00
-- url     : https://prove2.me/theorems/4c5ad619-d15b-475f-b233-f1d6f65ef993
-- title:
--   Trace-preserving normalization $\sum_i A_i^\dagger A_i = I$
-- statement:
--   A finite family $(A_i)_{i\in\iota}$ of $d\times d$ complex matrices satisfies the **normalization condition** of the operator-sum representation when
--
--   $$
--   \sum_{i\in\iota} A_i^\dagger A_i = I ,
--   $$
--
--   where $I$ is the $d\times d$ identity matrix. This is eq. (2.12) of the thesis; it follows from the unitarity of the joint system–environment evolution, and together with (2.10) it makes the OSR trace preserving.
--
--   **Formalization Note** Operators are `Matrix d d ℂ` with $d$ a finite type with decidable equality; the OSR index $\iota$ is any finite type.
-- source:
--   Bacon, Decoherence, Control, and Symmetry in Quantum Computers, arXiv:quant-ph/0305025v1, §2.2.1, eq. (2.12), p.16 (PDF p.33)

import Mathlib

open scoped Matrix

namespace BaconThesis.OSRUnitary

/-- Bacon, *Decoherence, Control, and Symmetry in Quantum Computers*, arXiv:quant-ph/0305025v1,
§2.2.1, eq. (2.12), p.16 (PDF p.33): the normalization condition `∑_i A_i† A_i = I` which,
together with (2.10), makes the operator-sum representation **trace preserving**.

**Formalization Note.** Operators are `Matrix d d ℂ` for a finite type `d` with decidable
equality (for the identity matrix `1`), `A_i†` is `(A i)ᴴ`, and the OSR index `ι` is any finite
type. -/
def IsTracePreservingOSR {d ι : Type} [Fintype d] [DecidableEq d] [Fintype ι]
    (A : ι → Matrix d d ℂ) : Prop :=
  ∑ i, (A i)ᴴ * A i = 1

end BaconThesis.OSRUnitary


