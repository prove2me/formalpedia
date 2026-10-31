-- Prove2me | Definitions.Def_ObliviousRSP_IsGeneric
-- name    : ObliviousRSP_IsGeneric
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T15:21:45.081875+00:00
-- url     : https://prove2.me/theorems/c1a8c525-d3eb-43b4-9783-637472d69672
-- title:
--   Generic ensemble of pure states
-- statement:
--   A set $S\subseteq\mathbb C^\iota$ of vectors is a **generic ensemble** when
--
--   1. every $\psi\in S$ is a unit vector, $\langle\psi|\psi\rangle = 1$, and
--   2. the projectors $|\psi\rangle\langle\psi|$, $\psi\in S$, span the complex vector space of all $\iota\times\iota$ complex matrices.
--
--   The paper calls an ensemble generic when its density matrices form a basis of the operators on the input Hilbert space. Genericity is what makes the main result true: for a non-generic ensemble (the paper's latitude example) a cheaper Bob-oblivious protocol exists.
--
--   **Formalization Note** Spanning replaces basis: the ensemble may contain more than $d^2$ states, and every basis spans. The probability distribution on the ensemble plays no role in the paper's argument and is omitted. For an empty index type there is no unit vector, so only the empty set qualifies, and it does (the space of matrices is zero).
-- source:
--   Leung–Shor, Oblivious remote state preparation, arXiv:quant-ph/0201008v1, p.2, definition of "generic ensemble" (first sentence of p.2)

import Mathlib
import Definitions.Def_ObliviousRSP_pureState

namespace ObliviousRSP

/-- Leung–Shor, *Oblivious remote state preparation*, arXiv:quant-ph/0201008v1, p.2: "We use the term “generic ensemble” to describe an ensemble of states whose density
matrices form a basis of operators acting on some (input) Hilbert space." A set `S` of vectors
in `ℂ^ι` is generic when every `ψ ∈ S` is a unit vector and the projectors `|ψ⟩⟨ψ|`,
`ψ ∈ S`, span the space of all `ι × ι` complex matrices over `ℂ`.

**Formalization Note.** *Spanning* replaces *basis*: `S` may contain more than `d²` states,
and every basis spans, so every generic ensemble of the paper satisfies this predicate. The
probability distribution of the ensemble plays no role in the paper's argument and is omitted.
For an empty `ι` no unit vector exists, so `S = ∅`, and `∅` is generic (the zero space). -/
def IsGeneric {ι : Type} [Fintype ι] (S : Set (ι → ℂ)) : Prop :=
  (∀ ψ ∈ S, star ψ ⬝ᵥ ψ = 1) ∧ Submodule.span ℂ (pureState '' S) = ⊤

end ObliviousRSP


