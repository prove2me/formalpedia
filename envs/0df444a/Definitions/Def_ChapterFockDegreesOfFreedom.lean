-- Prove2me | Definitions.Def_ChapterFockDegreesOfFreedom
-- name    : ChapterFockDegreesOfFreedom
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-01T03:56:32.871982+00:00
-- url     : https://prove2.me/theorems/2e6b6f16-1aea-4ee5-878b-03c6f652688b
-- title:
--   Chapter FockDegreesOfFreedom
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterFockDegreesOfFreedom.lean`): generated def bundle for ChapterFockDegreesOfFreedom. See BookProof/ChapterFockDegreesOfFreedom.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterFockDegreesOfFreedom.lean

import Mathlib


/-!
# The degree-of-freedom bookkeeping of the one-particle spaces
`L²(ℝ^N × ℤ₂^k)`

Source: `book.tex`.  Four times in the manuscript the one-particle space of the
(symmetric ⊗ antisymmetric) Fock space is declared to be
`L²(ℝ^N × ℤ₂^k)`, and each time the two exponents are justified by an explicit
count of fields, space(-time) coordinates and derivatives:

* Navier–Stokes (`book.tex` line ~4151):
  > *"The `ℝ^{33}` degrees of freedom correspond to 3 space coordinates (x), 3
  > fields (`u_k`) and its corresponding space-derivatives
  > (`∂_j u_k = u_{k,j}`, `∂_i∂_j u_k = u_{k,ij}`).  The `ℤ₂^3` degrees of freedom
  > correspond to 1 ghost corresponding to the divergence constraint (`ψ`) and
  > its corresponding space-derivatives (`∂_jψ = ψ_j`), minus one because we are
  > taking the tensor product of two Fock-spaces which introduces an extra `ℤ₂`
  > degree of freedom."*
* 3D Yang–Mills, `SU(3)` (line ~7047): `ℝ^{99} × ℤ₂^{31}`, from 3 space
  coordinates, `3×8 = 24` fields `A_{k a}` and their space-derivatives
  `∂_j A_{k a}`; `8` ghosts `ψ_a` and their space-derivatives `∂_jψ_a`, minus one.
* 4D Yang–Mills, `SU(3)` (line ~7305): `ℝ^{164} × ℤ₂^{39}`, from 4 spacetime
  coordinates, `4×8 = 32` fields `A_{μ a}` and their derivatives
  `∂_μ A_{ν a}`; `8` ghosts and their `4×8 = 32` derivatives, minus one.
* Quantum gravity in vielbein variables (line ~8261): `ℝ^{84} × ℤ₂^{19}`, from 4
  spacetime coordinates, `4×4 = 16` vielbein fields `e_μ^a` and their derivatives
  `∂_μ e_ν^a`; `4` diffeomorphism ghosts `ψ_μ` and their `4×4 = 16` derivatives,
  minus one.

The exponents `84`, `99`, `164` are used throughout the Lean development (e.g.
the `84`-dimensional fibre of the gravity Fock space) but the *bookkeeping
itself* — that the listed jet variables really are that many, and what the
"minus one" means — had not been recorded.  This file supplies it.

## What is formalized

For each of the four theories the file introduces the **index type** of the
listed one-particle degrees of freedom as an explicit finite sum type (one
summand per bullet of the book's list) and proves that its cardinality is the
number printed in the manuscript.  For the ghost sector it proves, in addition,
the **meaning of the "minus one"**: the ghost configuration space
`ℤ₂^{(raw ghosts)}` is canonically the product of `ℤ₂^{k}` with one extra `ℤ₂`
factor, which is the `ℤ₂` introduced by tensoring the bosonic and the fermionic
Fock space.  This is the content of `ghostSplit` and `card_ghost_eq_two_mul`.

## Deliverables

* `NavierStokes.jetCard` (`= 33`), `NavierStokes.ghostRawCard` (`= 4 = 3 + 1`);
* `YangMills3D.jetCard` (`= 99`), `YangMills3D.ghostRawCard` (`= 32 = 31 + 1`);
* `YangMills4D.jetCard` (`= 164`), `YangMills4D.ghostRawCard` (`= 40 = 39 + 1`);
* `Gravity.jetCard` (`= 84`), `Gravity.ghostRawCard` (`= 20 = 19 + 1`);
* `ghostSplit` / `card_ghost_eq_two_mul` — the generic "minus one" statement:
  `ℤ₂^{k+1} ≃ ℤ₂^{k} × ℤ₂`, and `#(ℤ₂^{k+1}) = 2 · #(ℤ₂^{k})`;
* `NavierStokes.jetCard_firstOrder` — the *first-order* Navier–Stokes jet space
  (space coordinates, fields and first derivatives only) has dimension `15`.
  The manuscript prints **both** numbers for the same space: `ℝ^{15}` in the
  displayed Fock space at line ~4141 and `ℝ^{33}` in the explanatory text at
  line ~4151.  The two agree exactly on which variables are listed except for
  the second space-derivatives `u_{k,ij}`, which the text includes and the
  display does not; since the Navier–Stokes Hamiltonian of that same section
  contains `ν u_{i,jj}`, the second derivatives are needed and `33` is the
  count consistent with the rest of the section.  Both counts are recorded here,
  the discrepancy being a bookkeeping slip of the manuscript.

Second space-derivatives are counted as **symmetric** in their two derivative
indices (`u_{k,ij} = u_{k,ji}`), i.e. `3 · 6 = 18` variables; this is what makes
the text's total `3 + 3 + 9 + 18 = 33` come out.
-/

namespace BookProof.FockDegreesOfFreedom

open Fintype

/-! ## The generic "minus one": tensoring two Fock spaces adds one `ℤ₂` -/

/-- **The book's "minus one".**  A ghost configuration on `k+1` binary degrees of
freedom is the same thing as a ghost configuration on `k` of them together with
one extra `ℤ₂` label — the extra `ℤ₂` produced by taking the tensor product of
the bosonic and the fermionic Fock space. -/
def ghostSplit (k : ℕ) : (Fin (k + 1) → ZMod 2) ≃ (Fin k → ZMod 2) × ZMod 2 :=
  (Fin.snocEquiv _).symm.trans (Equiv.prodComm _ _)



/-! ## Navier–Stokes: `L²(ℝ^{33} × ℤ₂^3)` -/

namespace NavierStokes

/-- Unordered pairs of space indices, i.e. the independent index pairs of a
**symmetric** second derivative `u_{k,ij} = u_{k,ji}` in three dimensions. -/
abbrev SymPair := {p : Fin 3 × Fin 3 // p.1 ≤ p.2}

/-- The one-particle index set of the Navier–Stokes theory, as listed in the
book: 3 space coordinates, 3 velocity fields `u_k`, their 9 first
space-derivatives `u_{k,j}` and their 18 symmetric second space-derivatives
`u_{k,ij}`. -/
abbrev Jet := Fin 3 ⊕ Fin 3 ⊕ (Fin 3 × Fin 3) ⊕ (Fin 3 × SymPair)







/-- The raw ghost degrees of freedom: the divergence-constraint ghost `ψ` and
its three space-derivatives `ψ_j`. -/
abbrev GhostRaw := Unit ⊕ Fin 3



end NavierStokes

/-! ## Three-dimensional `SU(3)` Yang–Mills: `L²(ℝ^{99} × ℤ₂^{31})` -/

namespace YangMills3D

/-- The one-particle index set: 3 space coordinates, the `3 × 8 = 24` fields
`A_{k a}` and their `3 × 24 = 72` space-derivatives `∂_j A_{k a}`. -/
abbrev Jet := Fin 3 ⊕ (Fin 3 × Fin 8) ⊕ (Fin 3 × Fin 3 × Fin 8)



/-- The raw ghost degrees of freedom: one ghost `ψ_a` per `SU(3)` generator and
their space-derivatives `∂_j ψ_a`. -/
abbrev GhostRaw := Fin 8 ⊕ (Fin 3 × Fin 8)



end YangMills3D

/-! ## Four-dimensional `SU(3)` Yang–Mills: `L²(ℝ^{164} × ℤ₂^{39})` -/

namespace YangMills4D

/-- The one-particle index set: 4 spacetime coordinates, the `4 × 8 = 32` fields
`A_{μ a}` and their `4 × 32 = 128` derivatives `∂_μ A_{ν a}`. -/
abbrev Jet := Fin 4 ⊕ (Fin 4 × Fin 8) ⊕ (Fin 4 × Fin 4 × Fin 8)



/-- The raw ghost degrees of freedom: one ghost `ψ_a` per `SU(3)` generator and
their spacetime-derivatives `∂_μ ψ_a`. -/
abbrev GhostRaw := Fin 8 ⊕ (Fin 4 × Fin 8)



end YangMills4D

/-! ## Quantum gravity in vielbein variables: `L²(ℝ^{84} × ℤ₂^{19})` -/

namespace Gravity

/-- The one-particle index set: 4 spacetime coordinates, the `4 × 4 = 16`
vielbein fields `e_μ^a` and their `4 × 16 = 64` derivatives `∂_μ e_ν^a`. -/
abbrev Jet := Fin 4 ⊕ (Fin 4 × Fin 4) ⊕ (Fin 4 × Fin 4 × Fin 4)



/-- The raw ghost degrees of freedom: 4 diffeomorphism ghosts `ψ_μ` and their
`4 × 4 = 16` derivatives `∂_μ ψ_ν`. -/
abbrev GhostRaw := Fin 4 ⊕ (Fin 4 × Fin 4)



end Gravity

end BookProof.FockDegreesOfFreedom


