-- Prove2me | Definitions.Def_ChapterA3j
-- name    : ChapterA3j
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-01T05:39:14.245358+00:00
-- url     : https://prove2.me/theorems/516a2a43-7528-49cb-b25b-c29e7e5cf850
-- title:
--   Chapter A3j
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterA3j.lean`): generated def bundle for ChapterA3j. See BookProof/ChapterA3j.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterA3j.lean

import Definitions.Def_ChapterA3
import Mathlib


/-!
# Chapter A, §A.3 — Notes 50–51 / Lemma 52: the chiral (`γ⁵`) decomposition core

Source: `book.tex` §A.3, Notes 50–51 and Lemma 52 (line ~5560) — the
classification of the finite-dimensional irreducible representations.

The book's finite-dim rep theory of `SL(2,ℂ)` / `Spin⁺(3,1)` is organized around
the chirality operator `γ⁵`:

* **Note 51 (complex irreps).**  The complex irreps `V_{(m,n)} = V⁺_m ⊗ V⁻_n` are
  built from symmetric tensor powers of the two `γ⁵`-eigenspaces (the Weyl / chiral
  Dirac spinors `V±`).  *Under parity* `V⁺_m ⊗ V⁻_n ↔ V⁻_m ⊗ V⁺_n`.
* **Lemma 52 (real irreps — the payoff).**  Unlike the complex irreps, the *real*
  irreps `W_{(m,n)}`, `m ≥ n`, are automatically projective reps of the **full**
  Lorentz group (invariant under parity and time reversal), because parity swaps
  the two chiralities and thus glues `V_{(m,n)}` to `V_{(n,m)}`.

This file formalizes the concrete algebraic **base case** of that structure —
the `γ⁵`-eigenspaces of the Dirac spinor itself (`m = n = ½`) — on the `4×4`
Majorana Clifford model of §A.3 (`ChapterA3`).  It is the exact chirality
analogue of the energy-sign story of `ChapterA4e`.  The chirality operator
`iγ⁵ = ChapterA3.mgamma5` squares to `-1` (`ChapterA3.mgamma5_sq`), so its
eigenvalues are `±i` and the chiral projectors `P_{L/R} = ½(1 ∓ i·iγ⁵)` live over
`ℂ`.

The two structural facts of Notes 50–51 / Lemma 52 that this concrete core
captures are:

* **Spin⁺-invariance of the chiral subspaces** (`projChirL_spinGen_comm` etc.):
  `iγ⁵` *commutes* with every even Clifford element `γ^μγ^ν` (the `Spin⁺(3,1)`
  generators), so the two chiral projectors commute with the whole connected
  Lorentz action — i.e. `V±` are genuine `Spin⁺` subrepresentations (the Weyl
  irreps `V⁺_½`, `V⁻_½`).
* **Parity swaps the chiralities** (`parity_swaps_chirL` / `parity_swaps_chirR`):
  `iγ⁵` *anticommutes* with `γ⁰` (the parity operator), so `γ⁰` *intertwines* the
  two chiral projectors, `P_L γ⁰ = γ⁰ P_R`.  Hence a single chirality is **not**
  preserved by the full Lorentz group (`chirality_not_parity_invariant`): the
  real full-Lorentz irrep must combine `V_{(m,n)}` with its parity image
  `V_{(n,m)}` — precisely the mechanism of Lemma 52.

Everything reduces to the integer Clifford relations of `ChapterA3` and is
`sorry`-free / `axiom`-free (only `propext`, `Classical.choice`, `Quot.sound`),
with **no `EXTERNAL` hypothesis** (Note 50 / Weyl complete reducibility and the
symmetric-tensor-power generalization to arbitrary `(m,n)` remain the cited
backbone, not this algebraic base case).
-/

open Matrix

namespace BookProof.ChapterA3j

open BookProof.ChapterA3

/-! ## The chirality operator and the `Spin⁺` generators over `ℂ` -/

/-- The chirality operator `iγ⁵` as a complex matrix (`= ChapterA3.mgamma5`). -/
noncomputable def chir : Matrix (Fin 4) (Fin 4) ℂ := mgamma5

/-- The `Spin⁺(3,1)` generators `γ^μγ^ν` (the even Clifford elements): the
infinitesimal boosts (`μ,ν` mixed) and rotations act through these. -/
noncomputable def spinGen (μ ν : Fin 4) : Matrix (Fin 4) (Fin 4) ℂ :=
  mgamma μ * mgamma ν









/-! ## The chiral projectors `P_{L/R} = ½(1 ∓ i·iγ⁵)` -/

/-- The left chiral projector `P_L = ½(1 - i·iγ⁵)`. -/
noncomputable def projChirL : Matrix (Fin 4) (Fin 4) ℂ :=
  (2 : ℂ)⁻¹ • (1 - Complex.I • chir)

/-- The right chiral projector `P_R = ½(1 + i·iγ⁵)`. -/
noncomputable def projChirR : Matrix (Fin 4) (Fin 4) ℂ :=
  (2 : ℂ)⁻¹ • (1 + Complex.I • chir)









/-! ## `Spin⁺`-invariance of the chiral projectors (the Weyl irreps `V±`) -/





/-! ## The payoff: parity swaps the two chiralities (Lemma 52) -/









end BookProof.ChapterA3j


