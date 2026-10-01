-- Prove2me | Definitions.Def_ChapterDirectSumEdge
-- name    : ChapterDirectSumEdge
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-01T03:41:11.194976+00:00
-- url     : https://prove2.me/theorems/4989aab3-8eac-46d5-890d-0293f68fecf4
-- title:
--   Chapter DirectSumEdge
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterDirectSumEdge.lean`): generated def bundle for ChapterDirectSumEdge. See BookProof/ChapterDirectSumEdge.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterDirectSumEdge.lean

import Definitions.Def_ChapterDirectSumEsa
import Mathlib


/-!
# The edge of an orthogonal direct sum: fibre edges glue to their infimum

Plan item **QG-3.4 (derived case)** of `CONSOLIDATED_PLAN.md` needs the
following purely structural fact, stated there informally as "the quadratic
form of the direct sum is the sum of the fibre forms, each `≥` its edge times
the fibre norm square, and `‖ψ‖² = Σᵢ ‖ψᵢ‖²":

> if every fibre operator `Hᵢ` satisfies a form bound
> `⟪u, Hᵢ u⟫ ≥ νᵢ‖u‖²` on its core `Dᵢ`, then the direct sum `⊕ᵢ Hᵢ`
> satisfies `⟪x, (⊕ᵢHᵢ) x⟫ ≥ ν‖x‖²` on the glued core `⊕ᵃˡᵍ Dᵢ`
> for any common lower bound `ν ≤ νᵢ`.

This module proves it, on the `dsCore`/`dsOp` direct sum of
`BookProof.ChapterDirectSumEsa`:

* `inner_dsCore_self_eq_sum`, `inner_dsOp_eq_sum` — on the algebraic direct
  sum both the norm and the energy are *finite* sums over the (finite)
  support of the state, so no summability side condition ever arises;
* `norm_sq_dsCore_eq_sum` — `‖x‖² = Σᵢ ‖xᵢ‖²` on the core;
* `quadForm_dsOp_eq_sum` — the quadratic form of `⊕ᵢHᵢ` is the sum of the
  fibre quadratic forms;
* **`dsOp_edge_of_fibre_edges`** — the edge statement itself, with a uniform
  bound `ν`;
* **`dsOp_edge_of_fibre_edges_le`** — the form the plan uses: fibre edges
  `νᵢ` and any `ν` with `ν ≤ νᵢ` for all `i` (e.g. `ν = min(ω₁/2, …, E₀)`);
* `dsOp_edge_pos` — the strict-positivity packaging: a positive common lower
  bound of the fibre edges is a strict one-particle edge of the glued
  operator.

## Honest boundary

This is the *derived* half of QG-3.4 only: it converts fibre edges into an
edge of the glued operator and asserts nothing about the fibre edges
themselves, nor about whether the physical operator of record decomposes as
such a direct sum (that is the QG-3.2(a) question).  A strict edge on a core
is a one-particle form bound, not a spectral gap of any Fock Hamiltonian.

Everything in this module is `sorry`-free and `axiom`-free.
-/

namespace BookProof.DirectSumEdge

open BookProof.FarisLavine BookProof.DirectSumEsa

noncomputable section

variable {ι : Type*} {G : ι → Type*} [∀ i, NormedAddCommGroup (G i)]
  [∀ i, InnerProductSpace ℂ (G i)] {D : ∀ i, Submodule ℂ (G i)}

/-- The support finset of a state of the algebraic direct sum. -/
def supportFinset (x : dsCore D) : Finset ι := x.2.1.toFinset



















end

end BookProof.DirectSumEdge


