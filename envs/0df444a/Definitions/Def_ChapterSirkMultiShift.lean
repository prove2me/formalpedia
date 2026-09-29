-- Prove2me | Definitions.Def_ChapterSirkMultiShift
-- name    : ChapterSirkMultiShift
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-09-10T05:16:35.290243+00:00
-- url     : https://prove2.me/theorems/b6f732b1-d7b3-449d-b204-46b08019b942
-- title:
--   `CONSOLIDATED_PLAN.md` §12.2, **Gap 4b**: `ChapterH5` covers the *single*-shift inversion-free shortcut (`krylov_no_inve ...
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (module `BookProof.SirkMultiShift`, source chapter `BookProof/ChapterSirkMultiShift.lean`).
--
--   `CONSOLIDATED_PLAN.md` §12.2, **Gap 4b**: `ChapterH5` covers the *single*-shift inversion-free shortcut (`krylov_no_inversion_eq_standard`: the sequence `wₖ = (H̄ − γI)wₖ₋₁` spans the standard Krylov subspace). The SIRK/Hashimoto numerics use a *sequence of distinct complex shifts* `z₁, z₂, …`, i.e. the forward sequence
--
--   `w₀ = v₀`, `wₖ₊₁ = (H̄ − zₖ I) wₖ`,
--
--   and the identity that the plan records as missing is
--
--   `span{w₀, w₁, …, w_{m−1}} = Kry m(H̄, v₀)`.
--
--   That identity is proved here, together with the general principle behind it.
--
--   * `triangularSpan_eq_krylovSpan` — the **general triangular criterion**: any family `u : ℕ → E` with `uᵢ − H^i v ∈ Kry i(H, v)` spans exactly the Krylov flag, `span{uᵢ | i < m} = Kry m(H, v)` for every `m`. This isolates the only property a "forward sequence" needs: the change of basis from `{H^i v}` is unitriangular. * `multiShiftSeq` — the multi-shift forward sequence `wₖ₊₁ = (H − zₖ I) wₖ`, for an arbitrary shift sequence `z : ℕ → K` (no distinctness, no non-vanishing, no field-characteristic hypothesis). * `multiShiftSeq_sub_pow_mem` — the degree-lowering core: `wᵢ − H^i v ∈ Kry i`. * `krylov_multiShift_eq_standard` — **headline (Gap 4b)**: `span{wᵢ | i < m} = Kry m(H, v)`. * `krylov_multiShift_span_eq_of_shifts` — hence the span does not depend on the shift sequence at all: two different shift schedules produce the same subspace, so the numerics' choice of `{z_j}` changes the basis but never the Krylov space that is compressed. * `multiShiftSeq_const` — the single-shift sequence of `ChapterH5` is the constant-schedule instance.
--
--   Everything is `sorry`-free and `axiom`-free (only `propext`, `Classical.choice`, `Quot.sound`).
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterSirkMultiShift.lean

import Definitions.Def_ChapterH5
import Mathlib

import Mathlib

/-!
# Chapter SirkMultiShift — the multi-shift forward-sequence span identity

`CONSOLIDATED_PLAN.md` §12.2, **Gap 4b**: `ChapterH5` covers the *single*-shift
inversion-free shortcut (`krylov_no_inversion_eq_standard`: the sequence
`wₖ = (H̄ − γI)wₖ₋₁` spans the standard Krylov subspace).  The SIRK/Hashimoto
numerics use a *sequence of distinct complex shifts* `z₁, z₂, …`, i.e. the
forward sequence

  `w₀ = v₀`,  `wₖ₊₁ = (H̄ − zₖ I) wₖ`,

and the identity that the plan records as missing is

  `span{w₀, w₁, …, w_{m−1}} = Kry m(H̄, v₀)`.

That identity is proved here, together with the general principle behind it.

## Deliverables

* `triangularSpan_eq_krylovSpan` — the **general triangular criterion**: any
  family `u : ℕ → E` with `uᵢ − H^i v ∈ Kry i(H, v)` spans exactly the Krylov
  flag, `span{uᵢ | i < m} = Kry m(H, v)` for every `m`.  This isolates the only
  property a "forward sequence" needs: the change of basis from `{H^i v}` is
  unitriangular.
* `multiShiftSeq` — the multi-shift forward sequence `wₖ₊₁ = (H − zₖ I) wₖ`, for
  an arbitrary shift sequence `z : ℕ → K` (no distinctness, no non-vanishing, no
  field-characteristic hypothesis).
* `multiShiftSeq_sub_pow_mem` — the degree-lowering core: `wᵢ − H^i v ∈ Kry i`.
* `krylov_multiShift_eq_standard` — **headline (Gap 4b)**:
  `span{wᵢ | i < m} = Kry m(H, v)`.
* `krylov_multiShift_span_eq_of_shifts` — hence the span does not depend on the
  shift sequence at all: two different shift schedules produce the same
  subspace, so the numerics' choice of `{z_j}` changes the basis but never the
  Krylov space that is compressed.
* `multiShiftSeq_const` — the single-shift sequence of `ChapterH5` is the
  constant-schedule instance.

Everything is `sorry`-free and `axiom`-free (only `propext`, `Classical.choice`,
`Quot.sound`).
-/

noncomputable section

namespace BookProof.ChapterSirkMultiShift

open BookProof.ChapterH5

variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E]

/-! ## 1. The general triangular criterion -/

/-- The span of the first `m` members of a family `u : ℕ → E`. -/
def seqSpan (u : ℕ → E) (m : ℕ) : Submodule K E :=
  Submodule.span K {x | ∃ i < m, x = u i}





variable {H : E →ₗ[K] E} {v : E}







/-! ## 2. The multi-shift forward sequence -/

/-- The **multi-shift forward sequence** `w₀ = v`, `wₖ₊₁ = (H − zₖ I) wₖ`: the
inversion-free construction with a *schedule* of shifts, as used by the SIRK
numerics. -/
def multiShiftSeq (H : E →ₗ[K] E) (z : ℕ → K) (v : E) : ℕ → E
  | 0 => v
  | (k + 1) => (H - z k • 1) (multiShiftSeq H z v k)













end BookProof.ChapterSirkMultiShift


