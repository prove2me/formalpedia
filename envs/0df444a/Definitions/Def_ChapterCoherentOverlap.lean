-- Prove2me | Definitions.Def_ChapterCoherentOverlap
-- name    : ChapterCoherentOverlap
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-01T03:31:42.414042+00:00
-- url     : https://prove2.me/theorems/e7805c1c-5438-49a2-9b30-ea4f9b9d751e
-- title:
--   Chapter CoherentOverlap
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterCoherentOverlap.lean`): generated def bundle for ChapterCoherentOverlap. See BookProof/ChapterCoherentOverlap.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterCoherentOverlap.lean

import Mathlib


/-!
# Chapter "The Coherent State of Attention", §"The Geometry of the Wave-packet" —
the coherent-state overlap is the Gaussian reproducing kernel

Formalization of the first identity of the new chapter `Book/CoherentState.lean`
(adapted from `coherent.md`).  Each query/key vector `q, k` is the parameter of a
*coherent state* `|q⟩, |k⟩` of a bosonic mode; the Bargmann–Fock reproducing
kernel gives the overlap

  `⟨q | k⟩ = exp (-‖q‖²/2 - ‖k‖²/2 + ⟪q, k⟫)`.

This module works over `EuclideanSpace ℝ (Fin n)` (the *real* coherent-state
parameters, where the overlap is a positive real number — the general complex
Bargmann kernel carries an extra phase `exp (i · Im ⟪q,k⟫)` which is invisible to
the Born rule of the next chapter section).  That restriction is no longer a gap:
`BookProof.ChapterCoherentOverlapComplex` formalizes the complex kernel, its
modulus/phase factorization, and the fact (`coherentOverlapC_ofReal`) that the
real kernel below is exactly its restriction to real parameters.

Deliverables (all `sorry`-free, `axiom`-free):

* `coherentOverlap` — the overlap, as a real-valued function of two vectors;
* `coherentOverlap_eq` — the explicit coordinate (sum) formula;
* `coherentOverlap_eq_gaussian` — **the reproducing kernel is a Gaussian**:
  `⟨q|k⟩ = exp (-‖q - k‖²/2)`; the "baseline" terms `-‖q‖²/2, -‖k‖²/2` and the
  alignment term `⟪q,k⟫` recombine into (minus one half) the squared distance;
* `coherentOverlap_pos`, `coherentOverlap_le_one` — the overlap is a positive
  real number, never exceeding `1`;
* `coherentOverlap_self`, `coherentOverlap_unit` — a coherent state is
  normalized: `⟨q|q⟩ = 1`, in particular for a unit vector;
* `coherentOverlap_comm` — symmetry of the kernel;
* `coherentOverlap_eq_one_iff` — the overlap saturates exactly on the diagonal.

Everything here is `sorry`-free and `axiom`-free (only `propext`,
`Classical.choice`, `Quot.sound`).
-/

open scoped BigOperators

noncomputable section

namespace BookProof.ChapterCoherentOverlap

variable {n : ℕ}

/-- The **coherent-state overlap** of two real coherent-state parameters,
i.e. the Bargmann–Fock reproducing kernel evaluated at `(q, k)`:
`⟨q | k⟩ = exp (-‖q‖²/2 - ‖k‖²/2 + ⟪q, k⟫)`. -/
def coherentOverlap (q k : EuclideanSpace ℝ (Fin n)) : ℝ :=
  Real.exp (-‖q‖ ^ 2 / 2 - ‖k‖ ^ 2 / 2 + inner ℝ q k)

/-! ## Coordinate identities -/









/-! ## The overlap is a Gaussian -/



/-! ## Basic properties -/















end BookProof.ChapterCoherentOverlap

end


