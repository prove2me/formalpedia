-- Prove2me | Definitions.Def_ChapterKernelBound
-- name    : ChapterKernelBound
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-01T04:14:47.764776+00:00
-- url     : https://prove2.me/theorems/d6639078-b0f3-4c2c-a0a9-6294fc2f537b
-- title:
--   Chapter KernelBound
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterKernelBound.lean`): generated def bundle for ChapterKernelBound. See BookProof/ChapterKernelBound.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterKernelBound.lean

import Mathlib


/-!
# Chapter B §3 — Cauchy–Schwarz / Hilbert–Schmidt boundedness of the kernel operator

Source: `book.tex`, chapter *"Wave-function parametrization of a probability
measure"*, §*"3. Any conditional probability measure in a standard measure space
is parametrized by a unitary operator"* (`book.tex` line ~1392) — the book's
central theorem.

Having written the joint probability density as `p(x,y) = |Ψ(x,y)|²` for a
normalized wave-function `Ψ ∈ L²(X × Y)`, the book views `Ψ` as an **integral
operator** `Ψ : L²(X) → L²(Y)`, `Ψ{Φ}(y) = ∫ dx Ψ(x,y) Φ(x)`, and observes
(the prerequisite to the singular-value expansion `Ψ = W D U†` formalized in
`ChapterB3`/`ChapterB3b`):

> *"Note that the Cauchy–Schwarz inequality implies `|∫ dx Ψ(x,y) Φ(x)|² ≤
> ∫ dx |Ψ(x,y)|²` where the `L²` norm of `Φ(x)` is 1.  Thus
> `‖Ψ{Φ}‖ = ∫ dy |∫ dx Ψ(x,y) Φ(x)|² ≤ ∫ dx dy |Ψ(x,y)|² = 1`, this implies
> `Ψ(x,y)` is bounded when defined as an operator `Ψ : L²(X) → L²(Y)`."*

This is the classical **Hilbert–Schmidt bound**: an integral operator with an
`L²` kernel is bounded, with operator norm at most the `L²` (Hilbert–Schmidt)
norm of the kernel.  Consistently with the finite-dimensional models used
throughout `BookProof` (e.g. the finite SVD in `ChapterB3b`), we formalize it for
a **discretized** kernel over finite index sets `ιx` (the sample space `X`) and
`ιy` (`Y`); the argument is exactly the book's row-wise Cauchy–Schwarz followed
by a sum over `y`, and is index-set/`RCLike`-field agnostic.

The kernel operator is `kernelOp Ψ Φ y = ∑ x, Ψ y x * Φ x` (the book's
`Ψ{Φ}(y)`).  The results, all `sorry`-free and `axiom`-free (only `propext`,
`Classical.choice`, `Quot.sound`):

* `kernel_hs_sq_bound` — the squared Hilbert–Schmidt bound
  `∑ y ‖Ψ{Φ}(y)‖² ≤ (∑ y ∑ x ‖Ψ(y,x)‖²) · (∑ x ‖Φ(x)‖²)`;
* `kernel_l2_bound` — its `L²` form
  `√(∑ y ‖Ψ{Φ}(y)‖²) ≤ √(∑ y ∑ x ‖Ψ(y,x)‖²) · √(∑ x ‖Φ(x)‖²)`, i.e.
  `‖Ψ{Φ}‖_{L²} ≤ ‖Ψ‖_{HS} · ‖Φ‖_{L²}` (the book's inequality verbatim);
* `kernel_contraction` — the book's normalized conclusion: if the kernel is
  normalized `∑ y ∑ x ‖Ψ(y,x)‖² = 1` (a normalized wave-function) then the
  operator is a **contraction**, `∑ y ‖Ψ{Φ}(y)‖² ≤ ∑ x ‖Φ(x)‖²`, hence bounded.
-/

namespace BookProof.KernelBound

open Finset

variable {𝕜 : Type*} [RCLike 𝕜]
variable {ιx ιy : Type*} [Fintype ιx] [Fintype ιy]

/-- The discretized integral-kernel operator `Φ ↦ (y ↦ ∑ x, Ψ y x * Φ x)`,
the book's `Ψ{Φ}(y) = ∫ dx Ψ(x,y) Φ(x)`. -/
def kernelOp (Ψ : ιy → ιx → 𝕜) (Φ : ιx → 𝕜) : ιy → 𝕜 :=
  fun y => ∑ x, Ψ y x * Φ x









end BookProof.KernelBound


