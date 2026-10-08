-- Prove2me | Definitions.Def_ChapterF4
-- name    : ChapterF4
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-06T05:26:44.467649+00:00
-- url     : https://prove2.me/theorems/41c325bb-aabc-40e8-8d1e-e4fe676daa0c
-- title:
--   Chapter F4
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterF4.lean`): generated def bundle for ChapterF4. See BookProof/ChapterF4.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterF4.lean

import Definitions.Def_ChapterF3
import Mathlib


/-!
# Chapter F4 — QFM: tomographic recovery (roadmap N14, §0 S7)

This file formalizes the tomographic-recovery half of the QFM (Quantum Flow
Matching) package (source `RiemannProof/QFM.tex` §8; reference implementation
`../unfer/qfm/`), following the N14 work-package queue (deliverables
F3.1–F3.5).  The F2.x half of N14 is on disk in
`ChapterF3.lean`/`ChapterF5.lean`/`ChapterF7.lean`.

It is the **merge (2026-07-08) of two independent Aristotle formalizations**
of the same deliverables; both are kept in full, in two sections below.

## Deliverables — first formalization (finite uniform-sign model)

* **F3.1 — Count-Sketch linearity and unbiasedness** (§8, `S₁`;
  `qfm/src/sketch.rs`).  The sketch `S₁` is linear (`csketch_add`,
  `csketch_smul`); with Rademacher signs it preserves inner products in
  expectation over the `2^d` sign patterns, `E[⟪S₁ x, S₁ y⟫] = ⟪x, y⟫`
  (`countsketch_unbiased`), via the pairwise sign identity
  `sign_pair_expectation`.
* **F3.2 — observable-matrix identity** (§8, `W_prob`; `qfm/src/observables.rs`).
  `Tr(E_{r,s}ᴴ Wᴴ Pₐ W) = conj(W_{a,r})·W_{a,s}` (`observable_matrix_identity`).
* **F3.3 — the unitary reduced flow** (§8 Phase 2; `qfm/src/potential.rs`).
  A unitary matrix preserves the Hermitian dot product
  (`unitary_preserves_dotProduct`); `e^{i H}` of a self-adjoint `H` is unitary
  (`selfAdjoint_exp_star_mul_self`).
* **F3.4 — the pseudo-inverse left-inverse** (§8, `Φ̃⁺`).  For full-column-rank
  `Φ`, `Φ⁺ = (Φᴴ Φ)⁻¹ Φᴴ` satisfies `Φ⁺ Φ = I` (`pseudoinverse_left_inverse`).

## Deliverables — second formalization (measure-theoretic model) + F3.5

* **F3.1** — Count-Sketch over an abstract probability space: linearity
  (`countSketch_add`) and unbiasedness `E[⟪S₁ x, S₁ y⟫] = ⟪x, y⟫` from the
  Rademacher hypothesis `∫ s c · s c' = δ_{cc'}` (`countSketch_unbiased`).
* **F3.2** — `Tr(E_{r,s}ᴴ Wᴴ Pₐ W) = conj(W_{a,r})·W_{a,s}`
  (`observable_matrix_entry`).
* **F3.3** — for Hermitian `H`, `e^{-i t H}` is unitary
  (`hermitian_flow_unitary`), hence norm-preserving
  (`hermitian_flow_preserves_normSq`).
* **F3.4** — Moore–Penrose left inverse via `Invertible (ΦᵀΦ)`
  (`pseudoInverse_left_inverse`).
* **F3.5 — the Misra–Gries heavy-hitter bound** (§8 Phase 4): with `k`
  counters, the estimate `f̂` of any item in a stream of length `N` satisfies
  `f − N/k ≤ f̂ ≤ f` (`misraGries_bound`; state machine `mgStep`/`mgRun`,
  conservation invariant `mgRun_sum`).  An independent formalization of F3.5
  also lives in `ChapterF6.lean` (`misra_gries_bound`).

Everything is `sorry`-free and `axiom`-free (only `propext`, `Classical.choice`,
`Quot.sound`); **no `EXTERNAL` hypothesis, no `axiom`**.
-/

open scoped BigOperators Matrix

namespace BookProof.ChapterF4

/-! ### First formalization — finite uniform-sign model -/

noncomputable section
open Matrix

/-! ## F3.1 — Count-Sketch linearity and unbiasedness (`qfm/src/sketch.rs`) -/

/-- A Rademacher sign from a bit. -/
def sgn (b : Bool) : ℝ := if b then 1 else -1

@[simp] theorem sgn_sq (b : Bool) : sgn b ^ 2 = 1 := by
  cases b <;> simp [sgn]

variable {d k : ℕ}

/-- The Count-Sketch map `S₁` with hash `h` and sign pattern `ω`:
`(S₁ x)_j = Σ_{c : h c = j} s(c)·x_c`. -/
def csketch (h : Fin d → Fin k) (ω : Fin d → Bool) (x : Fin d → ℝ) (j : Fin k) : ℝ :=
  ∑ c, (if h c = j then sgn (ω c) * x c else 0)

/-
**F3.1** (linearity in the data): `S₁ (x + y) = S₁ x + S₁ y`.
-/


/-
**F3.1** (homogeneity in the data): `S₁ (a • x) = a • S₁ x`.
-/


/-- The uniform expectation over the `2^d` sign patterns `ω : Fin d → Bool`. -/
def expectation (f : (Fin d → Bool) → ℝ) : ℝ := (∑ ω, f ω) / (2 ^ d)

/-
**F3.1** (pairwise sign identity — the independence input): summing
`s(c)·s(c')` over all `2^d` sign patterns gives `2^d` if `c = c'` and `0`
otherwise (Rademacher signs are orthonormal in expectation).
-/


/-
**F3.1** (unbiasedness): `E[⟪S₁ x, S₁ y⟫] = ⟪x, y⟫` — the Count-Sketch
estimator is unbiased for the inner product.
-/


/-! ## F3.2 — the observable-matrix identity (`qfm/src/observables.rs`) -/

/-
**F3.2**: with one-hot projector `Pₐ = |a⟩⟨a|` (`Matrix.single a a 1`) and the
Krylov operator basis element `E_{r,s} = |e_r⟩⟨e_s|` (`Matrix.single r s 1`), the
probability-observable matrix entry is
`Tr(E_{r,s}ᴴ · Wᴴ · Pₐ · W) = conj(W_{a,r})·W_{a,s}`.
-/


/-! ## F3.3 — the unitary reduced flow (`qfm/src/potential.rs`) -/

/-
**F3.3** (inner-product preservation): a unitary matrix `U` (with `Uᴴ U = 1`)
preserves the Hermitian dot product `⟪x, y⟫ = star x ⬝ᵥ y`.  In particular
`‖U x‖ = ‖x‖` (take `y = x`): norm-preserving generation.
-/


variable {A : Type*} [NormedRing A] [NormedAlgebra ℂ A] [StarRing A] [ContinuousStar A]
  [CompleteSpace A] [StarModule ℂ A]

/-
**F3.3** (the generator is unitary): for a self-adjoint `H`, the flow
`e^{i H} = selfAdjoint.expUnitary H` is unitary: `star U · U = 1`.
-/


/-! ## F3.4 — the pseudo-inverse left-inverse -/

/-
**F3.4**: for a full-column-rank matrix `Φ` (so the Gram matrix `Φᴴ Φ` is
invertible), the Moore–Penrose pseudo-inverse `Φ⁺ = (Φᴴ Φ)⁻¹ Φᴴ` is a left
inverse, `Φ⁺ Φ = I` — the subspace-recovery guarantee.
-/



end

/-! ### Second formalization — measure-theoretic model, and F3.5 -/

noncomputable section
open MeasureTheory

/-! ## F3.1 — Count-Sketch linearity and unbiasedness -/

variable {α κ Ω : Type*} [Fintype α] [DecidableEq α] [Fintype κ] [DecidableEq κ]
  {mΩ : MeasurableSpace Ω}

/-- The Count-Sketch map `S₁ : ℝ^α → ℝ^κ` (§8): `(S₁ x)_h = Σ_{c : hash c = h} s(c) x_c`,
with hash function `hash` and per-coordinate random signs `s`. -/
def countSketch (hash : α → κ) (s : α → Ω → ℝ) (x : α → ℝ) (ω : Ω) (h : κ) : ℝ :=
  ∑ c ∈ Finset.univ.filter (fun c => hash c = h), s c ω * x c



/-
**F3.1** (unbiasedness): with Rademacher signs (`E[s(c) s(c')] = δ_{cc'}`), the
Count-Sketch estimator preserves inner products in expectation:
`E[⟪S₁ x, S₁ y⟫] = ⟪x, y⟫`.  The AMS/Count-Sketch estimator.
-/


/-! ## F3.2 — the observable-matrix identities -/

/-
**F3.2** (observable-matrix entry, outer-product-of-a-row identity): with the
one-hot projector `P_a = |a⟩⟨a|` and operator basis `E_{r,s} = |e_r⟩⟨e_s|`,
`Tr(E_{r,s}ᴴ Wᴴ P_a W) = conj(W_{a,r}) · W_{a,s}`.
-/


/-! ## F3.3 — the unitary reduced flow -/

/-
**F3.3** (unitary reduced flow): for a Hermitian matrix `H`, the reduced flow
`U = e^{-i t H}` is unitary, `Uᴴ * U = 1`.
-/


/-
**F3.3** (norm-preserving generation): the reduced flow `U = e^{-i t H}` of a
Hermitian generator preserves the ℓ² norm-squared of any state,
`‖U c₀‖² = ‖c₀‖²` (the rev-14 `preserves_norm` guarantee).
-/


/-! ## F3.4 — the pseudo-inverse left-inverse -/

/-
**F3.4** (subspace-recovery guarantee): for a full-column-rank matrix `Φ` (so
that the Gram matrix `ΦᵀΦ` is invertible), the Moore–Penrose pseudo-inverse
`Φ⁺ = (ΦᵀΦ)⁻¹Φᵀ` is a left inverse: `Φ⁺ Φ = I`.
-/


/-! ## F3.5 — the Misra–Gries heavy-hitter bound -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Number of currently-active Misra–Gries counters (the support size of `c`). -/
def mgSupport (c : ι → ℕ) : ℕ := (Finset.univ.filter (fun a => 0 < c a)).card

/-- One step of Misra–Gries with `k` counters on state `(c, d)` (`c` the counter
vector, `d` the number of decrement rounds so far), processing item `x`:
increment `c x` if `x` is already tracked; else open a fresh counter if fewer
than `k` are active; else decrement every counter and record one decrement
round.  (`qfm` Misra–Gries heavy-hitter stage, §8 Phase 4.) -/
def mgStep (k : ℕ) (st : (ι → ℕ) × ℕ) (x : ι) : (ι → ℕ) × ℕ :=
  if 0 < st.1 x then (Function.update st.1 x (st.1 x + 1), st.2)
  else if mgSupport st.1 < k then (Function.update st.1 x 1, st.2)
  else (fun a => st.1 a - 1, st.2 + 1)

/-- The Misra–Gries run over a stream `xs` (processed from right to left; the
error bound is order-independent).  Returns `(f̂, d)` with `f̂` the counter
estimates and `d` the number of decrement rounds. -/
def mgRun (k : ℕ) : List ι → (ι → ℕ) × ℕ
  | [] => (fun _ => 0, 0)
  | x :: xs => mgStep k (mgRun k xs) x



/-
One-step preservation of the invariant "at most `k` counters are active".
-/


/-
Invariant: at most `k` counters are ever active.
-/


/-
Master conservation invariant: the total counter mass plus `(k+1)` per
decrement round equals the stream length `N`.
-/


/-
Decrement budget: `k · d ≤ N`.
-/


/-
Undercounting: the estimate never exceeds the true frequency.
-/


/-
The estimation error is bounded by the number of decrement rounds.
-/


/-
**F3.5** (Misra–Gries heavy-hitter guarantee): with `k` counters, the
frequency estimate `f̂ x = (mgRun k xs).1 x` of any item `x` in a stream `xs`
of length `N = xs.length` satisfies `f - N/k ≤ f̂ ≤ f`, where `f = xs.count x`
is the true frequency.  The lower bound is stated in the equivalent
truncated-subtraction-free form `f ≤ f̂ + N/k`.
-/



end

end BookProof.ChapterF4


