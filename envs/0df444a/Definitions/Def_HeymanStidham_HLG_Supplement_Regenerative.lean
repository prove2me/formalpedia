-- Prove2me | Definitions.Def_HeymanStidham_HLG_Supplement_Regenerative
-- name    : HeymanStidham_HLG_Supplement_Regenerative
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T11:12:41.980369+00:00
-- url     : https://prove2.me/theorems/230ebee0-3f7b-496f-a864-26f42a874838
-- title:
--   (viii)–(ix), p. 988 — delayed regenerative real sequences with finite mean cycle length
-- statement:
--   Let $X_n$ be a measurable real sequence on a probability space. Regeneration is described by measurable integer epochs $R_0<R_1<\cdots$ almost surely, where $R_0$ is the finite initial delay. Each complete random block contains its length and every value of the sequence between its endpoints:
--
--   $$B_k=\bigl(R_{k+1}-R_k,(X_{R_k+j})_{0\le j<R_{k+1}-R_k}\bigr).$$
--
--   The complete blocks are mutually independent and identically distributed, and independent of the initial block $(X_0,\ldots,X_{R_0-1})$. The expected number of sequence positions in a complete cycle is finite:
--
--   $$\mathbb E[R_1-R_0]<\infty.$$
--
--   This is the classical delayed regenerative-sequence interpretation of (viii) and (ix), which cite Çinlar, Chapter 9. It applies separately to the interarrival sequence and the customer-total sequence. Their regeneration epochs need not agree, and neither sequence is required independent of the other.
--
--   **Formalization Note** A block is stored as a natural length paired with a real sequence padded by zero after that length. Strictly increasing integer epochs ensure positive complete lengths and that the blocks cover the entire tail. The initial block may be empty. The definition includes no cycle-reward moment, no average-limit condition, and no bound on the delay's expectation.
-- source:
--   Heyman and Stidham, The relation between customer and time averages in queues, Oper. Res. 28 (1980), DOI 10.1287/opre.28.4.983, p. 988, (viii) and (ix), citing [3], Chapter 9; PDF p. 6

import Mathlib

namespace HeymanStidham.HLG.Supplement

open MeasureTheory ProbabilityTheory

/-- The full block between successive regeneration epochs, including its length.
Values beyond the block are padded with zero; the length prevents ambiguity. -/
def cycleBlock {Ω : Type*} (X : ℕ → Ω → ℝ) (R : ℕ → Ω → ℕ)
    (k : ℕ) (ω : Ω) : ℕ × (ℕ → ℝ) :=
  (R (k + 1) ω - R k ω, fun j =>
    if j < R (k + 1) ω - R k ω then X (R k ω + j) ω else 0)

/-- The possibly empty, delayed initial block, preceding the first regeneration. -/
def delayBlock {Ω : Type*} (X : ℕ → Ω → ℝ) (R : ℕ → Ω → ℕ)
    (ω : Ω) : ℕ × (ℕ → ℝ) :=
  (R 0 ω, fun j => if j < R 0 ω then X j ω else 0)

/-- Classical delayed regeneration for a real sequence, (viii)/(ix), p. 988.
The complete cycles are independent and identically distributed and independent
of the initial block. Only the expected number of positions in a complete cycle
is required finite. There is no condition on cycle rewards or convergence. -/
def IsRegenerative {Ω : Type*} [MeasurableSpace Ω]
    (X : ℕ → Ω → ℝ) (P : Measure Ω) : Prop :=
  (∀ n, Measurable (X n)) ∧
  ∃ R : ℕ → Ω → ℕ,
    (∀ k, Measurable (R k)) ∧
    (∀ᵐ ω ∂P, StrictMono (fun k => R k ω)) ∧
    Measurable (delayBlock X R) ∧
    (∀ k, Measurable (cycleBlock X R k)) ∧
    iIndepFun (fun k : ℕ => if k = 0 then delayBlock X R
      else cycleBlock X R (k - 1)) P ∧
    (∀ k, IdentDistrib (cycleBlock X R k) (cycleBlock X R 0) P P) ∧
    Integrable (fun ω => ((R 1 ω - R 0 ω : ℕ) : ℝ)) P

end HeymanStidham.HLG.Supplement


