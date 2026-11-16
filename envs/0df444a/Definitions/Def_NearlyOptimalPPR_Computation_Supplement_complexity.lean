-- Prove2me | Definitions.Def_NearlyOptimalPPR_Computation_Supplement_complexity
-- name    : NearlyOptimalPPR_Computation_Supplement_complexity
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T21:47:23.827362+00:00
-- url     : https://prove2.me/theorems/9df95115-4fd1-4276-ad58-33678dad7e2d
-- title:
--   Uniform nonrecursive envelopes and charged balanced-block preparation
-- statement:
--   For real $\varepsilon$ put $N=96/\varepsilon$. For a constant $C$, natural exponent $h$, and integer block $b$, define the notation
--   $$B(C,h,\varepsilon,b)=C(N^2/b+Nb)(1+\log(2+N))^h,$$
--   $$B_{\rm bal}(C,h,\varepsilon)=C\varepsilon^{-3/2}(1+\log(2+N))^h.$$
--   An integer-square comparison search chooses the balanced block; its full preparation is charged $8(\lceil N\rceil+2)$, in addition to the algorithm's work. Its identification with $\max(1,\lfloor\sqrt N\rfloor)$ and legality are theorem conclusions.
--
--   Memory consistency means that memoized degrees and rows agree with their oracle answers, every stored core row has been acquired, and every row with nonzero work residual, nonzero potential, or active status has a queried degree. This is a predicate to be proved for the execution, never a precondition. None of these definitions asserts termination, correctness or a complexity bound.
--
--   Differences from the source:
--   - encoding: expected O-tilde(N^2/b+Nb) work, O(N) graph adjacency queries, and balanced-block O-tilde(epsilon^(-3/2)) work → positive uniform C and Cq and one natural logarithmic exponent h, with work <= C*(N^2/b+Nb)*(1+log(2+N))^h, actual query-trace length <= Cq*N, and the full balanced-block consequence; reason: the p.16 proof and fixed SolveModel give finite logarithmic overheads; all constants precede every graph and input, and balanced constants may depend only on fixed comparison constants and the primitive model
--   - encoding: b asymptotic to sqrt(N) → every legal b between any fixed positive multiples of sqrt(N), together with an integer-square-search choice max(1,floor(sqrt(N))) and charged preparation; reason: this states the whole comparison-constant interpretation and implements the particular balanced choice without a free square-root instruction
-- source:
--   Rong-Hua Li, Quanqing Xu, Yichun Yang, Junjie Zhou, STOC 2027 submission #884 (October 2026), Theorem 3.1 and its proof, p. 5 (printed = PDF); canonical source.pdf, sha256 17a68253bbd187a44704374a465f62c34c8d7628c44b48c160e903ed3300bdb4; proof p.16; integer block selection uses the published blockSearch

import Definitions.Def_NearlyOptimalPPR_Computation_Supplement_ledger

set_option autoImplicit false

open Finset Matrix MeasureTheory
open scoped ENNReal

noncomputable section

namespace NearlyOptimalPPR.Computation.Supplement

attribute [local instance] Classical.propDecidable

/-- Only notation: no complexity bound is part of this definition. -/
def workBound (C : ℝ) (h : ℕ) (ε : ℝ) (b : ℕ) : ℝ :=
  C * (scale ε ^ 2 / (b : ℝ) + scale ε * (b : ℝ)) *
    (1 + Real.log (2 + scale ε)) ^ h

def balancedBound (C : ℝ) (h : ℕ) (ε : ℝ) : ℝ :=
  C * Real.rpow (1 / ε) (3 / 2 : ℝ) * (1 + Real.log (2 + scale ε)) ^ h

/-- Integer square comparisons, not a real square-root machine instruction.
For legal input this search is max(1,floor(sqrt N)). -/
def balancedBlock (ε : ℝ) : ℕ :=
  max 1 (blockSearch (scale ε) 0 (⌈scale ε⌉₊ + 1) 0)

/-- Charge the entire preparation search, including its first failing test.
This O(N) allowance uses only integer increments and square comparisons. -/
def balancedPreparation (ε : ℝ) : ℝ≥0∞ := (8 * (⌈scale ε⌉₊ + 2) : ℕ)

def balancedExpectedWork {n : ℕ} (m : SolveModel) (g : InputGraph n) (s : Fin n)
    (α ε : ℝ) : ℝ≥0∞ :=
  balancedPreparation ε + expectedWork m g s α ε (balancedBlock ε)

/-- Memory consistency to be proved from the access trace, not assumed as a
validity predicate. In particular, a solve may only use acquired rows. -/
def accessConsistent {n : ℕ} (g : InputGraph n) (l : Ledger n) : Prop :=
  (∀ v d, l.access.degrees v = some d → d = (g.neighbors v).length) ∧
  (∀ v row, l.access.rows v = some row → row = g.neighbors v) ∧
  (∀ v ∈ l.core.stored, l.access.rows v = some (g.neighbors v)) ∧
  (∀ v, l.core.x v ≠ 0 ∨ (l.core.frames 0).residual v ≠ 0 ∨
      v ∈ (l.core.frames 0).active →
    l.access.degrees v = some (g.neighbors v).length)

end NearlyOptimalPPR.Computation.Supplement


