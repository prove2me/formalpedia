-- Prove2me | Definitions.Def_RandomStreamCI_CodeIntersection_Supplement_OPI
-- name    : RandomStreamCI_CodeIntersection_Supplement_OPI
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T20:44:04.203595+00:00
-- url     : https://prove2.me/theorems/672c5a8c-8a1e-48e0-b25f-f6caa6449127
-- title:
--   Polynomial coefficient outputs and OPI success
-- statement:
--   Let $F$ be a finite field, $n$ the number of coordinates, and $d$ the dimension. A coefficient tuple $x\in F^d$ denotes $f_x(X)=\sum_{j=0}^{d-1}x_jX^j$, using the published coefficient polynomial. Evaluation at the points $\alpha_i$ gives the codeword $(f_x(\alpha_i))_i$. The Reed–Solomon code is the published generalized Reed–Solomon evaluation image with all multipliers equal to one, rendered as a finite set.
--
--   For any finite code $C\subseteq\Sigma^n$, a word output succeeds at threshold $\tau$ precisely when it is in $C$ and at least $\tau$ of its oracle membership bits are one. An absent output fails. Success is averaged over independent uniform Boolean oracle and complete uniform address order; independent private coins are represented by a PMF mixture of executions. The common target is
--   $$\tau(n,d)=\left\lceil\frac n2+\frac{\sqrt{dn}}8\right\rceil.$$
--   These definitions share the base execution and score without changing CI success. The zero coefficient tuple is included. All sums and divisions inside the ceiling are real.
-- source:
--   Bouland–Ding–Jain, Exponential quantum space advantage in random data streams, STOC 2027 submission #71, preprint dated 2026-11-02, release papers-1/71.pdf, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/71.pdf, SHA256 3fe1835efedc1b9f29103379085d28d84ab1057dc30c3e3f05a8dce9f536a797, Problem 2, p. 6; (8), p. 7; (11), p. 8; Theorems 27/29, pp. 22/28

import Definitions.Def_RandomStreamCI_CodeIntersection_Branching
import Definitions.Def_QAlgorithms_Defs_ReedSolomonData

noncomputable section

namespace RandomStreamCI.CodeIntersection.Supplement

open scoped BigOperators
attribute [local instance] Classical.propDecidable

/-- Problem 2, p. 6: all polynomials of degree strictly below d, in coefficient coordinates.
The zero polynomial and polynomials of smaller degree are included. -/
abbrev Coefficients (F : Type*) (d : ℕ) := Fin d → F

/-- Evaluation of the public coefficient polynomial, (8), p. 7. -/
def evaluation {F : Type*} [Field F] {n d : ℕ} (α : Fin n → F)
    (x : Coefficients F d) : Word n F :=
  fun i => (QAlgorithms.OPI.coefficientPolynomial x).eval (α i)

/-- The source RS code, using the published general GRS evaluation image with multipliers 1.
No root-count, cardinality or decoding claim is assumed. -/
def rsCode {F : Type*} [Field F] [Fintype F] {n : ℕ}
    (α : Fin n ↪ F) (d : ℕ) (hd : d ≤ n) : Finset (Word n F) :=
  Finset.univ.filter (fun c => c ∈ QAlgorithms.ReedSolomon.grsCode α (fun _ => 1) d
    α.injective (fun _ => one_ne_zero) hd)

/-- General codeword interpretation of OPI, (6)--(8), including invalid outputs and aborts. -/
def TauValid {n : ℕ} {Alphabet : Type*} [Fintype Alphabet] [DecidableEq Alphabet]
    (C : Finset (Word n Alphabet)) (τ : ℕ) (H : Oracle n Alphabet) : Option (Word n Alphabet) → Prop
  | none => False
  | some c => c ∈ C ∧ τ ≤ value H c Finset.univ

/-- Actual success over independent uniform oracle and complete random ordering. -/
def tauSuccess {n w : ℕ} {Alphabet : Type*} [Fintype Alphabet] [DecidableEq Alphabet]
    (B : BranchingProgram n Alphabet w) (C : Finset (Word n Alphabet)) (τ : ℕ) : ℝ :=
  streamProbability (fun ω => TauValid C τ ω.1
    (B.output (B.state ω (Fintype.card (Address n Alphabet)))))

/-- Independent private random coins: a finite mixture of actual deterministic executions. -/
def randomizedTauSuccess {n w : ℕ} {Alphabet Ω : Type*} [Fintype Alphabet] [DecidableEq Alphabet]
    [Fintype Ω] (p : PMF Ω) (B : Ω → BranchingProgram n Alphabet w)
    (C : Finset (Word n Alphabet)) (τ : ℕ) : ℝ :=
  ∑ ω, weights p ω * tauSuccess (B ω) C τ

/-- The exact target in Theorems 27 and 29: real division, radical, then natural ceiling. -/
def target (n d : ℕ) : ℕ := ⌈(n : ℝ) / 2 + Real.sqrt ((d : ℝ) * n) / 8⌉₊

end RandomStreamCI.CodeIntersection.Supplement


