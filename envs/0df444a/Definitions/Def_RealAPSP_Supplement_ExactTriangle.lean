-- Prove2me | Definitions.Def_RealAPSP_Supplement_ExactTriangle
-- name    : RealAPSP_Supplement_ExactTriangle
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T04:02:47.273274+00:00
-- url     : https://prove2.me/theorems/94c811f5-2b8e-490e-9f79-f2789bada0f3
-- title:
--   Integer and Real Exact Triangle with $\bot$, and their time classes
-- statement:
--   Let $A,B,C$ be $n\times n$ matrices whose entries are reals (or integers) or the dummy symbol $\bot$ for a missing value. A triple $(i,k,j)\in[n]^3$ is an **exact triangle** if all three entries $A[i,k]$, $B[k,j]$, $C[i,j]$ are present and
--
--   $$A[i,k]+B[k,j]+C[i,j]=0 .$$
--
--   A triple with a $\bot$ entry is never an exact triangle. **Exact Triangle** asks whether an exact triangle exists (Problems 3.5 and 3.6); an algorithm answers in integer output cell $0$, with $1$ for yes and $0$ for no.
--
--   Two time classes are defined on the base mission's comparison-addition machine.
--
--   1. **Integer Exact Triangle in time $O(n^{3-\epsilon}(\log(u+2))^d)$.** There are one deterministic program and a constant $\kappa$ such that for every $n\ge1$, every $u\ge0$ and all integer matrices with $\bot$ allowed and weights in $\{-u,\dots,u\}$, the program, given $n$, $u$, the presence flags and the weights, answers correctly within $\kappa\,n^{3-\epsilon}(\log(u+2))^d$ steps, with words of $O(\log((n+2)(u+2)))$ bits.
--   2. **Real Exact Triangle in time $O(n^r)$, correct with high probability.** For every failure exponent $a$ there are a program and a constant $\kappa$ such that for every $n\ge1$ and all real matrices with $\bot$ allowed, the program, given $n$ and the flags as integers and the entries as reals, halts within $\kappa\,n^r$ steps on every sequence of coin flips and answers correctly with probability at least $1-n^{-a}$, with words of $O(\log n)$ bits.
--
--   These are the hypothesis and the conclusion of Theorem 1.3, the real-to-integer reduction for Exact Triangle.
--
--   **Formalization Note** The exact triangle is the base mission's $0$-approximate triangle `IsApproxTri 0`. The two classes copy the base mission's Negative Triangle classes `IntNegTriDecided` and `RealNegTriSolved` word for word, with the exact-triangle answer in place of the negative-triangle one. The page's $(\log u)^{O(1)}$ vanishes at $u=1$, so the bound uses $\log(u+2)$.
-- source:
--   Fischer, Polak, Schmidt, Real-to-Integer Reduction for All-Pairs Shortest Paths, arXiv:2611.04847 (held file sha256 a3dc0096…), §3.2, Problems 3.5, 3.6 and the ⊥ convention, p.10 (PDF p.12); Theorem 1.3, p.2 (PDF p.4)

import Mathlib
import Definitions.Def_RealAPSP_Problems

namespace RealAPSP

namespace Supplement

/-!
# Integer and Real Exact Triangle with ⊥, and their time classes

Fischer, Polak, Schmidt, *Real-to-Integer Reduction for All-Pairs Shortest Paths*, arXiv:2611.04847 (held file
sha256 a3dc0096…), §3.2, p.10 (PDF p.12): "Problem 3.5 (Integer Exact Triangle). Given three n × n matrices
A, B, C ∈ Z^{n×n}, decide if there exist i, k, j ∈ [n] such that A[i, k] + B[k, j] + C[i, j] = 0. Problem 3.6 (Real
Exact Triangle). … R^{n×n} …"; "For the integer variants we throughout assume that the weights are from the universe
{−u, . . . , u}. Throughout the paper we also allow integer and real instances of any of the defined problem to contain
missing values replaced by a dummy symbol ⊥." Theorem 1.3, p.2 (PDF p.4), for the time bounds.

**Formalization Note.**
* **Exact triangle.** A triple `(i, k, j)` is an exact triangle when its three entries are present and sum to `0`:
  the published `RealAPSP.IsApproxTri 0`. A triple with a ⊥ entry is never a solution.
* **Answer.** Output cell `0` holds `1` if an exact triangle exists and `0` otherwise, as for the published
  `RealAPSP.DecidesNegTri`.
* **Integer side.** `IntExactTriDecided ε d` is the published `RealAPSP.IntNegTriDecided ε d` with the exact-triangle
  answer in place of the negative-triangle one: one deterministic program (a run on the all-false coin tape) for all
  `n ≥ 1` and all `u`, ⊥ allowed, weights from `{−u, …, u}`, word bound `((n+2)(u+2))^c`, time
  `κ·n^{3−ε}·(log(u+2))^d`. The page's `(log u)^{O(1)}` is `0` at `u = 1`; `log(u+2)` keeps the bound positive.
* **Real side.** `RealExactTriSolved r` is the published `RealAPSP.RealNegTriSolved r` with the exact-triangle answer:
  for every failure exponent `a` a program and a time constant `κ`, word bound `(n+2)^c` independent of the weights,
  time `κ·n^r`, success probability at least `1 − n^{−a}`, ⊥ allowed.
-/

/-- The answer of Exact Triangle, at output cell `0`: `1` if an exact triangle exists, else `0`. -/
def DecidesExactTri {n : ℕ} (A B C : Mat ℝ n) (σ : State) : Prop :=
  ((∃ i k j, IsApproxTri 0 A B C i k j) → σ.imem (outCell 0) = 1) ∧
    ((¬ ∃ i k j, IsApproxTri 0 A B C i k j) → σ.imem (outCell 0) = 0)

/-- Integer Exact Triangle, with ⊥ allowed and weights from `{−u, …, u}`, is decided in time
`O(n^{3−ε} (log(u+2))^d)` by one deterministic program for all `n ≥ 1` and all `u`. -/
def IntExactTriDecided (ε : ℝ) (d : ℕ) : Prop :=
  ∃ (P : Program) (κ : ℝ), ∀ (n : ℕ), 1 ≤ n → ∀ (u : ℕ) (X Y Z : Mat ℤ n),
    WeightsBounded u X → WeightsBounded u Y → WeightsBounded u Z →
    Runs P ((n + 2) * (u + 2)) (intTriInts [(n : ℤ), (u : ℤ)] X Y Z) []
      (κ * (n : ℝ) ^ (3 - ε) * Real.log ((u : ℝ) + 2) ^ d)
      (DecidesExactTri (castMat X) (castMat Y) (castMat Z))

/-- Real Exact Triangle, with ⊥ allowed, is decided in time `O(n^r)` by a randomized algorithm correct with high
probability: for every failure exponent `a` there is a program. -/
def RealExactTriSolved (r : ℝ) : Prop :=
  ∀ a : ℕ, ∃ (P : Program) (κ : ℝ), ∀ (n : ℕ), 1 ≤ n → ∀ A B C : Mat ℝ n,
    RunsWhp P (n + 2) (triInts [(n : ℤ)] A B C) (triReals [] A B C)
      (κ * (n : ℝ) ^ r) ((n : ℝ) ^ (-(a : ℝ))) (DecidesExactTri A B C)

end Supplement

end RealAPSP


