-- Prove2me | Definitions.Def_RealAPSP_Problems
-- name    : RealAPSP_Problems
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T20:58:08.1835+00:00
-- url     : https://prove2.me/theorems/6b5c6178-1647-4f86-9e90-9706dd015ca9
-- title:
--   Integer and Real APSP and Negative Triangle in a stated time bound
-- statement:
--   For a directed graph $w$ given as an adjacency matrix with $\bot$ for a non-edge, the distance $d_w(i,j)$ is the infimum of the weights of all walks from $i$ to $j$, and is $+\infty$ when there is no walk. No negative cycles means that every closed walk has nonnegative weight; then the infimum is attained.
--
--   **Integer APSP in time $O(n^{3-\varepsilon}(\log(u+2))^d)$** asserts one deterministic program that, for all $n\ge1$, all $u$ and all such graphs with weights in $\{-u,\dots,u\}$, with word bound $((n+2)(u+2))^c$, writes for each pair a reachability flag and the distance.
--
--   **Real APSP in time $O(n^r)$** asserts that for each failure exponent $a$ there is a program that, with word bound $(n+2)^c$, on real weights in the real bank, halts within $\kappa n^r$ steps on every coin tape and writes the flags and the distances with probability at least $1-n^{-a}$.
--
--   Integer and Real Negative Triangle are decision problems of the same two shapes, with $\bot$ allowed.
--
--   These predicates are the two sides of Theorem 1.1.
--
--   **Formalization Note** The word bound on the integer side depends on $u$, so weights fit in one word and the assumption is as weak as the page's. The logarithm is $\log(u+2)$ because $(\log u)^{d}=0$ at $u=1$.
-- source:
--   Fischer, Polak, Schmidt, Real-to-Integer Reduction for All-Pairs Shortest Paths, arXiv:2611.04847 (held file sha256 a3dc0096…), Problems 3.1–3.4, p.10 (PDF p.12); §3.1, p.9 (PDF p.11)

import Mathlib
import Definitions.Def_RealAPSP_Triangles

namespace RealAPSP

/-!
# Integer and Real APSP, Integer and Real Negative Triangle, on the machine

Fischer, Polak, Schmidt, arXiv:2611.04847 (held file sha256 a3dc0096…), §3.2, p.10 (PDF p.12): "Problem 3.1 (Integer
APSP). Given a directed graph with integer edge weights and no negative cycles, compute the length of a shortest
path from u to v for every pair of vertices (u, v). Problem 3.2 (Real APSP). … real edge weights …"; Problems 3.3,
3.4 (Negative Triangle); §3.1, p.9 (high probability, "at least 1 − n^{−c} … a constant which we can choose as
large as required").

**Formalization Note.**
* **Graph.** A directed graph is an adjacency matrix with ⊥ for a non-edge, so there are no parallel arcs and a
  time bound in `n` alone is meaningful. Self-loops and negative edges are allowed.
* **Distance.** `dist` is the infimum, in `EReal`, of the weights of all walks; it is `⊤` when there is no walk, and
  under `NoNegCycle` it is attained by a walk.
* **Integer side.** Weights are given in cells with `u` in a cell, and the word bound is `((n+2)(u+2))^c`, so
  weights fit in one word for every `u`, with a single program for all `u`. The hypothesis of Theorem 1.1 is
  deterministic: the run is on the all-false tape.
* **`log(u+2)`.** The page's `(log u)^{O(1)}` is `0` at `u = 1`; `log(u+2)` keeps the bound positive at `u = 0, 1`.
* **Real side.** The word bound is `(n+2)^c`, independent of the weights. The failure exponent `a` is chosen after
  the saving and before the program, as on p.9.
-/

/-- `w` has a walk from `i` to `j` of weight `e`. -/
inductive IsWalk {n : ℕ} (w : Mat ℝ n) : Fin n → Fin n → ℝ → Prop
  | nil (i : Fin n) : IsWalk w i i 0
  | cons {i j k : Fin n} {d e : ℝ} : w i j = some d → IsWalk w j k e → IsWalk w i k (d + e)

/-- No negative cycles: every closed walk has nonnegative weight. -/
def NoNegCycle {n : ℕ} (w : Mat ℝ n) : Prop := ∀ i d, IsWalk w i i d → 0 ≤ d

/-- The length of a shortest walk from `i` to `j`, `⊤` when there is none. -/
noncomputable def dist {n : ℕ} (w : Mat ℝ n) (i j : Fin n) : EReal :=
  ⨅ (e : ℝ) (_ : IsWalk w i j e), (e : EReal)

/-- The output of Integer APSP: for `k = i·n + j`, cell `2k` is the reachability flag and cell `2k+1` the distance. -/
def IntAPSPOutput {n : ℕ} (w : Mat ℤ n) (σ : State) : Prop :=
  ∀ i j : Fin n,
    (dist (castMat w) i j ≠ ⊤ →
      σ.imem (outCell (2 * ((i : ℕ) * n + j))) = 1 ∧
      (((σ.imem (outCell (2 * ((i : ℕ) * n + j) + 1)) : ℤ) : ℝ) : EReal) = dist (castMat w) i j) ∧
    (dist (castMat w) i j = ⊤ → σ.imem (outCell (2 * ((i : ℕ) * n + j))) = 0)

/-- The output of Real APSP: for `k = i·n + j`, integer cell `k` is the flag and real cell `k` the distance. -/
def RealAPSPOutput {n : ℕ} (w : Mat ℝ n) (σ : State) : Prop :=
  ∀ i j : Fin n,
    (dist w i j ≠ ⊤ →
      σ.imem (outCell ((i : ℕ) * n + j)) = 1 ∧
      ((σ.rmem (routCell ((i : ℕ) * n + j)) : ℝ) : EReal) = dist w i j) ∧
    (dist w i j = ⊤ → σ.imem (outCell ((i : ℕ) * n + j)) = 0)

/-- All weights of `w` lie in `{−u, …, u}`. -/
def WeightsBounded {n : ℕ} (u : ℕ) (w : Mat ℤ n) : Prop :=
  ∀ i j z, w i j = some z → |z| ≤ (u : ℤ)

/-- Integer APSP with weights from `{−u, …, u}` is solved in time `O(n^{3−ε} (log(u+2))^d)`, by one deterministic
program for all `n ≥ 1` and all `u`. Input: `n`, `u`, the flags, the weights. -/
def IntegerAPSPSolved (ε : ℝ) (d : ℕ) : Prop :=
  ∃ (P : Program) (κ : ℝ), ∀ (n : ℕ), 1 ≤ n → ∀ (u : ℕ) (w : Mat ℤ n),
    WeightsBounded u w → NoNegCycle (castMat w) →
    Runs P ((n + 2) * (u + 2)) ([(n : ℤ), (u : ℤ)] ++ flagCells w ++ valueCells w) []
      (κ * (n : ℝ) ^ (3 - ε) * Real.log ((u : ℝ) + 2) ^ d) (IntAPSPOutput w)

/-- Real APSP is solved in time `O(n^r)` by a randomized algorithm correct with high probability: for every failure
exponent `a` there is a program. Input: `n`, the flags, and in the real bank the weights. -/
def RealAPSPSolved (r : ℝ) : Prop :=
  ∀ a : ℕ, ∃ (P : Program) (κ : ℝ), ∀ (n : ℕ), 1 ≤ n → ∀ w : Mat ℝ n, NoNegCycle w →
    RunsWhp P (n + 2) ([(n : ℤ)] ++ flagCells w) (valueCells w)
      (κ * (n : ℝ) ^ r) ((n : ℝ) ^ (-(a : ℝ))) (RealAPSPOutput w)

/-- The answer of Negative Triangle, at output cell `0`: `1` if a negative triangle exists, else `0`. -/
def DecidesNegTri {n : ℕ} (A B C : Mat ℝ n) (σ : State) : Prop :=
  ((∃ i k j, IsNegTri A B C i k j) → σ.imem (outCell 0) = 1) ∧
    ((¬ ∃ i k j, IsNegTri A B C i k j) → σ.imem (outCell 0) = 0)

/-- Integer Negative Triangle, with ⊥ allowed and weights from `{−u, …, u}`, is decided in time
`O(n^{3−ε} (log(u+2))^d)` by one deterministic program. -/
def IntNegTriDecided (ε : ℝ) (d : ℕ) : Prop :=
  ∃ (P : Program) (κ : ℝ), ∀ (n : ℕ), 1 ≤ n → ∀ (u : ℕ) (X Y Z : Mat ℤ n),
    WeightsBounded u X → WeightsBounded u Y → WeightsBounded u Z →
    Runs P ((n + 2) * (u + 2)) (intTriInts [(n : ℤ), (u : ℤ)] X Y Z) []
      (κ * (n : ℝ) ^ (3 - ε) * Real.log ((u : ℝ) + 2) ^ d)
      (DecidesNegTri (castMat X) (castMat Y) (castMat Z))

/-- Real Negative Triangle, with ⊥ allowed, is decided in time `O(n^r)` by a randomized algorithm correct with
high probability. -/
def RealNegTriSolved (r : ℝ) : Prop :=
  ∀ a : ℕ, ∃ (P : Program) (κ : ℝ), ∀ (n : ℕ), 1 ≤ n → ∀ A B C : Mat ℝ n,
    RunsWhp P (n + 2) (triInts [(n : ℤ)] A B C) (triReals [] A B C)
      (κ * (n : ℝ) ^ r) ((n : ℝ) ^ (-(a : ℝ))) (DecidesNegTri A B C)

end RealAPSP


