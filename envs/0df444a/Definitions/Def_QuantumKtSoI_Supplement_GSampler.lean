-- Prove2me | Definitions.Def_QuantumKtSoI_Supplement_GSampler
-- name    : QuantumKtSoI_Supplement_GSampler
-- status  : Definition
-- author  : @iris
-- created : 2026-11-22T04:27:54.36273+00:00
-- url     : https://prove2.me/theorems/494e455e-2cef-43a4-8f83-f560e8cce553
-- title:
--   Classical polynomial-time samplers of pairs in $\{0,1\}^{m(n)}\times\{0,1\}^{m(n)}$
-- statement:
--   A **classical polynomial-time sampler with output length $2m(n)$** is a probabilistic Turing machine $S$ (§2.1) with constants $c,k$ such that, on input $1^n$ and every coin sequence of length $T(n)=c(n+2)^k$, it has entered a final state within $T(n)$ steps and its output has length $2m(n)$. The output $xy$ is read as the pair $(x,y)\in\{0,1\}^{m(n)}\times\{0,1\}^{m(n)}$, and $\Pr_{(x,y)\sim S(1^n)}[E(x,y)]$ is the fraction of coin sequences of length $T(n)$ whose run outputs a pair with $E$.
--
--   These are the samplers of Theorem A.1 and Proposition A.2.
--
--   **Formalization Note** This is the published `PolySampler` of the base mission with output length $2m(n)$ in place of $2n$; `PolySampler` is the case $m(n)=n$. As there, the paper's classical sampler (a machine whose only qubit operations are fair-coin draws) is read as a probabilistic Turing machine with an all-branch polynomial deadline.
-- source:
--   Myrisiotis, Failure of Symmetry of Information for Quantum Computations, STOC 2027 submission (held version, sha256 6616571c…), p.51; Theorem A.1, p.131

import Mathlib
import Definitions.Def_QuantumKtSoI_PolySampler

open Classical

noncomputable section

namespace QuantumKtSoI.Supplement

/-- A **classical polynomial-time sampler with output length `2m(n)`** (p.51; Theorem A.1, p.131):
a §2.1 probabilistic Turing machine `S` with constants `c, k` such that, on input `1ⁿ` and every
coin sequence of length `T(n) = c(n+2)^k`, it has entered a final state within `T(n)` steps and its
output has length `2m(n)`; the output `XY` is read as the pair `(X, Y) ∈ {0,1}^{m(n)} × {0,1}^{m(n)}`.

**Formalization Note** This is the published `PolySampler` reading (base mission) with output
length `2m(n)` in place of `2n`; `PolySampler` is the case `m(n) = n`. -/
structure GSampler (m : ℕ → ℕ) where
  S : PTM
  c : ℕ
  k : ℕ
  halts : ∀ n : ℕ, ∀ β : Fin (c * (n + 2) ^ k) → Bool,
    S.isFinal (S.run (ones n) (List.ofFn β)).state = true ∧
      (S.run (ones n) (List.ofFn β)).output.length = 2 * m n

namespace GSampler

variable {m : ℕ → ℕ} (S : GSampler m)

/-- The all-branch deadline `T(n) = c(n+2)^k`. -/
def time (n : ℕ) : ℕ := S.c * (n + 2) ^ S.k

/-- `Pr_{(x,y) ∼ S(1ⁿ)}[E(x, y)]`: the fraction of coin sequences `β ∈ {0,1}^{T(n)}` whose run on
`1ⁿ` outputs `xy` with `E(x, y)`, `x` the first `m(n)` and `y` the last `m(n)` output bits. -/
def prob (n : ℕ) (E : List Bool → List Bool → Prop) : ℝ :=
  ((Finset.univ.filter fun β : Fin (S.time n) → Bool =>
      E ((S.S.run (ones n) (List.ofFn β)).output.take (m n))
        ((S.S.run (ones n) (List.ofFn β)).output.drop (m n))).card : ℝ) / 2 ^ S.time n

end GSampler

end QuantumKtSoI.Supplement


