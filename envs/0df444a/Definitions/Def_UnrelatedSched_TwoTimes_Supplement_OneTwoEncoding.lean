-- Prove2me | Definitions.Def_UnrelatedSched_TwoTimes_Supplement_OneTwoEncoding
-- name    : UnrelatedSched_TwoTimes_Supplement_OneTwoEncoding
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T12:43:08.010396+00:00
-- url     : https://prove2.me/theorems/fa3656c3-f3a9-421c-b9b0-ed09732a87d0
-- title:
--   Instances with processing times in $\{1,2\}$ and their bit-string encodings (Theorem 6)
-- statement:
--   This file fixes the data of Theorem 6 of Lenstra, Shmoys and Tardos and how that data is written as a bit string, so that a running time can be measured.
--
--   **Instances.** There are $m$ machines $0,\dots,m-1$ and $n$ jobs $0,\dots,n-1$; job $j$ needs $p_{ij}$ time units on machine $i$. The matrix $P=(p_{ij})$ is a **$\{1,2\}$ matrix** if
--
--   $$p_{ij}\in\{1,2\}\qquad\text{for every machine } i \text{ and every job } j,$$
--
--   each entry being chosen independently.
--
--   **Input encoding.** The instance $(m,n,P)$ is written as the bit string consisting of $m$ ones, a zero, $n$ ones, a zero, and then the $mn$ entries of $P$ row by row (machine $0$ first; within a machine, job $0$ first), one bit per entry: $0$ for $p_{ij}=1$ and $1$ for $p_{ij}=2$. On a $\{1,2\}$ matrix this string determines $m$, $n$ and $P$, and its length is $m+n+mn+2$.
--
--   **Output encoding.** A schedule $\sigma$, which runs job $j$ on machine $\sigma(j)$, is written as the concatenation over $j=0,\dots,n-1$ of $\sigma(j)$ ones followed by a zero. Given $n$ it determines $\sigma$, and its length is at most $nm$.
--
--   These encodings give Theorem 6's phrase "solvable in polynomial time" a concrete input and output on which a Turing machine's running time is counted.
--
--   **Formalization Note** Machines are `Fin m`, jobs `Fin n` and processing times natural numbers; the indicator bit of an entry is `decide (P i j = 2)`. The encoding is meant for $\{1,2\}$ matrices only: on other matrices it forgets every entry except whether it equals $2$. The numbers $m$ and $n$ are written in unary; since the matrix is part of the input, this changes the input length by at most a constant factor whenever $n\ge 1$.
-- source:
--   Lenstra, Shmoys, Tardos, Approximation algorithms for scheduling unrelated parallel machines, CWI Report OS-R8714 (1987), p. 2, §1 (the scheduling model), and p. 8, §5, Theorem 6 (processing times in {1, 2})

import Mathlib

namespace UnrelatedSched.TwoTimes.Supplement

/-- The processing-time matrix `P` (machines `Fin m`, jobs `Fin n`) has every entry in `{1, 2}`
(Lenstra, Shmoys, Tardos, CWI Report OS-R8714 (1987), §5, Theorem 6, p. 8). Each entry is
constrained independently. -/
def IsOneTwoMatrix {m n : ℕ} (P : Matrix (Fin m) (Fin n) ℕ) : Prop :=
  ∀ i j, P i j = 1 ∨ P i j = 2

/-- The binary input encoding of a scheduling instance with processing times in `{1, 2}`:
the number of machines `m` in unary (`m` copies of `true`), a separator `false`, the number of jobs
`n` in unary, a separator `false`, and then the `m * n` entries of `P` in row-major order
(machine `0` first, then within a machine job `0` first), one bit each: `false` for `P i j = 1`
and `true` for `P i j = 2`. On a `{1, 2}` matrix this determines `m`, `n` and `P`, and its length
is `m + n + m * n + 2`. -/
def encodeInstance {m n : ℕ} (P : Matrix (Fin m) (Fin n) ℕ) : List Bool :=
  List.replicate m true ++ [false] ++ List.replicate n true ++ [false] ++
    (List.ofFn fun i : Fin m => List.ofFn fun j : Fin n => decide (P i j = 2)).flatten

/-- The binary output encoding of a schedule `σ : Fin n → Fin m` (job `j` runs on machine `σ j`):
for each job `j = 0, …, n - 1` in turn, the machine index `σ j` in unary (`σ j` copies of `true`)
followed by a separator `false`. It determines `σ` (given `n`), and its length is at most
`n * m`. -/
def encodeSchedule {m n : ℕ} (σ : Fin n → Fin m) : List Bool :=
  (List.ofFn fun j : Fin n => List.replicate (σ j : ℕ) true ++ [false]).flatten

end UnrelatedSched.TwoTimes.Supplement


