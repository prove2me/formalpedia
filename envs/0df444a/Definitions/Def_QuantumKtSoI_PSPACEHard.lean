-- Prove2me | Definitions.Def_QuantumKtSoI_PSPACEHard
-- name    : QuantumKtSoI_PSPACEHard
-- status  : Definition
-- author  : @iris
-- created : 2026-11-11T08:38:13.741371+00:00
-- url     : https://prove2.me/theorems/d4af6739-dfea-4c66-abf9-5f0530427d01
-- title:
--   PSPACE, polynomial-time many-one reductions, PSPACE-hardness, and deciding within a time bound
-- statement:
--   1. A language $L\subseteq\{0,1\}^*$ is in **PSPACE** (§2.4) if a deterministic machine (a valid coded machine without gate states) with a read-only input tape and an output tape whose head never moves left halts on every input $x$ with output $[x\in L]$ using at most $c(|x|+2)^k$ cells of its other tapes, for constants $c,k$.
--   2. A **many-one reduction** from $L$ to $L'$ (p.18) is a total function $f$ computed by such a deterministic machine within $c(|x|+2)^k$ steps with $x\in L\iff f(x)\in L'$.
--   3. $L$ is **PSPACE-hard** if every language in PSPACE reduces to it.
--   4. A machine **decides** $L$ within $T$ steps on large inputs (p.22) if for some $n_0$ and every $x$ with $|x|\ge n_0$ it halts within $\lfloor T(|x|)\rfloor$ steps on every branch and outputs the single bit $1$ with probability at least $2/3$ if $x\in L$ and at most $1/3$ if $x\notin L$.
--
--   These are used in Theorem 6.18, whose hypothesis is a fast quantum decider for a PSPACE-complete language.
--
--   **Formalization Note** Space is counted as $\sum_t(b_t+1)$ for bounds $b_t$ on the head positions of the work tapes on every branch at every time; heads start on cell $0$, stay on nonnegative cells and move one cell per step, so this is the number of cells visited.
-- source:
--   Myrisiotis, Failure of Symmetry of Information for Quantum Computations, STOC 2027 submission (held version, sha256 6616571c…), §2.4, p.17; p.18; p.22; Theorem 2.4, p.19

import Mathlib
import Definitions.Def_QuantumKtSoI_Machine_outputProb
import Definitions.Def_QuantumKtSoI_CodedMachine

open Classical

noncomputable section

namespace QuantumKtSoI

/-- The machine `B` **decides** the language `L` **within `T` steps on every sufficiently large
input length** (BQTIME convention, p.22; promise convention, p.17): for some `n₀` and every `x`
with `|x| ≥ n₀`, `B` halts within `⌊T(|x|)⌋` steps on every branch on `x`, and outputs the single
bit `1` with probability at least `2/3` if `x ∈ L` and at most `1/3` if `x ∉ L`, every other
output counting as rejection. -/
def DecidesWithin (B : CodedMachine) (L : Set (List Bool)) (T : ℕ → ℝ) : Prop :=
  ∃ n₀ : ℕ, ∀ x : List Bool, n₀ ≤ x.length →
    B.toMachine.HaltsWithin x ⌊T x.length⌋₊ ∧
      (x ∈ L → (2 / 3 : ℝ) ≤ B.toMachine.outputProb x ⌊T x.length⌋₊ [true]) ∧
      (x ∉ L → B.toMachine.outputProb x ⌊T x.length⌋₊ [true] ≤ 1 / 3)

/-- On input `x` the machine `A` uses at most `S` cells of its tapes other than the input and
output tapes: there are bounds `b t` on the head positions of those tapes on every branch at every
time with `Σ_t (b t + 1) ≤ S` (heads start at cell `0`, stay at cells `≥ 0` and move by one cell
per step, so the cells visited on tape `t` are `0, …, max head index`). -/
def UsesSpace (A : Machine) (x : List Bool) (S : ℕ) : Prop :=
  ∃ b : A.T → ℕ,
    (∑ t ∈ Finset.univ.filter (fun t => t ≠ A.inT ∧ t ≠ A.outT), (b t + 1)) ≤ S ∧
      ∀ s, ∀ ρ ∈ A.recSeqs x s, ∀ C ∈ (A.branch x ρ).support, ∀ t,
        t ≠ A.inT → t ≠ A.outT → C.head t ≤ (b t : ℤ)

/-- **PSPACE** (§2.4, p.17): `L` is decided by a deterministic multi-tape machine (a valid coded
machine without gate states) with a read-only input tape and an output tape whose head never
moves left, which halts on every input `x` with output `[x ∈ L]` using `O(|x|^c)` cells of its
other tapes, written `c'·(|x|+2)^k`. -/
def InPSPACE (L : Set (List Bool)) : Prop :=
  ∃ A : CodedMachine, A.Valid ∧ A.GateFree ∧
    (∀ p, A.toMachine.IsClassical p → ∀ σ, A.toMachine.Legal p σ →
      (A.toMachine.δ p (A.toMachine.mask p σ)).2.2 A.toMachine.outT ≠ Move.L) ∧
    ∃ c k : ℕ, ∀ x : List Bool,
      (∃ t, A.toMachine.HaltsWithin x t ∧
        A.toMachine.outputProb x t [decide (x ∈ L)] = 1) ∧
      UsesSpace A.toMachine x (c * (x.length + 2) ^ k)

/-- A **deterministic polynomial-time many-one reduction** from `L` to `L'` (p.18): a total
function `f`, computed on input `x` by a deterministic machine (a valid coded machine without gate
states) within `c(|x|+2)^k` steps, with `x ∈ L ↔ f x ∈ L'` for every `x`. -/
def PolyReduction (L L' : Set (List Bool)) : Prop :=
  ∃ f : List Bool → List Bool, (∀ x, x ∈ L ↔ f x ∈ L') ∧
    ∃ F : CodedMachine, F.Valid ∧ F.GateFree ∧ ∃ c k : ℕ, ∀ x : List Bool,
      F.toMachine.HaltsWithin x (c * (x.length + 2) ^ k) ∧
        F.toMachine.outputProb x (c * (x.length + 2) ^ k) (f x) = 1

/-- `L` is **PSPACE-hard** under deterministic polynomial-time many-one reductions: every
language in PSPACE reduces to `L` (Theorem 2.4, p.19, for `L⋆`). -/
def PSPACEHard (L : Set (List Bool)) : Prop :=
  ∀ L' : Set (List Bool), InPSPACE L' → PolyReduction L' L

end QuantumKtSoI


