-- Prove2me | Definitions.Def_ClassicalSchurLift
-- name    : ClassicalSchurLift
-- status  : Definition
-- author  : @mysticflounder
-- created : 2026-09-26T21:18:23.195985+00:00
-- url     : https://prove2.me/theorems/894d2199-1e4c-42c6-992a-2bc2bed7b398
-- title:
--   Sets sumfree in a group, and the jump sequence $\Delta X$ of the grid $X = \{u + Mj\}$
-- statement:
--   This bundle defines the objects of the lift from the group $\mathbb{Z}_{m_1} \times \mathbb{Z}_{m_2}$ to block-sum sets (Lemma 3 of the note).
--
--   1. Let $G$ be a set with an addition; in the mission $G = \mathbb{Z}_{m_1} \times \mathbb{Z}_{m_2}$, where $\mathbb{Z}_m$ denotes the integers modulo $m$. A subset $S \subseteq G$ is **sumfree in $G$** (Lean `GroupSumFree`) if $x + y \notin S$ for all $x, y \in S$, with the sum taken in $G$ and $x = y$ allowed.
--   2. For $m_1, M, L \in \mathbb{N}$ put (Lean `liftPrefix m₁ M L`) $x_L = (L \bmod m_1) + M \lfloor L/m_1 \rfloor$. If $L = j m_1 + u$ with $0 \le u \le m_1 - 1$, then $x_L = u + Mj$.
--   3. For $m_1, m_2, M \in \mathbb{N}$, the **lifted sequence** (Lean `liftSeq m₁ m₂ M`) is the sequence of the $m_1 m_2 - 1$ successive differences of $x_0, x_1, \dots, x_{m_1 m_2 - 1}$:
--
--   $$
--   A = \bigl(x_1 - x_0,\ x_2 - x_1,\ \dots,\ x_{m_1 m_2 - 1} - x_{m_1 m_2 - 2}\bigr).
--   $$
--
--   When $m_1 \ge 1$ and $M \ge m_1$, the numbers $x_0 < x_1 < \dots < x_{m_1 m_2 - 1}$ are the elements, in increasing order, of the grid
--
--   $$
--   X = \{\, u + Mj : 0 \le u \le m_1 - 1,\ 0 \le j \le m_2 - 1 \,\},
--   $$
--
--   and $A = \Delta X$ is the sequence of successive jumps of $X$ in the sense of Definition 2.6 of Eliahou and Revuelta. It consists of $m_2$ runs of $m_1 - 1$ entries equal to $1$, separated by $m_2 - 1$ entries equal to $M - m_1 + 1$. For example, $m_1 = m_2 = 7$ and $M = 19$ give seven runs of six entries $1$ separated by six entries $13$: a sequence of length $48$ and sum $120$.
--
--   The lift turns a cover of the nonzero elements of $\mathbb{Z}_{m_1} \times \mathbb{Z}_{m_2}$ by sets that are sumfree in the group into a sequence of positive integers whose block sums have small Schur degree and whose prefix averages are bounded. It is the source of the lower bound $L(5) \ge 49$.
--
--   **Formalization Note** The predicate `GroupSumFree` is stated for any type with an addition, and $\mathbb{Z}_m$ is Mathlib's `ZMod m`. `liftPrefix` and `liftSeq` are defined for all parameters: the differences use truncated subtraction on $\mathbb{N}$, the length $m_1 m_2 - 1$ is $0$ when $m_1 m_2 = 0$, and for $m_1 = 0$ Lean's conventions $L \bmod 0 = L$ and $\lfloor L/0 \rfloor = 0$ apply. The theorems of the mission use them only with $m_1 \ge 1$ and $M \ge m_1$, where the description as $\Delta X$ holds.
-- source:
--   S. Eliahou and M. P. Revuelta, "The Schur degree of additive sets", Discrete Math. 344(5) (2021) 112332, https://doi.org/10.1016/j.disc.2021.112332 (preprint arXiv:2006.01502), Definition 2.6 (the sequence ΔX of successive jumps of a finite set X ⊂ ℤ). A. McKenna, "The Schur degree of block sums: L(4) = 16 and L(5) ≥ 49", Zenodo (2026), https://doi.org/10.5281/zenodo.22987189, §4 (sets sumfree in an abelian group; Lemma 4.1: the grid X = {u + M·j} and A = ΔX). Lean source: https://github.com/mysticflounder/schur-degree-block-sums/blob/v1.0.1/lean/ClassicalSchur/Lift.lean#L25-L35 (release v1.0.1, doi:10.5281/zenodo.22987688).

-- Generated from lean/ClassicalSchur/Lift.lean by skeleton
-- subtraction: every declaration except the def-material below is deleted,
-- and project imports are rewritten to their platform Definitions bundles.
import Mathlib

namespace ClassicalSchur



/-- A subset of an additive group is sumfree in the group when it has no
`x, y, z` with `x + y = z` (`x = y` allowed). -/
def GroupSumFree {G : Type*} [Add G] (S : Set G) : Prop := ∀ x ∈ S, ∀ y ∈ S, x + y ∉ S

/-- The `L`-th element, in increasing order, of `X = {u + M·j}`: with
`L = j·m₁ + u` and `u < m₁` it is `u + M·j`. -/
def liftPrefix (m₁ M L : ℕ) : ℕ := L % m₁ + M * (L / m₁)

/-- The sequence `A = ΔX` of jumps of `X = {u + M·j : u < m₁, j < m₂}`. -/
def liftSeq (m₁ m₂ M : ℕ) : List ℕ :=
  (List.range (m₁ * m₂ - 1)).map fun k => liftPrefix m₁ M (k + 1) - liftPrefix m₁ M k

end ClassicalSchur


