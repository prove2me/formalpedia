-- Prove2me | Definitions.Def_MinrankTW_joinTableLayout
-- name    : MinrankTW_joinTableLayout
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T12:33:09.930848+00:00
-- url     : https://prove2.me/theorems/77766fbc-ae7c-4595-b634-55565b1c00d8
-- title:
--   Record layout of a table on linear relations
-- statement:
--   The memory layout in which the integer-table clause of Proposition 1 is stated. A table $f$ assigning to every linear relation $R\le\mathbb F_q^a\oplus\mathbb F_q^c$ an integer polynomial of degree at most $d$ is stored from a base cell:
--
--   1. four header cells hold $a$, $c$, $d$ and the number $N_q(a+c)$ of records;
--   2. each record holds the codes, row by row, of a matrix in $\mathbb F_q^{(a+c)\times(a+c)}$ whose row space is $R$ (split into the first $a$ and the last $c$ coordinates), followed for $k=0,\dots,d$ by a sign cell and the absolute value of the coefficient of $z^k$ in $f(R)$;
--   3. every relation occurs in exactly one record, in any order and with any spanning matrix.
--
--   The layout does not presuppose a canonical enumeration of subspaces; building one is part of the algorithm (§A.1).
-- source:
--   Perles–Weinstein, Efficient Algorithms for Minrank and Index Coding for Low-Treewidth Graphs, STOC 2027 submission (manuscript sha256 32a91384…), Proposition 1, p.15 and Sections A.1–A.3, pp.16–17

import Mathlib
import Definitions.Def_MinrankTW_Nq

namespace MinrankTW

open Polynomial

/-!
# The RAM record layout of a table on linear relations

The layout in which Proposition 1 (Perles–Weinstein, *Efficient Algorithms for Minrank and Index Coding for Low-Treewidth Graphs*, STOC 2027 submission manuscript (sha256 32a91384…c57991), p.15: "integer polynomial tables") and §A.1–A.3
(pp.16–17) are stated as RAM computations.

**Formalization Note** A table `f` assigns to every linear relation `R ≤ F^a ⊕ F^c` an integer
polynomial of degree at most `d`. It is stored from cell `base`: cells `base, …, base + 3`
hold `a, c, d` and the number `N_q(a + c)` of records; record `r` (for `r < N_q(a + c)`)
starts at `base + 4 + r · ((a + c)² + 2(d + 1))` and holds the codes `e(σ_ij)`, row by row, of a
matrix `σ ∈ F^{(a+c)×(a+c)}` whose row space is `R` (split as `F^a ⊕ F^c` by the first `a`
and the last `c` coordinates), followed, for `k = 0, …, d`, by a sign cell (`1` if the
coefficient of `z^k` in `f(R)` is negative, else `0`) and its absolute value. Every relation
occurs in exactly one record, in any order and with any spanning matrix: the layout does not
presuppose a canonical enumeration of subspaces.
-/

variable {F : Type*} [Field F] [Fintype F]

/-- A subspace of `F^{a+c}` read as a linear relation in `F^a ⊕ F^c`. -/
def splitRel {a c : ℕ} (W : Submodule F (Fin (a + c) → F)) :
    Submodule F ((Fin a → F) × (Fin c → F)) :=
  W.map ((LinearMap.funLeft F F (Fin.castAdd c)).prod (LinearMap.funLeft F F (Fin.natAdd a)))

/-- The length of one record. -/
def recLen (a c d : ℕ) : ℕ := (a + c) * (a + c) + 2 * (d + 1)

/-- `mem` stores the table `f` (degree `≤ d`) from cell `base` in the record layout. -/
def EncodesTableAt (e : F ≃ Fin (Fintype.card F)) (mem : ℕ → ℕ) (base a c d : ℕ)
    (f : Submodule F ((Fin a → F) × (Fin c → F)) → ℤ[X]) : Prop :=
  mem base = a ∧ mem (base + 1) = c ∧ mem (base + 2) = d ∧ mem (base + 3) = Nq F (a + c) ∧
  ∃ σ : Fin (Nq F (a + c)) → Matrix (Fin (a + c)) (Fin (a + c)) F,
    Function.Bijective (fun r => splitRel (Submodule.span F (Set.range (σ r)))) ∧
    ∀ r : Fin (Nq F (a + c)),
      (∀ i j : Fin (a + c),
        mem (base + 4 + r * recLen a c d + ((i : ℕ) * (a + c) + j)) = (e (σ r i j) : ℕ)) ∧
      ∀ k : ℕ, k ≤ d →
        mem (base + 4 + r * recLen a c d + (a + c) * (a + c) + 2 * k) =
          (if (f (splitRel (Submodule.span F (Set.range (σ r))))).coeff k < 0 then 1 else 0) ∧
        mem (base + 4 + r * recLen a c d + (a + c) * (a + c) + 2 * k + 1) =
          ((f (splitRel (Submodule.span F (Set.range (σ r))))).coeff k).natAbs

end MinrankTW


