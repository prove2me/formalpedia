-- Prove2me | Definitions.Def_SoftmaxAttnFD_RatEnc
-- name    : SoftmaxAttnFD_RatEnc
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:01:34.317147+00:00
-- url     : https://prove2.me/theorems/b7cc1a3e-829e-4ca8-8354-2ed1bbd1b195
-- title:
--   Encoded rationals and memory layout helpers
-- statement:
--   A rational input is an encoded triple: a sign, a numerator $\mathrm{num}\in\mathbb N$ and a denominator $\mathrm{den}\ge 1$, not necessarily in lowest terms. Its value is $\pm\mathrm{num}/\mathrm{den}$, and its **encoding length** is the larger of the bit lengths of $\mathrm{num}$ and $\mathrm{den}$.
--
--   The triple takes three consecutive memory cells: sign ($0$ or $1$), numerator, denominator. Vectors and matrices are written row by row. A memory holds a well-formed triple at address $a$ if the sign cell is at most $1$ and the denominator is positive; the value read there is the corresponding rational.
--
--   The predicates `MatBounded` and `VecBounded` say that all entries have magnitude at most $B$ and encoding length at most $b$, and `qdot` is the exact rational inner product of two encoded rows.
--
--   This renders "All input coordinates are rationals of magnitude at most $B\ge1$, with signed numerators and positive denominators of bit length at most $b$".
-- source:
--   Huang, Chen, Softmax Attention with Any Temperature in Fixed Dimension, arXiv:2611.06055 (sha256 a60f7609…), Definition 2.1, p.10

import Mathlib

namespace SoftmaxAttnFD

/-- A rational as an encoded triple (arXiv:2611.06055, sha256 a60f7609…, Definition 2.1, p.10:
"signed numerators and positive denominators of bit length at most b").

**Formalization Note** The triple need not be reduced, so every encoding the page allows is an
input. -/
structure RatEnc where
  neg : Bool
  num : ℕ
  den : ℕ
  den_pos : 0 < den

/-- The value of an encoded rational. -/
def RatEnc.val (e : RatEnc) : ℚ :=
  (if e.neg then -1 else 1) * (e.num : ℚ) / (e.den : ℚ)

/-- The encoding length: the larger bit length of numerator and denominator. -/
def RatEnc.bits (e : RatEnc) : ℕ := max e.num.size e.den.size

/-- The value as a real number. -/
noncomputable def RatEnc.toReal (e : RatEnc) : ℝ := (e.val : ℝ)

/-- The three memory cells of an encoded rational: sign (0 or 1), numerator, denominator. -/
def RatEnc.cells (e : RatEnc) : List ℕ := [e.neg.toNat, e.num, e.den]

/-- The cells of a vector, in order. -/
def vecCells {a : ℕ} (v : Fin a → RatEnc) : List ℕ :=
  (List.finRange a).flatMap fun i => (v i).cells

/-- The cells of a matrix, row by row. -/
def matCells {a c : ℕ} (A : Fin a → Fin c → RatEnc) : List ℕ :=
  (List.finRange a).flatMap fun i => vecCells (A i)

/-- The memory holding the list `l` from cell `0` on, zero elsewhere. -/
def memOf (l : List ℕ) : ℕ → ℕ := fun i => l.getD i 0

/-- The memory holds a well-formed triple at address `a`: sign cell at most 1, denominator positive. -/
def ValidAt (mem : ℕ → ℕ) (a : ℕ) : Prop := mem a ≤ 1 ∧ 0 < mem (a + 2)

/-- The rational read at address `a`, meaningful under `ValidAt`. -/
def valAt (mem : ℕ → ℕ) (a : ℕ) : ℚ :=
  (if mem a = 0 then 1 else -1) * (mem (a + 1) : ℚ) / (mem (a + 2) : ℚ)

/-- Every entry of a matrix has magnitude at most `B` and encoding length at most `b`. -/
def MatBounded {a c : ℕ} (A : Fin a → Fin c → RatEnc) (B : ℝ) (b : ℕ) : Prop :=
  ∀ i j, |(A i j).toReal| ≤ B ∧ (A i j).bits ≤ b

/-- Every entry of a vector has magnitude at most `B` and encoding length at most `b`. -/
def VecBounded {a : ℕ} (v : Fin a → RatEnc) (B : ℝ) (b : ℕ) : Prop :=
  ∀ i, |(v i).toReal| ≤ B ∧ (v i).bits ≤ b

/-- The exact rational inner product of two encoded rows. -/
def qdot {d : ℕ} (x y : Fin d → RatEnc) : ℚ := ∑ l, (x l).val * (y l).val

end SoftmaxAttnFD


