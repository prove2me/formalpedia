-- Prove2me | Definitions.Def_IntMul_BinaryQuadraticPhase
-- name    : IntMul_BinaryQuadraticPhase
-- status  : Definition
-- author  : @raresbuhai
-- created : 2026-10-09T17:26:21.478989+00:00
-- url     : https://prove2.me/theorems/45dcb824-9749-4093-b918-caf8f97b5b6a
-- title:
--   Binary phases and the elementary complex tensor transform
-- statement:
--   This interface defines the binary character $(-1)^a$, its doubled lift from $\mathbb F_2$ to $\mathbb Z/4\mathbb Z$, and the exact Gaussian-integer phase $i^q$. It also defines the one-coordinate complex transform $C$ with diagonal entries $(1+i)/2$ and off-diagonal entries $(1-i)/2$, its tensor-product kernel, the coordinatewise phase $\prod_j i^{x_j}$, and Hamming weight modulo four. The file contains only definitions, with no residual normal-form or machine-correctness assumptions. These are the objects in the complex binary residual interface used by the integer-multiplication κ construction.
-- source:
--   CrocSwap/integer-mult-bounds, commit 3b6b66891c0ac888521cf591fe306c6286601d4f, notes/endpoint-gauge-complex.tex, subsection “A normal form for every nondegenerate binary residual”. https://github.com/CrocSwap/integer-mult-bounds/blob/3b6b66891c0ac888521cf591fe306c6286601d4f/notes/endpoint-gauge-complex.tex

import Mathlib.Data.ZMod.Basic
import Mathlib.NumberTheory.Zsqrtd.GaussianInt

/-! Binary characters and exact fourth-root phases for the complex residual interface.
These definitions contain no algorithmic, analytic, or normal-form assumptions. -/

open scoped BigOperators

namespace IntMul.BinaryPhase

/-- The real-valued binary character, embedded in the complex numbers. -/
def sign (a : ZMod 2) : ℂ := if a.val = 0 then 1 else -1

/-- The canonical doubled lift from a binary value to a value modulo four. -/
def twice (a : ZMod 2) : ZMod 4 := 2 * (a.val : ZMod 4)

/-- An exact Gaussian-integer fourth root, using the canonical residue modulo four. -/
def phase (a : ZMod 4) : GaussianInt := (Zsqrtd.sqrtd : GaussianInt) ^ a.val

/-- The canonical bit lifted to a residue modulo four. -/
def liftBit (a : ZMod 2) : ZMod 4 := (a.val : ZMod 4)

/-- The elementary complex transform on one binary coordinate. -/
noncomputable def cEntry (a b : ZMod 2) : ℂ :=
  if a.val = b.val then (1 + Complex.I) / 2 else (1 - Complex.I) / 2

/-- The tensor product of the elementary complex transform, expressed by entries. -/
noncomputable def tensorKernel {ι : Type*} [Fintype ι] (x y : ι → ZMod 2) : ℂ :=
  ∏ i, cEntry (x i) (y i)

/-- Coordinatewise fourth-root phases. -/
def coordinatePhase {ι : Type*} [Fintype ι] (x : ι → ZMod 2) : ℂ :=
  ∏ i, (phase (liftBit (x i)) : ℂ)

/-- Hamming weight reduced modulo four. -/
def quadraticWeight {ι : Type*} [Fintype ι] (x : ι → ZMod 2) : ZMod 4 :=
  ∑ i, liftBit (x i)

end IntMul.BinaryPhase


