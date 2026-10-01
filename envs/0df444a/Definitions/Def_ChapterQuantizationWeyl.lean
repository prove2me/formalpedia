-- Prove2me | Definitions.Def_ChapterQuantizationWeyl
-- name    : ChapterQuantizationWeyl
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-01T04:41:54.027196+00:00
-- url     : https://prove2.me/theorems/0dd1ebc9-1b4a-48c0-900f-1024382337eb
-- title:
--   Chapter QuantizationWeyl
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterQuantizationWeyl.lean`): generated def bundle for ChapterQuantizationWeyl. See BookProof/ChapterQuantizationWeyl.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterQuantizationWeyl.lean

import Mathlib


/-!
# Quantization due to time-evolution: the Weyl relations from conjugation

This file formalizes the self-contained algebraic content of the book's section
**"Quantization due to time evolution"** (from the chapter *"Quantization due to
time-evolution: Yang-Mills and Classical Statistical Field Theory"*, `book.tex`
line ~6802).  The book's central claim there is that *quantization* — the
appearance of the canonical commutation relations of position and momentum
(strictly, the **Weyl relations**, the exponentiated form of the CCR) — is a
consequence of a **non-deterministic time-evolution** acting by conjugation.

The mechanism used in the book is the Trotter / Baker–Campbell–Hausdorff formula
`e^{εA} e^{B} e^{-εA} = e^{B - ε[A,B] + O(ε²)}`, together with the concrete
`e^{iεp²} e^{ix} e^{-iεp²} = e^{i(x+εp)}` (conjugating the exponentiated position
by a kinetic time-step shifts it by the momentum — "the time-derivative of the
position operator is the momentum operator").

The full CCR `[x,p] = i·1` has **no finite-dimensional representation** (a trace
argument forbids it).  The honest finite-dimensional model that captures exactly
the structure the book uses is the **Heisenberg algebra / group**: three
`3×3` real matrices

* `Xgen = e₁₂`  (the "position" generator),
* `Ygen = e₂₃`  (the "momentum" generator),
* `Zgen = e₁₃`  (the central element `[X,Y]`),

with the defining relations `[X,Y] = Z`, `Z` central, and `X² = Y² = Z² = 0`.
Here every element is nilpotent so the exponential series terminates and all the
BCH/Trotter identities become **exact** (no `O(ε²)` remainder): this is the
Heisenberg group, whose group law is precisely the exponentiated CCR.

Main results (all `sorry`-free, `axiom`-free beyond `propext`/`Classical.choice`/
`Quot.sound`):

* `comm_XY` — the CCR `[X,Y] = Z`, and `comm_scaled` its scaled form
  `[aX, bY] = (ab)Z`;
* `Zgen_central`, `Zgen_sq` — `Z` is central and squares to zero;
* `Heis_mul` — the Heisenberg **group law**
  `H(a,b,c)·H(a',b',c') = H(a+a', b+b', c+c'+a·b')`;
* `exp_Ngen` — the exponential map `exp(aX+bY+cZ) = H(a, b, c + ab/2)`;
* `weyl` — the **Weyl relation** `exp(aX)·exp(bY) = exp(aX + bY + (ab/2)Z)`
  (the exponentiated CCR / BCH product formula, exact here);
* `weyl_shift` — the **conjugation / quantization identity**
  `exp(aX)·exp(bY)·exp(-aX) = exp(bY + (ab)Z) = exp(bY + a[X,Y])`,
  the finite-dimensional model of the book's `e^{εA}e^{B}e^{-εA}=e^{B-ε[A,B]}`
  and of `e^{iεp²}e^{ix}e^{-iεp²}=e^{i(x+εp)}`: conjugating the "momentum"
  one-parameter subgroup by the "position" time-step shifts it in the central
  `[X,Y]` direction.
-/

open NormedSpace
open scoped Matrix

namespace BookProof.QuantizationWeyl

/- We equip the `3×3` real matrices with the (local, non-canonical) `ℓ∞`
operator norm so that `NormedSpace.exp` has its series available. -/
attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

/-- The algebra of `3×3` real matrices, the ambient algebra of the model. -/
abbrev M := Matrix (Fin 3) (Fin 3) ℝ

/-- The "position" generator `X = e₁₂`. -/
def Xgen : M := !![0,1,0;0,0,0;0,0,0]

/-- The "momentum" generator `Y = e₂₃`. -/
def Ygen : M := !![0,0,0;0,0,1;0,0,0]

/-- The central generator `Z = e₁₃ = [X,Y]`. -/
def Zgen : M := !![0,0,1;0,0,0;0,0,0]

/-- A general element `aX + bY + cZ` of the Heisenberg (nilpotent) subalgebra. -/
def Ngen (a b c : ℝ) : M := !![0,a,c;0,0,b;0,0,0]

/-- A general element `H(a,b,c) = I + aX + bY + cZ` of the Heisenberg group. -/
def Heis (a b c : ℝ) : M := !![1,a,c;0,1,b;0,0,1]

 































end BookProof.QuantizationWeyl


