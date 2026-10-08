-- Prove2me | Definitions.Def_MazurTransfer_OrderEighteenDyadicCandidateData
-- name    : MazurTransfer_OrderEighteenDyadicCandidateData
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-06T12:26:27.735558+00:00
-- url     : https://prove2.me/theorems/9ef860bd-8ad2-4bdf-ad79-6671abcfbe0c
-- title:
--   Finite dyadic data for the order-18 descent
-- statement:
--   This module supplies coefficient triples over $\mathbb Z/16\mathbb Z$, the multiplication obtained by reducing $\tau^3=3\tau+1$, the corresponding square predicate, and fifteen fixed candidate vectors from the global norm-kernel enumeration. It asserts no nonsquare result. Named downstream consumer: the finite nonsquare certificate and its checked transfer into the order-18 local descent.
-- source:
--   User MazurTheorem WIP at 54d43d8dda8a6fcf069cc02a815f850d762c5c0c: MazurTorsion/NumberTheory/XOneEighteenDyadicCubicCertificate.lean. All original data and the decidable square-predicate instance are retained; the candidate_nonsquare theorem is separated at its exact whole Lean AST command boundary. Original Apache-2.0 header retained. The original coefficient-vector docstring typo modulo 2^7 is corrected to modulo 2^4, matching ZMod 16; no definition or theorem type changes.

/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import Mathlib

/-!
# Finite cubic dyadic certificates for the `X₁(18)` descent

The dyadic completion of the real cubic coefficient field is unramified of
residue degree three.  Its quotient modulo `2⁴` is represented here by
coefficient triples for `τ³ = 3τ + 1`.  This deliberately finite module
records the nonsquare calculation for the fifteen nonidentity products of
the four proposed global norm-kernel generators.

The downstream local-descent module is responsible for relating these raw
triples to integral elements in the completion; no such bridge is assumed
here.
-/

namespace MazurTorsion.XOneEighteenDyadicCubicCertificate

/-- Coefficients of `a + bτ + cτ²` modulo `2⁴`. -/
abbrev CubicResidue := Fin 3 → ZMod 16

/-- Multiplication after reducing by `τ³ = 3τ + 1`. -/
def mul (x y : CubicResidue) : CubicResidue :=
  ![x 0 * y 0 + x 1 * y 2 + x 2 * y 1,
    x 0 * y 1 + x 1 * y 0 + 3 * (x 1 * y 2 + x 2 * y 1) + x 2 * y 2,
    x 0 * y 2 + x 1 * y 1 + x 2 * y 0 + 3 * x 2 * y 2]

/-- The raw finite-ring square predicate. -/
def IsSquare (x : CubicResidue) : Prop :=
  ∃ a b c : ZMod 16, mul ![a, b, c] ![a, b, c] = x

instance (x : CubicResidue) : Decidable (IsSquare x) :=
  by
    unfold IsSquare
    letI d₃ (a b : ZMod 16) : Decidable
        (∃ c : ZMod 16, mul ![a, b, c] ![a, b, c] = x) :=
      Fintype.decidableExistsFintype
    letI d₂ (a : ZMod 16) : Decidable
        (∃ b c : ZMod 16, mul ![a, b, c] ![a, b, c] = x) :=
      Fintype.decidableExistsFintype
    exact Fintype.decidableExistsFintype

/-- Reductions of the fifteen nonempty products of the four global
norm-kernel generators, in binary-mask order `1, ..., 15`. -/
def candidate : Fin 15 → CubicResidue :=
  ![![15, 1, 5],
    ![28, 11, 11],
    ![102, 62, 97],
    ![30, 22, 2],
    ![50, 66, 104],
    ![80, 96, 54],
    ![70, 64, 68],
    ![18, 0, 18],
    ![32, 34, 118],
    ![62, 94, 16],
    ![8, 66, 116],
    ![40, 84, 44],
    ![40, 96, 68],
    ![96, 76, 80],
    ![108, 72, 12]]



end MazurTorsion.XOneEighteenDyadicCubicCertificate

/- Structural boundary: the explicit finite multiplication, square predicate
and fifteen fixed vectors. Named consumer: the dyadic candidate nonsquare
certificate, then the unconditional order-18 descent. No nonsquare theorem
is asserted in this data interface. -/


