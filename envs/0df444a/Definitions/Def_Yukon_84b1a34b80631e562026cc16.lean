-- Prove2me | Definitions.Def_Yukon_84b1a34b80631e562026cc16
-- name    : Yukon_84b1a34b80631e562026cc16
-- status  : Definition
-- author  : @yukon
-- created : 2026-09-30T17:59:05.073841+00:00
-- url     : https://prove2.me/theorems/6f8d978a-76bd-4c83-9471-7dd4f42da0ae
-- title:
--   YukonModule.ArkLib.ProofSystem.ToyProblem.Definitions.part0
-- statement:
--   Source module ArkLib.ProofSystem.ToyProblem.Definitions.
-- source:
--   https://github.com/Verified-zkEVM/ArkLib/blob/e65197892890b8fd9b0dc05b8980273cf1d595cc/ArkLib/ProofSystem/ToyProblem/Definitions.lean
--
--   yukon-proof-operation:f65ab816d2030af119d148f1c77568d7d1be34600d07564ee79b11a61c3a5f27
--   [yukon-proof-receipt:eyJ2IjoxLCJtYXJrZXIiOiJ5dWtvbi1wcm9vZi1vcGVyYXRpb246ZjY1YWI4MTZkMjAzMGFmMTE5ZDE0OGYxYzc3NTY4ZDdkMWJlMzQ2MDBkMDc1NjRlZTc5YjExYTYxYzNhNWYyNyIsImhhc2giOiI2NDBhM2VkMDM1MTJlMGEwOGExMWYyMDhiYTUyZDc2ODZjODZhYTMzODhjM2U2ZGM5MDA0ZmU0YTBhMDc1ZjFiIiwia2luZCI6ImRlZmluaXRpb24iLCJ0YXJnZXQiOiJZdWtvbl84NGIxYTM0YjgwNjMxZTU2MjAyNmNjMTYiLCJlbnZpcm9ubWVudCI6eyJtYXRobGliUmV2IjoiMGRmNDQ0YTM2MGVhYTYwYWI4YzExZGNhNTFhODZhZjY5Mjk1NTQ3NCIsInRvb2xjaGFpbiI6ImxlYW5wcm92ZXIvbGVhbjQ6djQuMzMuMSJ9LCJ0YWciOiJiZXR0ZXItY29kZXMifQ]

/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

import Definitions.Def_Yukon_2d0e6914e1f35ef62dbe39e4

import Definitions.Def_Yukon_c1febaeb760a3ab48ce07f54

import Definitions.Def_Yukon_57f2f4a582b59c53cdee835d



import Mathlib.Data.NNReal.Defs
import Mathlib.Topology.MetricSpace.Infsep
import Mathlib.Tactic.Qify
import Mathlib.InformationTheory.Hamming
import Mathlib.Data.ENat.Lattice
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.RingTheory.Henselian
import Mathlib.LinearAlgebra.AffineSpace.Combination
import Mathlib.LinearAlgebra.AffineSpace.Pointwise
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Algebra.Lie.OfAssociative
import Init
import Mathlib.Tactic.DepRewrite
import Mathlib.Data.Fin.Basic
import Batteries.Data.Fin.Fold
import Mathlib.Tactic.FinCases
import Mathlib.Data.Fin.Tuple.Take
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Order.Sub.Basic
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Order.CompletePartialOrder
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Data.NNReal.Basic
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.Algebra.Order.Star.Basic
import Mathlib.Algebra.BigOperators.Finsupp.Fin
import Mathlib.Data.Finsupp.Fin
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Data.FinEnum
import Mathlib.Algebra.Group.Action.Pointwise.Finset
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.SchwartzZippel
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.ENNReal.Inv
import Mathlib.Data.ENat.Basic
import Mathlib.Data.ENat.Defs
import Mathlib.Data.Nat.Cast.Order.Field
import Mathlib.Algebra.CharP.Defs
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finsupp.Basic
import Mathlib.Data.Nat.Digits.Defs
import Mathlib.Data.Nat.Bitwise
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.IntervalCases
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.Ring.Regular
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.PicardGroup
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.FieldTheory.Finiteness
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Data.Real.ENatENNReal
import Mathlib.Algebra.Order.Floor.Semifield
set_option backward.isDefEq.respectTransparency.types false
/-!
# Toy problem definitions

This file defines the exact and relaxed relations for the toy IOP of [ABF26, Section 6],
together with its winning-challenge set. The encoding map is part of the data: replacing it by
an existentially chosen map with the same range would change the constrained relation.

## References

* [Arnon, G., Boneh, D., and Fenzi, G., *Open Problems in List Decoding and Correlated
    Agreement*][ABF26]
-/

namespace ToyProblem

open Code InterleavedCode
open scoped NNReal

variable {ι F A : Type*} [Fintype ι] [Field F] [AddCommGroup A] [Module F A]

/-- The toy-problem relation for a fixed linear encoder. Each word is the encoding of one
message row, and every message row satisfies its prescribed linear constraint. -/
def RelationFor {k ℓ : ℕ} (encode : (Fin k → F) →ₗ[F] (ι → A))
    (v : Fin k → F) (μ : Fin ℓ → F) (W : Fin ℓ → ι → A) : Prop :=
  ∃ M : Fin ℓ → Fin k → F, (∀ i, W i = encode (M i)) ∧
    ∀ i, ∑ j, M i j * v j = μ i

/-- The relaxed toy-problem relation. A word stack is valid when it agrees with an exact
instance on at least a `1 - δ` fraction of coordinate blocks. -/
def RelaxedRelationFor {k ℓ : ℕ} (encode : (Fin k → F) →ₗ[F] (ι → A)) (δ : ℝ≥0)
    (v : Fin k → F) (μ : Fin ℓ → F) (W : Fin ℓ → ι → A) : Prop :=
  ∃ Wstar : Fin ℓ → ι → A, RelationFor encode v μ Wstar ∧
    ∃ S : Finset ι, (1 - (δ : ℝ)) * Fintype.card ι ≤ S.card ∧
      ∀ i, ∀ j ∈ S, W i j = Wstar i j

/-- The challenges for which the affine combination of two words and constraints is a valid
one-row relaxed instance. -/
def winningSetFor {k : ℕ} (encode : (Fin k → F) →ₗ[F] (ι → A)) (δ : ℝ≥0)
    (v : Fin k → F) (μ₁ μ₂ : F) (f₁ f₂ : ι → A) : Set F :=
  {γ | RelaxedRelationFor (ℓ := 1) encode δ v
    (fun _ ↦ μ₁ + γ * μ₂) (fun _ j ↦ f₁ j + γ • f₂ j)}

end ToyProblem


