-- Prove2me | Definitions.Def_Yukon_c1febaeb760a3ab48ce07f54
-- name    : Yukon_c1febaeb760a3ab48ce07f54
-- status  : Definition
-- author  : @yukon
-- created : 2026-09-30T17:54:09.411836+00:00
-- url     : https://prove2.me/theorems/a0d6b750-7ec9-4e7c-bd4e-a8ddc0f051e4
-- title:
--   YukonModule.ArkLib.Data.CodingTheory.Erasure.part0
-- statement:
--   Source module ArkLib.Data.CodingTheory.Erasure.
-- source:
--   https://github.com/Verified-zkEVM/ArkLib/blob/e65197892890b8fd9b0dc05b8980273cf1d595cc/ArkLib/Data/CodingTheory/Erasure.lean
--
--   yukon-proof-operation:99f12274be126d5640d114181191b10e107787ff4e2a059e74b2c301bf8b9763
--   [yukon-proof-receipt:eyJ2IjoxLCJtYXJrZXIiOiJ5dWtvbi1wcm9vZi1vcGVyYXRpb246OTlmMTIyNzRiZTEyNmQ1NjQwZDExNDE4MTE5MWIxMGUxMDc3ODdmZjRlMmEwNTllNzRiMmMzMDFiZjhiOTc2MyIsImhhc2giOiJhMmI5MGY4MDA0YjkzZjYxMDcyNjA3ODY1MjNjMTgyYmNkOTg4NWFhNTUzZTM2Y2JiN2NjNGMwZGI1YzExYWFmIiwia2luZCI6ImRlZmluaXRpb24iLCJ0YXJnZXQiOiJZdWtvbl9jMWZlYmFlYjc2MGEzYWI0OGNlMDdmNTQiLCJlbnZpcm9ubWVudCI6eyJtYXRobGliUmV2IjoiMGRmNDQ0YTM2MGVhYTYwYWI4YzExZGNhNTFhODZhZjY5Mjk1NTQ3NCIsInRvb2xjaGFpbiI6ImxlYW5wcm92ZXIvbGVhbjQ6djQuMzMuMSJ9LCJ0YWciOiJiZXR0ZXItY29kZXMifQ]

/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

import Definitions.Def_Yukon_2d0e6914e1f35ef62dbe39e4



import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.ENNReal.Inv
import Mathlib.Data.ENat.Basic
import Mathlib.Data.ENat.Defs
import Mathlib.Data.Nat.Cast.Order.Field
import Mathlib.Algebra.CharP.Defs
import Mathlib.Data.NNReal.Basic
import Mathlib.Data.NNReal.Defs
import Mathlib.Algebra.BigOperators.Fin
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
import Mathlib.Algebra.Order.Star.Basic
import Init
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Data.Real.ENatENNReal
import Mathlib.Topology.MetricSpace.Infsep
import Mathlib.Tactic.Qify
import Mathlib.InformationTheory.Hamming
import Mathlib.Data.ENat.Lattice
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.RingTheory.Henselian
import Mathlib.LinearAlgebra.AffineSpace.Combination
import Mathlib.LinearAlgebra.AffineSpace.Pointwise
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Tactic.DepRewrite
import Mathlib.Data.Fin.Basic
import Batteries.Data.Fin.Fold
import Mathlib.Tactic.FinCases
import Mathlib.Data.Fin.Tuple.Take
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Order.Sub.Basic
import Mathlib.Algebra.Order.Ring.Nat
set_option backward.isDefEq.respectTransparency.types false
/-!
# Erasure-decoding uniqueness

The metric fact underlying erasure decoding: fewer than `minDist C` erasures leave at most one
codeword consistent with the observed word. Equivalently, a code of minimum distance `d`
corrects `d - 1` erasures.

The observations are modelled as an `Option`-valued word, `none` marking an erasure. This
file packages the general exceptional-coordinate theorem
`Code.eq_of_disagreementCols_subset_of_card_lt_minDist` for that shape; the correction
*algorithm* and its cost are out of scope, ArkLib having no cost model to state them in.

## Main statements

* `CodingTheory.eq_of_consistent_with_erased`

## References

* [Guruswami, V., Rudra, A., and Sudan, M., *Essential Coding Theory*][codingtheory]
* [Arnon, G., Boneh, D., and Fenzi, G., *Open Problems in List Decoding and Correlated
    Agreement*][ABF26]
-/

namespace CodingTheory

open Code

variable {ι F : Type*} [Fintype ι]

/-- Two codewords consistent with the same partially-erased word `f`, where fewer than
`minDist C` coordinates are erased, are equal: they can disagree only on erased coordinates,
so their Hamming distance is below the minimum distance. -/
theorem eq_of_consistent_with_erased [DecidableEq F] {C : Set (ι → F)}
    {f : ι → Option F} {u v : ι → F} (hu : u ∈ C) (hv : v ∈ C)
    (hfu : ∀ i, f i = some (u i) ∨ f i = none)
    (hfv : ∀ i, f i = some (v i) ∨ f i = none)
    (hcard : (Finset.univ.filter (fun i ↦ f i = none)).card < Code.minDist C) :
    u = v := by
  -- `u` and `v` agree wherever `f` is not erased.
  have hsub : disagreementCols u v ⊆ Finset.univ.filter (fun i ↦ f i = none) := by
    intro i hi
    rw [mem_disagreementCols] at hi
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    rcases hfu i with h1 | h1
    · rcases hfv i with h2 | h2
      · exact absurd (Option.some.inj (h1.symm.trans h2)) hi
      · exact h2
    · exact h1
  exact Code.eq_of_disagreementCols_subset_of_card_lt_minDist hu hv _ hsub hcard

end CodingTheory


