-- Prove2me | Definitions.Def_HadamardCubeFiber
-- name    : HadamardCubeFiber
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-07T04:32:13.530472+00:00
-- url     : https://prove2.me/theorems/e103f693-26ee-4c43-8ba1-b2d22af55e96
-- statement:
--   This block sets up notation for 6×6 complex matrices indexed by Fin 6. A matrix H is Unimodular if every entry has complex absolute value 1, and IsComplexHadamard if it is unimodular and satisfies H*H = 6·I, where H* is the conjugate transpose, so the columns are mutually orthogonal. The entrywiseSquare of H replaces each entry H_ij by H_ij². For a vector v : Fin 6 → ℂ and a complex number z, cubeFiber(v,z) is the finite set of indices i with v_i³ = z, the cubic fibre of v over z. Finally rowRatio(H,i,j) is the vector indexed by k whose kth entry is H_ik times the complex conjugate of H_jk, the entrywise ratio of rows i and j when entries are unimodular. These are definitions only, with no theorem or hypothesis stated.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/HadamardCubeFiber.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/HadamardCubeFiber.lean; bytes 16..714
-- Kind: block; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib

namespace OAI

/-! Cancellation of row ratios on a prescribed cubic fibre. -/

open scoped BigOperators Matrix

namespace HadamardSix

abbrev Index := Fin 6
abbrev Matrix6 := Matrix Index Index ℂ

def Unimodular (H : Matrix6) : Prop := ∀ i j, ‖H i j‖ = 1

def IsComplexHadamard (H : Matrix6) : Prop :=
  Unimodular H ∧ H.conjTranspose * H = (6 : ℂ) • (1 : Matrix6)

def entrywiseSquare (H : Matrix6) : Matrix6 := fun i j => H i j ^ 2

noncomputable def cubeFiber (v : Index → ℂ) (z : ℂ) : Finset Index := by
  classical
  exact Finset.univ.filter (fun i => v i ^ 3 = z)

noncomputable def rowRatio (H : Matrix6) (i j : Index) : Index → ℂ :=
  fun k => H i k * star (H j k)



end HadamardSix
end OAI


