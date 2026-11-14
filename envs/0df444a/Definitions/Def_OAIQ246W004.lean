-- Prove2me | Definitions.Def_OAIQ246W004
-- name    : OAIQ246W004
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-13T07:14:58.081621+00:00
-- url     : https://prove2.me/theorems/fe9d461b-66bd-4c53-a647-cb2d6b3eb340
-- title:
--   Definitions bundle OAIQ246W004 of the split of OpenAI, Weak pure infiniteness and O-infinity absorption (result family 303)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.WeakPureInfiniteness.exact_weaklyPurelyInfinite_individuallyProperlyInfinite_any` and `OAI.WeakPureInfiniteness.exact_weaklyPurelyInfinite_stronglyPurelyInfinite`, carved from OpenAI's openai/math development (OpenAI, *Weak pure infiniteness and O-infinity absorption (result family 303)*, OpenAI Math Release, September 25, 2026, result family 303, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 11 declarations of OpenAI's Lean: 1 definition and 10 theorems. The definitions and types are `OAI.WeakPureInfiniteness.tensorToHilbertSum`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`WeakInfiniteness_TensorHilbertSum`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/WeakInfiniteness/TensorHilbertSum.lean).
--
--   **Imports.** It imports the bundles `OAIQ246W000` and `OAIQ246W001` of this split.
--
--   **Imported by** (directly, in this split): the proof of `OAI.WeakPureInfiniteness.freeDiagonalFunctional_bound_of_kernel`.
-- source:
--   OpenAI, Weak pure infiniteness and O-infinity absorption (result family 303), OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 303; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Weak-pure-infiniteness-and-O-infinity-absorption-September-25-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ246W000
import Definitions.Def_OAIQ246W001

section
-- module Solutions.OAIQ246_WI.Compat
attribute [-instance] _root_.OAI.WeakPureInfiniteness.uliftCStarAlgebra _root_.OAI.WeakPureInfiniteness.uliftInnerProduct _root_.OAI.WeakPureInfiniteness.uliftStarRing
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
@[simp] theorem fin5_lit_2_4 : ((2 : Fin 5) = 4) ↔ False := by decide
@[simp] theorem fin5_lit_3_0 : ((3 : Fin 5) = 0) ↔ False := by decide
@[simp] theorem fin5_lit_3_1 : ((3 : Fin 5) = 1) ↔ False := by decide
@[simp] theorem fin5_lit_3_2 : ((3 : Fin 5) = 2) ↔ False := by decide
@[simp] theorem fin5_lit_3_4 : ((3 : Fin 5) = 4) ↔ False := by decide
@[simp] theorem fin5_lit_4_0 : ((4 : Fin 5) = 0) ↔ False := by decide
@[simp] theorem fin5_lit_4_1 : ((4 : Fin 5) = 1) ↔ False := by decide
@[simp] theorem fin5_lit_4_2 : ((4 : Fin 5) = 2) ↔ False := by decide
@[simp] theorem fin5_lit_4_3 : ((4 : Fin 5) = 3) ↔ False := by decide
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ246_WI.WeakInfiniteness_TensorHilbertSum
attribute [-instance] _root_.OAI.WeakPureInfiniteness.groupHilbertNontrivial _root_.OAI.WeakPureInfiniteness.uliftCStarAlgebra _root_.OAI.WeakPureInfiniteness.uliftInnerProduct _root_.OAI.WeakPureInfiniteness.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct ENNReal ComplexOrder
open UniformSpace
open CStarAlgebra
open scoped NNReal
open scoped TensorProduct ComplexConjugate
open scoped ENNReal InnerProductSpace
open scoped InnerProductSpace
open scoped TensorProduct InnerProductSpace

namespace WeakPureInfiniteness

section TensorHilbertSum

variable {H G : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

lemma tensorToHilbertSumMap_inner (x y : H ⊗[ℂ] GroupHilbert G) :
    inner ℂ (tensorToHilbertSumMap x) (tensorToHilbertSumMap y) = inner ℂ x y := by
  induction x using OAI.tensorInductionOn with
  | tmul ξ η =>
    induction y using OAI.tensorInductionOn with
    | tmul ζ θ =>
      simp only [tensorToHilbertSumMap_tmul, lp.inner_eq_tsum, tensorSequence_apply,
        inner_smul_left, inner_smul_right, TensorProduct.inner_tmul, RCLike.inner_apply]
      rw [← tsum_mul_left]
      apply tsum_congr
      intro g
      ring
    | add y z hy hz => simp only [map_add, inner_add_right, hy, hz]
  | add x z hx hz => simp only [map_add, inner_add_left, hx, hz]

def tensorToHilbertSum : (H ⊗[ℂ] GroupHilbert G) →ₗᵢ[ℂ] HilbertValued.HilbertSum G H :=
  LinearMap.isometryOfInner (E := H ⊗[ℂ] GroupHilbert G)
    (E' := HilbertValued.HilbertSum G H) (𝕜 := ℂ) tensorToHilbertSumMap
    (fun x y => tensorToHilbertSumMap_inner x y)

end TensorHilbertSum

end WeakPureInfiniteness
end

end OAI
end


