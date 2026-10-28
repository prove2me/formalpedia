-- Prove2me | Definitions.Def_OAIQ15Sf009
-- name    : OAIQ15Sf009
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-26T15:24:15.379256+00:00
-- url     : https://prove2.me/theorems/b1c8fe6b-4187-4694-8d51-38e2928a8675
-- title:
--   Definitions bundle OAIQ15Sf009 of the split of OpenAI, A counterexample to Kaplansky's quasitrace conjecture and failure of tensor-product stable finiteness
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.KaplanskyConsequences.stable_finiteness_bundle`, carved from OpenAI's openai/math development (OpenAI, *A counterexample to Kaplansky's quasitrace conjecture and failure of tensor-product stable finiteness*, OpenAI Math Release, September 23, 2026, result family 294, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 5 declarations of OpenAI's Lean: 3 definitions and 2 theorems. The definitions and types are `OAI.KaplanskyConsequences.Regular.diagonalHom`, `OAI.KaplanskyConsequences.Regular.polynomialAlgebra`, `OAI.KaplanskyConsequences.homKernel`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis/Kaplansky, in whole or in part: [`Kaplansky_Regular_ReducedPolynomials`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Kaplansky/Kaplansky/Regular/ReducedPolynomials.lean), [`Kaplansky_Regular_RegularOperators`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Kaplansky/Kaplansky/Regular/RegularOperators.lean), [`Kaplansky_StableFiniteness_SimpleRepresentation`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Kaplansky/Kaplansky/StableFiniteness/SimpleRepresentation.lean).
--
--   **Imports.** It imports the published bundle `Def_KaplanskyStableFiniteness`; the bundle `OAIQ15Sf004` of this split.
--
--   **Imported by** (directly, in this split): the proofs of `OAI.KaplanskyConsequences.Regular.polynomial_dense_zero`, `OAI.KaplanskyConsequences.Regular.tensor_two_isometries_of_small_tuple` and `OAI.KaplanskyConsequences.simple_stable_tensor_counterexample_exists`.
-- source:
--   OpenAI, A counterexample to Kaplansky's quasitrace conjecture and failure of tensor-product stable finiteness, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 294; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-counterexample-to-Kaplanskys-quasitrace-conjecture-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis/Kaplansky at commit adc7f12

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_KaplanskyStableFiniteness
import Definitions.Def_OAIQ15Sf004

section
-- module Solutions.OAIQ15_Sf.Kaplansky_Regular_ReducedPolynomials
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace KaplanskyConsequences.Regular

open scoped BigOperators InnerProductSpace ENNReal
attribute [local instance 2000] Classical.propDecidable Classical.decEq
variable {G : Type*} [Group G]

lemma span_left_mul {x y : Op G}
    (hx : x ∈ Submodule.span ℂ (Set.range (left (G:=G) (H:=ℂ))))
    (hy : y ∈ Submodule.span ℂ (Set.range (left (G:=G) (H:=ℂ)))) :
    x*y ∈ Submodule.span ℂ (Set.range (left (G:=G) (H:=ℂ))) := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨g,rfl⟩ := hx
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨h,rfl⟩ := hy
      rw [←left_mul]
      exact Submodule.subset_span ⟨g*h,rfl⟩
    | zero => simp
    | add x y hx hy ihx ihy => simpa only [mul_add] using (Submodule.span ℂ _).add_mem ihx ihy
    | smul c x hx ih => simpa only [mul_smul_comm] using (Submodule.span ℂ _).smul_mem c ih
  | zero => simp
  | add x y hx hy ihx ihy => simpa only [add_mul] using (Submodule.span ℂ _).add_mem ihx ihy
  | smul c x hx ih => simpa only [smul_mul_assoc] using (Submodule.span ℂ _).smul_mem c ih

lemma span_left_star {x : Op G}
    (hx : x ∈ Submodule.span ℂ (Set.range (left (G:=G) (H:=ℂ)))) :
    star x ∈ Submodule.span ℂ (Set.range (left (G:=G) (H:=ℂ))) := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨g,rfl⟩ := hx
    rw [left_star]
    exact Submodule.subset_span ⟨g⁻¹,rfl⟩
  | zero =>
    rw [star_zero (Op G)]
    exact (Submodule.span ℂ (Set.range (left (G:=G) (H:=ℂ)))).zero_mem
  | add x y hx hy ihx ihy =>
    rw [star_add x y]
    exact (Submodule.span ℂ _).add_mem ihx ihy
  | smul c x hx ih => simpa only [star_smul] using (Submodule.span ℂ _).smul_mem (star c) ih

def polynomialAlgebra : StarSubalgebra ℂ (Op G) where
  carrier := Submodule.span ℂ (Set.range (left (G:=G) (H:=ℂ)))
  zero_mem' := (Submodule.span ℂ _).zero_mem
  one_mem' := by
    rw [←left_one (G:=G) (H:=ℂ)]
    exact Submodule.subset_span ⟨1,rfl⟩
  add_mem' := (Submodule.span ℂ _).add_mem
  mul_mem' := span_left_mul
  algebraMap_mem' c := by
    rw [Algebra.algebraMap_eq_smul_one,←left_one (G:=G) (H:=ℂ)]
    exact (Submodule.span ℂ _).smul_mem c (Submodule.subset_span ⟨1,rfl⟩)
  star_mem' := span_left_star


end KaplanskyConsequences.Regular

end

end OAI
end

section
-- module Solutions.OAIQ15_Sf.Kaplansky_Regular_RegularOperators
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace KaplanskyConsequences.Regular

open scoped ComplexOrder InnerProductSpace BigOperators ENNReal
attribute [local instance] Classical.propDecidable
variable {G H : Type*} [Group G] [NormedAddCommGroup H]
  [InnerProductSpace ℂ H] [CompleteSpace H]

def diagonalHom : (H →L[ℂ] H) →⋆ₐ[ℂ] (HilbertSum G H →L[ℂ] HilbertSum G H) where
  toFun := diagonal
  map_zero' := by ext; rfl
  map_one' := diagonal_one
  map_add' _ _ := by ext; rfl
  map_mul' := diagonal_mul
  commutes' _ := by ext; rfl
  map_star' := diagonal_star


end KaplanskyConsequences.Regular

end

end OAI
end

section
-- module Solutions.OAIQ15_Sf.Kaplansky_StableFiniteness_SimpleRepresentation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace KaplanskyConsequences

open scoped ComplexOrder InnerProductSpace
attribute [local instance] CStarAlgebra.spectralOrder CStarAlgebra.spectralOrderedRing
universe u v
variable {A : Type u} {B : Type v} [CStarAlgebra A] [CStarAlgebra B]

def homKernel (f : A →⋆ₐ[ℂ] B) : ClosedStarIdeal A where
  carrier := {a | f a=0}
  zero_mem' := map_zero f
  add_mem' := by intros; dsimp at *; simp_all only [map_add,add_zero]
  mul_mem' := by intros; dsimp at *; simp_all only [map_mul,zero_mul]
  smul_mem' := by intros; dsimp at *; simp_all only [map_smul,smul_zero]
  star_mem' := by intros; dsimp at *; simp_all only [map_star,star_zero]
  mul_mem_left := by intro a b hb; change f (a*b)=0; rw [map_mul,hb,mul_zero]
  mul_mem_right := by intro a b ha; change f (a*b)=0; rw [map_mul,ha,zero_mul]
  closed := isClosed_eq (map_continuous f) continuous_const


end KaplanskyConsequences

end

end OAI
end


