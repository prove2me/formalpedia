-- Prove2me | Definitions.Def_OAIQ031A076
-- name    : OAIQ031A076
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T14:21:22.820021+00:00
-- url     : https://prove2.me/theorems/6a7baf80-187b-4f1d-92a0-021ca3683834
-- title:
--   Definitions bundle OAIQ031A076 of the split of OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.ArExplicit.Statement.main`, carved from OpenAI's openai/math development (OpenAI, *An explicit counterexample to the Auslander-Reiten conjecture (result family 199)*, OpenAI Math Release, September 23, 2026, result family 199, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 17 declarations of OpenAI's Lean: 5 definitions, 2 instances and 10 theorems. The definitions and types are `OAI.ArExplicit.TriangleGradedSequence.diagonalGenerator`, `OAI.ArExplicit.TriangleGradedSequence.zeroDiagonalEquiv`, `OAI.ArExplicit.TriangleGradedSequence.zeroScalarEquiv`, `OAI.ArExplicit.TriangularInduction.tensorCochain`, `OAI.ArExplicit.scalarExtension_semisimpleQuotientEquiv`.
--
--   **Sources.** They come from these modules of lean/OAI/Algebra, in whole or in part: [`AuslanderReiten_BaseChange_ScalarExtensionStructure`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/BaseChange/ScalarExtensionStructure.lean), [`AuslanderReiten_Fibers_FiberDiagonalGenerator`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Fibers/FiberDiagonalGenerator.lean), [`AuslanderReiten_Fibers_FiberProjectionProfile`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Fibers/FiberProjectionProfile.lean), [`AuslanderReiten_Fibers_FiberProjectionZero`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Fibers/FiberProjectionZero.lean), [`AuslanderReiten_HomComplex_FullHomCompositionSquare`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/HomComplex/FullHomCompositionSquare.lean), [`AuslanderReiten_HomComplex_FullHomZeroProjection`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/HomComplex/FullHomZeroProjection.lean), [`AuslanderReiten_HomComplex_FullHomZeroRepresentative`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/HomComplex/FullHomZeroRepresentative.lean), [`AuslanderReiten_Modules_TrivialInduction`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Modules/TrivialInduction.lean), [`AuslanderReiten_Resolutions_TrivialInductionQuotient`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Resolutions/TrivialInductionQuotient.lean), [`AuslanderReiten_Triangular_TriangularCrossHom`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Triangular/TriangularCrossHom.lean).
--
--   **Imports.** It imports the bundles `OAIQ031A049`, `OAIQ031A052`, `OAIQ031A053`, `OAIQ031A056`, `OAIQ031A057`, `OAIQ031A058`, `OAIQ031A059` and `OAIQ031A060` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ031A116`; the proof of `OAI.ArExplicit.Statement.fullStatement_of_mainConclusions`.
-- source:
--   OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 199; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/An-explicit-counterexample-to-the-Auslander-Reiten-conjecture-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algebra at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ031A049
import Definitions.Def_OAIQ031A052
import Definitions.Def_OAIQ031A053
import Definitions.Def_OAIQ031A056
import Definitions.Def_OAIQ031A057
import Definitions.Def_OAIQ031A058
import Definitions.Def_OAIQ031A059
import Definitions.Def_OAIQ031A060

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_BaseChange_ScalarExtensionStructure
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ArExplicit

open TensorProduct

variable {k R : Type*} [Field k] [Ring R] [Algebra k R] [Module.Finite k R]
variable (E : Type*) [Field E] [Algebra k E]

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem scalarExtension_radical_eq_kernel (f : R →ₐ[k] (ι → k))
    (hf : Function.Surjective f) (hJ : Ring.jacobson R = RingHom.ker f) :
    Ring.jacobson (E ⊗[k] R) = RingHom.ker (scalarExtensionQuotientMap E f) := by
  have hnil : IsNilpotent (RingHom.ker f) := by
    rw [← hJ]
    exact finiteAlgebra_radical_isNilpotent (k := k)
  have hid : IsNilpotent (RingHom.ker (AlgHom.id k E)) := by
    refine ⟨1, ?_⟩
    rw [Submodule.pow_one]
    ext e
    rfl
  have ht : Ring.jacobson (E ⊗[k] (ι → k)) = ⊥ :=
    jacobson_eq_bot_of_equiv (Algebra.TensorProduct.piScalarRight k E E ι).toRingEquiv
      (field_pi_jacobson_eq_bot E ι)
  rw [tensor_radical_eq_kernel (AlgHom.id k E) f Function.surjective_id hf hid hnil ht]
  ext x
  change (Algebra.TensorProduct.map (AlgHom.id k E) f) x = 0 ↔
    (Algebra.TensorProduct.piScalarRight k E E ι)
      ((Algebra.TensorProduct.map (AlgHom.id E E) f) x) = 0
  have heq : (Algebra.TensorProduct.map (AlgHom.id k E) f) x =
      (Algebra.TensorProduct.map (AlgHom.id E E) f) x := by
    induction x with
    | zero => simp
    | tmul e r => rfl
    | add x y hx hy => simp only [map_add, hx, hy]
  rw [heq]
  exact ⟨fun h => by rw [h, map_zero], fun h =>
    (Algebra.TensorProduct.piScalarRight k E E ι).injective (by simpa using h)⟩

noncomputable def scalarExtension_semisimpleQuotientEquiv (f : R →ₐ[k] (ι → k))
    (hf : Function.Surjective f) (hJ : Ring.jacobson R = RingHom.ker f) :
    (E ⊗[k] R ⧸ Ring.jacobson (E ⊗[k] R)) ≃ₐ[E] (ι → E) :=
  (Ideal.quotientEquivAlgOfEq E (scalarExtension_radical_eq_kernel E f hf hJ)).trans
    (Ideal.quotientKerAlgEquivOfSurjective (scalarExtensionQuotientMap_surjective E f hf))

end ArExplicit

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Fibers_FiberProjectionProfile
attribute [-instance] _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ArExplicit.TriangleGradedSequence
open CategoryTheory CategoryTheory.Pretriangulated
universe u v w
variable (k : Type u) [Field k]
variable {C : Type w} [Category.{v} C] [Preadditive C] [Linear k C]
variable [Limits.HasZeroObject C] [HasShift C ℤ]
variable [∀ n : ℤ, (CategoryTheory.shiftFunctor C n).Additive] [Pretriangulated C]
variable (T : Triangle C) (hT : T ∈ distTriang C) (X : C)
include hT

theorem first_injective_of_previous_surjective (n : ℤ)
    (hs : Function.Surjective (second k T X n)) :
    Function.Injective (first k T X (n+1)) := by
  have hc : connecting k T X n = 0 := by
    apply LinearMap.ext
    intro x
    have hx : x ∈ LinearMap.range (second k T X n) := hs x
    rw [exact_top k T X hT n] at hx
    exact hx
  rw [← LinearMap.ker_eq_bot, ← exact_next k T X hT n, hc, LinearMap.range_zero]

theorem first_positive_bijective
    (hpos : ∀ n : ℤ, 0 < n → Subsingleton (Top T X n))
    (hs₀ : Function.Surjective (second k T X 0)) (n : ℤ) (hn : 0 < n) :
    Function.Bijective (first k T X n) := by
  constructor
  · have hs : Function.Surjective (second k T X (n-1)) := by
      by_cases h1 : n = 1
      · subst n
        exact hs₀
      · let := hpos (n-1) (by omega)
        exact second_surjective_of_top_subsingleton k T X (n-1)
    generalize hm : n - 1 = m at hs
    have he : n = m + 1 := by omega
    subst n
    exact first_injective_of_previous_surjective k T hT X m hs
  · let := hpos n hn
    exact first_surjective_of_top_subsingleton k T hT X n

theorem first_zero_injective [Subsingleton (Top T X (-1))] :
    Function.Injective (first k T X 0) := by
  have hinj := first_injective_of_previous_surjective k T hT X (-1)
    (second_surjective_of_top_subsingleton k T X (-1))
  exact hinj

end ArExplicit.TriangleGradedSequence

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Fibers_FiberProjectionZero
attribute [-instance] _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ArExplicit.TriangleGradedSequence
open CategoryTheory CategoryTheory.Pretriangulated
universe u v w
variable (k : Type u) [Field k] [CharP k 2]
variable {C : Type w} [Category.{v} C] [Preadditive C] [Linear k C]
variable [Limits.HasZeroObject C] [HasShift C ℤ]
variable [∀ n : ℤ, (CategoryTheory.shiftFunctor C n).Additive] [Pretriangulated C]
variable (T : Triangle C) (hT : T ∈ distTriang C) (X : C)
variable (em : Middle T X 0 ≃ₗ[k] k × k) (et : Top T X 0 ≃ₗ[k] k)
variable (c : k) (hc : c ≠ 0)
variable (hrow : ∀ m, et (second k T X 0 m) = c * ((em m).1 + (em m).2))

variable [Subsingleton (Top T X (-1))]

theorem zeroDiagonalProjection_bijective :
    Function.Bijective (zeroDiagonalProjection k T hT X em et c hc hrow) := by
  constructor
  · intro x y h
    apply first_zero_injective k T hT X
    apply em.injective
    exact congrArg Subtype.val h
  · intro z
    have hz : second k T X 0 (em.symm z.val) = 0 := by
      apply et.injective
      rw [hrow, em.apply_symm_apply, map_zero]
      rw [CharTwo.add_eq_zero.mpr z.property, mul_zero]
    have hm : em.symm z.val ∈ LinearMap.range (first k T X 0) := by
      rw [exact_middle k T X hT 0]
      exact hz
    obtain ⟨x, hx⟩ := hm
    refine ⟨x, Subtype.ext ?_⟩
    change em (first k T X 0 x) = z.val
    rw [hx, em.apply_symm_apply]

def zeroDiagonalEquiv : Bottom T X 0 ≃ₗ[k] diagonalSubmodule (k := k) (V := k) :=
  LinearEquiv.ofBijective (zeroDiagonalProjection k T hT X em et c hc hrow)
    (zeroDiagonalProjection_bijective k T hT X em et c hc hrow)

end ArExplicit.TriangleGradedSequence

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Fibers_FiberDiagonalGenerator
attribute [-instance] _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ArExplicit.TriangleGradedSequence
open CategoryTheory CategoryTheory.Pretriangulated
universe u v w
variable (k : Type u) [Field k] [CharP k 2]
variable {C : Type w} [Category.{v} C] [Preadditive C] [Linear k C]
variable [Limits.HasZeroObject C] [HasShift C ℤ]
variable [∀ n : ℤ, (CategoryTheory.shiftFunctor C n).Additive] [Pretriangulated C]
variable (T : Triangle C) (hT : T ∈ distTriang C) (X : C)
variable (em : Middle T X 0 ≃ₗ[k] k × k) (et : Top T X 0 ≃ₗ[k] k)
variable (c : k) (hc : c ≠ 0)
variable (hrow : ∀ m, et (second k T X 0 m) = c * ((em m).1 + (em m).2))
variable [Subsingleton (Top T X (-1))]

def zeroScalarEquiv : Bottom T X 0 ≃ₗ[k] k :=
  (zeroDiagonalEquiv k T hT X em et c hc hrow).trans (scalarDiagonalEquiv k)

def diagonalGenerator : Bottom T X 0 :=
  (zeroScalarEquiv k T hT X em et c hc hrow).symm 1

@[simp] theorem zeroScalarEquiv_diagonalGenerator :
    zeroScalarEquiv k T hT X em et c hc hrow (diagonalGenerator k T hT X em et c hc hrow) = 1 :=
  LinearEquiv.apply_symm_apply _ _

theorem diagonalGenerator_image :
    em (first k T X 0 (diagonalGenerator k T hT X em et c hc hrow)) = (1,1) := by
  have h := congrArg Subtype.val
    ((zeroDiagonalEquiv k T hT X em et c hc hrow).apply_symm_apply
      ((scalarDiagonalEquiv k).symm 1))
  exact h

end ArExplicit.TriangleGradedSequence

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_HomComplex_FullHomCompositionSquare
attribute [-instance] _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CochainComplex.HomComplex
namespace ArExplicit
universe u v w
variable (k : Type u) [CommRing k]
variable {C : Type w} [Category.{v} C] [Preadditive C] [Linear k C]
variable {K L M N P : CochainComplex C ℤ}
variable {a : L ⟶ M} {b : M ⟶ N} {c : L ⟶ P} {d : P ⟶ N}
include k

theorem fullHomPostcomp_square (n : ℤ)
    (h : (HomotopyCategory.quotient C _).map (a ≫ b) =
      (HomotopyCategory.quotient C _).map (c ≫ d))
    (x : CohomologyClass K L n) :
    fullHomPostcomp b n (fullHomPostcomp a n x) =
      fullHomPostcomp d n (fullHomPostcomp c n x) := by
  rw [fullHomPostcomp_comp, fullHomPostcomp_comp]
  exact fullHomPostcomp_congr k n h x

end ArExplicit

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_HomComplex_FullHomZeroRepresentative
attribute [-instance] _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CochainComplex.HomComplex
namespace ArExplicit
universe u v w
variable {C : Type w} [Category.{v} C] [Preadditive C]
variable {K L : CochainComplex C ℤ}

variable (k : Type u) [CommRing k] [Linear k C]

include k in
theorem fullHomZero_class_eq_iff (f g : K ⟶ L) :
    CohomologyClass.mk (Cocycle.ofHom f) = CohomologyClass.mk (Cocycle.ofHom g) ↔
      (HomotopyCategory.quotient C _).map f = (HomotopyCategory.quotient C _).map g := by
  constructor
  · intro h
    rw [← fullHomPrecomp_identity f, ← fullHomPrecomp_identity g] at h
    have hh := congrArg (fullHomShiftedHomotopyEquiv k K L 0) h
    rw [fullHomShiftedHomotopyEquiv_precomp, fullHomShiftedHomotopyEquiv_precomp] at hh
    change _ ≫ fullHomShiftedHomotopyEquiv k L L 0 (CompleteComparison.fullHomIdentity L) =
      _ ≫ fullHomShiftedHomotopyEquiv k L L 0 (CompleteComparison.fullHomIdentity L) at hh
    rw [fullHomShiftedHomotopyEquiv_identity] at hh
    exact (cancel_mono _).1 hh
  · intro h
    rw [← fullHomPrecomp_identity f, ← fullHomPrecomp_identity g]
    exact fullHomPrecomp_congr k 0 h _

end ArExplicit

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_HomComplex_FullHomZeroProjection
attribute [-instance] _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CochainComplex.HomComplex
namespace ArExplicit
universe u v w
variable {C : Type w} [Category.{v} C] [Preadditive C]
variable {K L M : CochainComplex C ℤ}

variable (k : Type u) [CommRing k] [Linear k C]

include k in
theorem fullHomZero_projection_inverse (f : K ⟶ L) (g : L ⟶ K)
    (e : (HomotopyCategory.quotient C _).obj L ≅ (HomotopyCategory.quotient C _).obj K)
    (he : (HomotopyCategory.quotient C _).map g = e.hom)
    (h : fullHomPostcomp g 0 (CohomologyClass.mk (Cocycle.ofHom f)) =
      CohomologyClass.mk (Cocycle.ofHom (𝟙 K))) :
    (HomotopyCategory.quotient C _).map f = e.inv := by
  rw [fullHomPostcomp_ofHom] at h
  have hh := (fullHomZero_class_eq_iff k (f ≫ g) (𝟙 K)).mp h
  rw [CategoryTheory.Functor.map_comp, he, CategoryTheory.Functor.map_id] at hh
  apply (cancel_mono e.hom).1
  exact hh.trans e.inv_hom_id.symm

end ArExplicit

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Modules_TrivialInduction
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.Resolution.instIsScalarTowerTSimple _root_.OAI.ArExplicit.Resolution.instModuleTSimple _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ArExplicit.TrivialInduction

variable {k R : Type*} [CommRing k] [Ring R] [Algebra k R]

local notation "T" => TrivialExtension k R

instance instIsScalarTowerTrivialExtensionQuotient : IsScalarTower k T (Quotient (k := k) (R := R)) where
  smul_assoc a t r := smul_assoc a t.base r

end ArExplicit.TrivialInduction

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Resolutions_TrivialInductionQuotient
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.moduleCatBaseComm _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory
namespace ArExplicit.TrivialInduction
universe u
variable {k R : Type u} [Field k] [Ring R] [Algebra k R]
attribute [local instance] moduleCatBaseModule moduleCatBaseTower

instance baseComm (M : ModuleCat.{u} R) : SMulCommClass k R M where
  smul_comm a r m := by
    change (algebraMap k R a) • (r • m) = r • ((algebraMap k R a) • m)
    rw [← mul_smul, Algebra.commutes a r, mul_smul]

end ArExplicit.TrivialInduction

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Triangular_TriangularCrossHom
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ArExplicit.TriangularInduction

open CategoryTheory CochainComplex.HomComplex

universe u

variable {k R F : Type u} [Field k] [Ring R] [Algebra k R]
variable [AddCommGroup F] [Module k F] [Module R F] [Module Rᵐᵒᵖ F]
variable [SMulCommClass k R F] [SMulCommClass R Rᵐᵒᵖ F]
variable [IsScalarTower k R F] [IsScalarTower k Rᵐᵒᵖ F] [SMulCommClass k Rᵐᵒᵖ F]

attribute [local instance] moduleCatBaseModule moduleCatBaseTower

abbrev tensorCochain (P : CochainComplex (ModuleCat.{u} R) ℤ) :=
  ((BalancedTensor.functor (k := k) (R := R) (S := R) (F := F)).mapHomologicalComplex _).obj P

end ArExplicit.TriangularInduction

end

end OAI
end


