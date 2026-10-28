-- Prove2me | Definitions.Def_OAIQ031A127
-- name    : OAIQ031A127
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T15:02:16.573598+00:00
-- url     : https://prove2.me/theorems/d1544b9a-c540-4876-9f94-e86d49c1dad1
-- title:
--   Definitions bundle OAIQ031A127 of the split of OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.ArExplicit.Statement.main`, carved from OpenAI's openai/math development (OpenAI, *An explicit counterexample to the Auslander-Reiten conjecture (result family 199)*, OpenAI Math Release, September 23, 2026, result family 199, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 5 declarations of OpenAI's Lean: 5 theorems.
--
--   **Sources.** They come from these modules of lean/OAI/Algebra, in whole or in part: [`AuslanderReiten_Coordinates_TensorComparisonNaturality`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Coordinates/TensorComparisonNaturality.lean), [`AuslanderReiten_Coordinates_TensorComparisonProjectedRow`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Coordinates/TensorComparisonProjectedRow.lean), [`AuslanderReiten_Coordinates_TensorComparisonScalar`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Coordinates/TensorComparisonScalar.lean), [`AuslanderReiten_Coordinates_TensorComparisonZero`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Coordinates/TensorComparisonZero.lean).
--
--   **Imports.** It imports the bundle `OAIQ031A116` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ031A137`.
-- source:
--   OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 199; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/An-explicit-counterexample-to-the-Auslander-Reiten-conjecture-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algebra at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ031A116

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Coordinates_TensorComparisonNaturality
attribute [-instance] _root_.OAI.ArExplicit.BalancedTensor.functor_linear _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CochainComplex.HomComplex
namespace ArExplicit.TriangularInduction
universe u
variable {k R F G : Type u} [Field k] [Ring R] [Algebra k R]
variable [AddCommGroup F] [Module k F] [Module R F] [Module Rᵐᵒᵖ F]
variable [SMulCommClass k R F] [SMulCommClass R Rᵐᵒᵖ F]
variable [IsScalarTower k Rᵐᵒᵖ F]
variable [AddCommGroup G] [Module k G] [Module R G] [Module Rᵐᵒᵖ G]
variable [SMulCommClass k R G] [SMulCommClass R Rᵐᵒᵖ G]
variable [IsScalarTower k Rᵐᵒᵖ G]
attribute [local instance] moduleCatBaseModule moduleCatBaseTower
variable (a : F →ₗ[Rᵐᵒᵖ] G) (ha : ∀ (r : R) f, a (r • f) = r • a f)
variable {P : CochainComplex (ModuleCat.{u} R) ℤ}
variable (v : P ⟶ tensorCochain (k := k) (F := F) P) (n : ℤ)

theorem tensorComparison_natural
    (x : CohomologyClass P P n × CohomologyClass P P n) :
    fullHomPostcomp (BalancedTensor.complexMap (k := k) a ha P) n
      (tensorComparison v n x) =
    tensorComparison (v ≫ BalancedTensor.complexMap (k := k) a ha P) n x := by
  let t := BalancedTensor.complexMap (k := k) a ha P
  have ht : t = ((BalancedTensor.naturalMap (k := k) a ha).mapHomologicalComplex _).app P := rfl
  have hn (z : CohomologyClass P P n) :
      fullHomPostcomp t n (fullHomPrecomp v n
        (mapFullHom (BalancedTensor.functor (k := k) (R := R) (S := R) (F := F)) P P n z)) =
      fullHomPrecomp (v ≫ t) n
        (mapFullHom (BalancedTensor.functor (k := k) (R := R) (S := R) (F := G)) P P n z) := by
    rw [fullHomPostcomp_precomp, ht, mapFullHom_naturality, fullHomPrecomp_comp]
  change fullHomPostcomp t n (fullHomPostcomp v n x.2 + (n+1).negOnePow •
      fullHomPrecomp v n
        (mapFullHom (BalancedTensor.functor (k := k) (R := R) (S := R) (F := F)) P P n x.1)) =
    fullHomPostcomp (v ≫ t) n x.2 + (n+1).negOnePow •
      fullHomPrecomp (v ≫ t) n
        (mapFullHom (BalancedTensor.functor (k := k) (R := R) (S := R) (F := G)) P P n x.1)
  rw [map_add, Units.smul_def, map_zsmul, fullHomPostcomp_comp, hn]
  rfl

end ArExplicit.TriangularInduction

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Coordinates_TensorComparisonScalar
attribute [-instance] _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CochainComplex.HomComplex
open scoped ModuleCat.Algebra
namespace ArExplicit.TriangularInduction
universe u
variable {k R F : Type u} [Field k] [CharP k 2] [Ring R] [Algebra k R]
variable [AddCommGroup F] [Module k F] [Module R F] [Module Rᵐᵒᵖ F]
variable [SMulCommClass k R F] [SMulCommClass R Rᵐᵒᵖ F]
variable [IsScalarTower k R F] [IsScalarTower k Rᵐᵒᵖ F] [SMulCommClass k Rᵐᵒᵖ F]
attribute [local instance] moduleCatBaseModule moduleCatBaseTower
variable {P : CochainComplex (ModuleCat.{u} R) ℤ}
variable (v : P ⟶ tensorCochain (k := k) (F := F) P)

omit [CharP k 2] [IsScalarTower k R F] [IsScalarTower k Rᵐᵒᵖ F]
  [SMulCommClass k Rᵐᵒᵖ F] in
theorem tensorComparison_bijective_of_coordinates (n : ℤ)
    (E : CohomologyClass P (tensorCochain (k := k) (F := F) P) n ≃ₗ[k]
      (CohomologyClass P P n × CohomologyClass P P n))
    (a b : k) (hab : a ≠ b)
    (hE : ∀ x, E (tensorComparison v n x) = twoTwistLinear a b x) :
    Function.Bijective (tensorComparison v n) := by
  constructor
  · intro x y h
    apply twoTwistLinear_injective a b hab
    rw [← hE, ← hE, h]
  · intro y
    obtain ⟨x, hx⟩ := twoTwistLinear_surjective a b hab (E y)
    exact ⟨x, E.injective ((hE x).trans hx)⟩

end ArExplicit.TriangularInduction

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Coordinates_TensorComparisonProjectedRow
attribute [-instance] _root_.OAI.ArExplicit.BalancedTensor.functor_linear _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CochainComplex.HomComplex
open scoped ModuleCat.Algebra
namespace ArExplicit.TriangularInduction
universe u
variable {k R F G : Type u} [Field k] [CharP k 2] [Ring R] [Algebra k R]
variable [AddCommGroup F] [Module k F] [Module R F] [Module Rᵐᵒᵖ F]
variable [SMulCommClass k R F] [SMulCommClass R Rᵐᵒᵖ F]
variable [IsScalarTower k R F] [IsScalarTower k Rᵐᵒᵖ F] [SMulCommClass k Rᵐᵒᵖ F]
variable [AddCommGroup G] [Module k G] [Module R G] [Module Rᵐᵒᵖ G]
variable [SMulCommClass k R G] [SMulCommClass R Rᵐᵒᵖ G]
variable [IsScalarTower k R G] [IsScalarTower k Rᵐᵒᵖ G] [SMulCommClass k Rᵐᵒᵖ G]
attribute [local instance] moduleCatBaseModule moduleCatBaseTower
variable (a : F →ₗ[Rᵐᵒᵖ] G) (ha : ∀ (r : R) f, a (r • f) = r • a f)
variable {P : CochainComplex (ModuleCat.{u} R) ℤ}
variable (v : P ⟶ tensorCochain (k := k) (F := F) P)
variable (w : P ⟶ tensorCochain (k := k) (F := G) P)
variable (b : tensorCochain (k := k) (F := G) P ⟶ P)

omit [IsScalarTower k R F] [SMulCommClass k Rᵐᵒᵖ F]
    [IsScalarTower k R G] [SMulCommClass k Rᵐᵒᵖ G] in
theorem tensorComparison_projected_row
    (hprojection : (HomotopyCategory.quotient _ _).map
      (v ≫ BalancedTensor.complexMap (k := k) a ha P) =
        (HomotopyCategory.quotient _ _).map w)
    (hunit : (HomotopyCategory.quotient _ _).map (w ≫ b) = 𝟙 _)
    (n : ℤ) (c : k)
    (hscalar : ∀ z : CohomologyClass P P n,
      fullHomPostcomp b n (fullHomPrecomp w n
        (mapFullHom (BalancedTensor.functor (k := k) (R := R) (S := R) (F := G)) P P n z)) = c • z)
    (x : CohomologyClass P P n × CohomologyClass P P n) :
    fullHomPostcomp b n
      (fullHomPostcomp (BalancedTensor.complexMap (k := k) a ha P) n
        (tensorComparison v n x)) = c • x.1 + x.2 := by
  rw [tensorComparison_natural]
  rw [tensorComparison_congr_homotopy (k := k) hprojection n x]
  exact tensorComparison_scalar_row w b hunit n c hscalar x

end ArExplicit.TriangularInduction

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Coordinates_TensorComparisonZero
attribute [-instance] _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CochainComplex.HomComplex
open scoped ModuleCat.Algebra
namespace ArExplicit.TriangularInduction
universe u
variable {k R F : Type u} [Field k] [Ring R] [Algebra k R]
variable [AddCommGroup F] [Module k F] [Module R F] [Module Rᵐᵒᵖ F]
variable [SMulCommClass k R F] [SMulCommClass R Rᵐᵒᵖ F]
variable [IsScalarTower k R F]
attribute [local instance] moduleCatBaseModule moduleCatBaseTower
variable {P : CochainComplex (ModuleCat.{u} R) ℤ}
variable (v : P ⟶ tensorCochain (k := k) (F := F) P)

theorem tensorComparison_scalarIdentity (a b : k) :
    tensorComparison v 0
      (a • CohomologyClass.mk (Cocycle.ofHom (𝟙 P)),
       b • CohomologyClass.mk (Cocycle.ofHom (𝟙 P))) =
      (b-a) • CohomologyClass.mk (Cocycle.ofHom v) := by
  change fullHomPostcomp v 0 (b • CohomologyClass.mk (Cocycle.ofHom (𝟙 P))) +
    (0+1 : ℤ).negOnePow • fullHomPrecomp v 0
      (mapFullHom (BalancedTensor.functor (k := k) (R := R) (S := R) (F := F)) P P 0
        (a • CohomologyClass.mk (Cocycle.ofHom (𝟙 P)))) = _
  rw [fullHomPostcomp_smul, fullHomPostcomp_identity, mapFullHom_smul,
    mapFullHom_identity, fullHomPrecomp_smul, fullHomPrecomp_identity]
  rw [show (0+1 : ℤ).negOnePow = (-1 : ℤˣ) by decide, Units.smul_def]
  change b • CohomologyClass.mk (Cocycle.ofHom v) +
    (-1 : ℤ) • (a • CohomologyClass.mk (Cocycle.ofHom v)) = _
  rw [neg_one_zsmul, sub_smul, sub_eq_add_neg]

theorem tensorComparison_zero_nonzero_kernel
    (hid : CohomologyClass.mk (Cocycle.ofHom (𝟙 P)) ≠ 0) :
    ∃ w : CohomologyClass P P 0 × CohomologyClass P P 0,
      w ≠ 0 ∧ tensorComparison v 0 w = 0 := by
  refine ⟨(CohomologyClass.mk (Cocycle.ofHom (𝟙 P)),
    CohomologyClass.mk (Cocycle.ofHom (𝟙 P))), ?_, ?_⟩
  · intro hw
    exact hid (congrArg Prod.fst hw)
  · simpa only [one_smul, sub_self, zero_smul] using
      tensorComparison_scalarIdentity v (1 : k) 1

end ArExplicit.TriangularInduction

end

end OAI
end


