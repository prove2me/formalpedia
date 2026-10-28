-- Prove2me | Definitions.Def_OAIQ031A116
-- name    : OAIQ031A116
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T14:51:13.412963+00:00
-- url     : https://prove2.me/theorems/961781da-5ca4-473c-ad87-19043977066e
-- title:
--   Definitions bundle OAIQ031A116 of the split of OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.ArExplicit.Statement.main`, carved from OpenAI's openai/math development (OpenAI, *An explicit counterexample to the Auslander-Reiten conjecture (result family 199)*, OpenAI Math Release, September 23, 2026, result family 199, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 16 declarations of OpenAI's Lean: 7 definitions, 1 instance and 8 theorems. The definitions and types are `OAI.ArExplicit.T.tensorEndpoint`, `OAI.ArExplicit.TriangularInduction.comparisonSourceEquiv`, `OAI.ArExplicit.TriangularInduction.crossChainMap`, `OAI.ArExplicit.TriangularInduction.crossCochainEquiv`, `OAI.ArExplicit.TriangularInduction.crossCohomologyEquiv`, `OAI.ArExplicit.TriangularInduction.crossFullHomEquivalence`, `OAI.ArExplicit.TriangularInduction.tensorComparison`.
--
--   **Sources.** They come from these modules of lean/OAI/Algebra, in whole or in part: [`AuslanderReiten_Cones_TwoConeSkeleton`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Cones/TwoConeSkeleton.lean), [`AuslanderReiten_Coordinates_TensorComparisonHomotopy`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Coordinates/TensorComparisonHomotopy.lean), [`AuslanderReiten_Coordinates_TensorComparisonScalar`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Coordinates/TensorComparisonScalar.lean), [`AuslanderReiten_Coordinates_TensorTopComparison`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Coordinates/TensorTopComparison.lean), [`AuslanderReiten_Triangular_TriangularComparison`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Triangular/TriangularComparison.lean), [`AuslanderReiten_Triangular_TriangularComparisonTransport`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Triangular/TriangularComparisonTransport.lean), [`AuslanderReiten_Triangular_TriangularCrossHom`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Triangular/TriangularCrossHom.lean), [`AuslanderReiten_Triangular_TriangularProjective`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Triangular/TriangularProjective.lean).
--
--   **Imports.** It imports the bundles `OAIQ031A076`, `OAIQ031A092`, `OAIQ031A100`, `OAIQ031A102` and `OAIQ031A103` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ031A126`, `OAIQ031A127` and `OAIQ031A128`.
-- source:
--   OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 199; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/An-explicit-counterexample-to-the-Auslander-Reiten-conjecture-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algebra at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ031A076
import Definitions.Def_OAIQ031A092
import Definitions.Def_OAIQ031A100
import Definitions.Def_OAIQ031A102
import Definitions.Def_OAIQ031A103

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Cones_TwoConeSkeleton
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory

namespace ArExplicit.TwoCone

universe u
variable {R : Type u} [Ring R] (D : Data R)

theorem middleD_exact (hex : ∀ n, Function.Exact (D.d (n + 1)) (D.d n)) (n : ℕ) :
    Function.Exact (middleD D (n + 1)) (middleD D n) := by
  rintro ⟨x, y⟩
  constructor
  · intro h
    obtain ⟨a, ha⟩ := (hex (n + 2) x).mp (congrArg Prod.fst h)
    obtain ⟨b, hb⟩ := (hex (n + 2) y).mp (congrArg Prod.snd h)
    exact ⟨(a, b), Prod.ext ha hb⟩
  · rintro ⟨⟨a, b⟩, h⟩
    exact Prod.ext ((hex (n + 2) x).mpr ⟨a, congrArg Prod.fst h⟩)
      ((hex (n + 2) y).mpr ⟨b, congrArg Prod.snd h⟩)

end ArExplicit.TwoCone

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Triangular_TriangularProjective
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.EnvelopingBimodule.regular_projective _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.TriangularInduction.instAdditiveModuleCatTriangularEFunctor _root_.OAI.ArExplicit.TriangularInduction.instAdditiveModuleCatTriangularJFunctor _root_.OAI.ArExplicit.TriangularInduction.instFaithfulModuleCatTriangularEFunctor _root_.OAI.ArExplicit.TriangularInduction.instFaithfulModuleCatTriangularJFunctor _root_.OAI.ArExplicit.TriangularInduction.instFullModuleCatTriangularEFunctor _root_.OAI.ArExplicit.TriangularInduction.instFullModuleCatTriangularJFunctor _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ArExplicit.TriangularInduction

variable {k R F : Type*} [CommRing k] [Ring R] [Algebra k R]
variable [AddCommGroup F] [Module k F] [Module R F] [Module Rᵐᵒᵖ F]
variable [SMulCommClass k R F] [SMulCommClass R Rᵐᵒᵖ F]
variable [IsScalarTower k R F] [IsScalarTower k Rᵐᵒᵖ F] [SMulCommClass k Rᵐᵒᵖ F]

omit [IsScalarTower k R F] [SMulCommClass k Rᵐᵒᵖ F] in
theorem eRegular_split :
    (eRegularProjection (k := k) (R := R) (F := F)).comp eRegularInclusion = LinearMap.id := by
  apply LinearMap.ext
  intro x
  ext
  · rfl
  · exact (BalancedTensor.runitLeft (S := R)).symm_apply_apply x.bottom

instance eRegular_projective : Module.Projective (Triangular R F) (TriangularE k R F R) :=
  Module.Projective.of_split eRegularInclusion eRegularProjection eRegular_split

end ArExplicit.TriangularInduction

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Triangular_TriangularCrossHom
attribute [-instance] _root_.OAI.ArExplicit.BalancedTensor.functor_linear _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.EnvelopingBimodule.regular_projective _root_.OAI.ArExplicit.ExternalTensor.hasHomCochainTotal _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.TrivialInduction.baseComm _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
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

variable (P Q : CochainComplex (ModuleCat.{u} R) ℤ) (n : ℤ)

def crossCochainEquiv : Cochain P (tensorCochain (k := k) (F := F) Q) n ≃+
    Cochain (jCochain (k := k) (F := F) P) (eCochain (k := k) (F := F) Q) n where
  toFun x := Cochain.mk fun p q hpq => crossHomAdd (P.X p) (Q.X q) (x.v p q hpq)
  invFun x := Cochain.mk fun p q hpq => ModuleCat.ofHom (TriangularModule.bottomMap (x.v p q hpq).hom)
  left_inv x := by
    apply Cochain.ext
    intro p q hpq
    rfl
  right_inv x := by
    apply Cochain.ext
    intro p q hpq
    apply ModuleCat.hom_ext
    exact jHom_bottomMap _
  map_add' x y := by
    apply Cochain.ext
    intro p q hpq
    exact map_add (crossHomAdd (P.X p) (Q.X q)) (x.v p q hpq) (y.v p q hpq)

@[simp] theorem crossCochainEquiv_v
    (x : Cochain P (tensorCochain (k := k) (F := F) Q) n) (p q : ℤ) (hpq : p+n=q) :
    (crossCochainEquiv P Q n x).v p q hpq = crossHomAdd (P.X p) (Q.X q) (x.v p q hpq) := rfl

theorem crossCochainEquiv_differential (m : ℤ)
    (x : Cochain P (tensorCochain (k := k) (F := F) Q) n) :
    δ n m (crossCochainEquiv P Q n x) = crossCochainEquiv P Q m (δ n m x) := by
  by_cases hnm : n+1=m
  · apply Cochain.ext
    intro p q hpq
    simp only [δ_v n m hnm _ p q hpq (q-1) (p+1) rfl rfl, crossCochainEquiv_v]
    let x₁ : P.X p ⟶ (BalancedTensor.functor (k := k) (R := R) (S := R) (F := F)).obj (Q.X (q-1)) :=
      x.v p (q-1) (by omega)
    let x₂ : P.X (p+1) ⟶ (BalancedTensor.functor (k := k) (R := R) (S := R) (F := F)).obj (Q.X q) :=
      x.v (p+1) q (by omega)
    change crossHomAdd _ _ x₁ ≫ (eFunctor k R F).map (Q.d (q-1) q) +
      m.negOnePow • ((jFunctor k R F).map (P.d p (p+1)) ≫ crossHomAdd _ _ x₂) =
      crossHomAdd (P.X p) (Q.X q) (x₁ ≫
        (BalancedTensor.functor (k := k) (R := R) (S := R) (F := F)).map (Q.d (q-1) q) +
          m.negOnePow • (P.d p (p+1) ≫ x₂))
    rw [map_add]
    simp only [Units.smul_def, map_zsmul]
    rw [crossHomAdd_target, crossHomAdd_source]
  · rw [δ_shape n m hnm, δ_shape n m hnm, map_zero]

def crossFullHomEquivalence : FullHomEquivalence P (tensorCochain (k := k) (F := F) Q)
    (jCochain (k := k) (F := F) P) (eCochain (k := k) (F := F) Q) where
  cochain := crossCochainEquiv P Q
  differential := crossCochainEquiv_differential P Q

def crossCohomologyEquiv :
    CohomologyClass P (tensorCochain (k := k) (F := F) Q) n ≃+
      CohomologyClass (jCochain (k := k) (F := F) P) (eCochain (k := k) (F := F) Q) n :=
  (crossFullHomEquivalence P Q).cohomology n

variable {P Q n}

def crossChainMap (f : P ⟶ tensorCochain (k := k) (F := F) Q) :
    jCochain (k := k) (F := F) P ⟶ eCochain (k := k) (F := F) Q where
  f i := crossHomAdd (P.X i) (Q.X i) (f.f i)
  comm' i j _ := by
    change crossHomAdd _ _ (f.f i) ≫ (eFunctor k R F).map (Q.d i j) =
      (jFunctor k R F).map (P.d i j) ≫ crossHomAdd _ _ (f.f j)
    exact (crossHomAdd_target (f.f i) (Q.d i j)).symm.trans
      ((congrArg (crossHomAdd (P.X i) (Q.X j)) (f.comm i j)).trans
        (crossHomAdd_source (P.d i j) (f.f j)))

end ArExplicit.TriangularInduction

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Triangular_TriangularComparison
attribute [-instance] _root_.OAI.ArExplicit.BalancedTensor.functor_linear _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
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
variable {P : CochainComplex (ModuleCat.{u} R) ℤ}
variable (v : P ⟶ tensorCochain (k := k) (F := F) P) (n : ℤ)

@[simp] theorem crossCohomologyEquiv_mk
    (x : Cocycle P (tensorCochain (k := k) (F := F) P) n) :
    crossCohomologyEquiv P P n (CohomologyClass.mk x) =
      CohomologyClass.mk ((crossFullHomEquivalence P P).cocycle n x) := rfl

def tensorComparison : (CohomologyClass P P n × CohomologyClass P P n) →+
    CohomologyClass P (tensorCochain (k := k) (F := F) P) n where
  toFun x := fullHomPostcomp v n x.2 + (n+1).negOnePow • fullHomPrecomp v n
    (mapFullHom (BalancedTensor.functor (k := k) (R := R) (S := R) (F := F)) P P n x.1)
  map_zero' := by simp
  map_add' x y := by simp [smul_add]; abel

end ArExplicit.TriangularInduction

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Coordinates_TensorComparisonHomotopy
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
variable {k R F : Type u} [Field k] [Ring R] [Algebra k R]
variable [AddCommGroup F] [Module k F] [Module R F] [Module Rᵐᵒᵖ F]
variable [SMulCommClass k R F] [SMulCommClass R Rᵐᵒᵖ F]
variable [IsScalarTower k R F] [IsScalarTower k Rᵐᵒᵖ F] [SMulCommClass k Rᵐᵒᵖ F]
attribute [local instance] moduleCatBaseModule moduleCatBaseTower
variable {P : CochainComplex (ModuleCat.{u} R) ℤ}
variable {v w : P ⟶ tensorCochain (k := k) (F := F) P}

omit [IsScalarTower k R F] [IsScalarTower k Rᵐᵒᵖ F] [SMulCommClass k Rᵐᵒᵖ F] in
theorem tensorComparison_congr_homotopy
    (h : (HomotopyCategory.quotient _ _).map v = (HomotopyCategory.quotient _ _).map w)
    (n : ℤ) (x : CohomologyClass P P n × CohomologyClass P P n) :
    tensorComparison v n x = tensorComparison w n x := by
  change fullHomPostcomp v n x.2 + (n+1).negOnePow •
      fullHomPrecomp v n (mapFullHom (BalancedTensor.functor (k := k) (R := R) (S := R) (F := F)) P P n x.1) =
    fullHomPostcomp w n x.2 + (n+1).negOnePow •
      fullHomPrecomp w n (mapFullHom (BalancedTensor.functor (k := k) (R := R) (S := R) (F := F)) P P n x.1)
  rw [fullHomPostcomp_congr k n h, fullHomPrecomp_congr k n h]

end ArExplicit.TriangularInduction

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Coordinates_TensorComparisonScalar
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
variable {k R F : Type u} [Field k] [CharP k 2] [Ring R] [Algebra k R]
variable [AddCommGroup F] [Module k F] [Module R F] [Module Rᵐᵒᵖ F]
variable [SMulCommClass k R F] [SMulCommClass R Rᵐᵒᵖ F]
variable [IsScalarTower k R F] [IsScalarTower k Rᵐᵒᵖ F] [SMulCommClass k Rᵐᵒᵖ F]
attribute [local instance] moduleCatBaseModule moduleCatBaseTower
variable {P : CochainComplex (ModuleCat.{u} R) ℤ}
variable (v : P ⟶ tensorCochain (k := k) (F := F) P)

omit [IsScalarTower k R F] [IsScalarTower k Rᵐᵒᵖ F] [SMulCommClass k Rᵐᵒᵖ F] in
theorem tensorComparison_scalar_row (b : tensorCochain (k := k) (F := F) P ⟶ P)
    (hunit : (HomotopyCategory.quotient (ModuleCat.{u} R) _).map (v ≫ b) = 𝟙 _)
    (n : ℤ) (c : k)
    (hscalar : ∀ z : CohomologyClass P P n,
      fullHomPostcomp b n (fullHomPrecomp v n
        (mapFullHom (BalancedTensor.functor (k := k) (R := R) (S := R) (F := F)) P P n z)) = c • z)
    (x : CohomologyClass P P n × CohomologyClass P P n) :
    fullHomPostcomp b n (tensorComparison v n x) = c • x.1 + x.2 := by
  change fullHomPostcomp b n (fullHomPostcomp v n x.2 + (n+1).negOnePow •
    fullHomPrecomp v n
      (mapFullHom (BalancedTensor.functor (k := k) (R := R) (S := R) (F := F)) P P n x.1)) = _
  rw [map_add, Units.smul_def, map_zsmul,
    fullHomPostcomp_homotopy_inverse k n v b hunit, hscalar]
  change x.2 + (n+1).negOnePow • (c • x.1) = _
  rw [TriangleGradedSequence.integerUnit_smul k, add_comm]

end ArExplicit.TriangularInduction

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Coordinates_TensorTopComparison
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.Resolution.instIsScalarTowerMulOppositeBaseAlgebraSimple _root_.OAI.ArExplicit.Resolution.simpleRightAction _root_.OAI.ArExplicit.Resolution.simpleRightModule _root_.OAI.ArExplicit.TrivialInduction.dualModule _root_.OAI.ArExplicit.TrivialInduction.induced_term_projective _root_.OAI.ArExplicit.TrivialInduction.instAdditiveModuleCatTrivialExtensionInflate _root_.OAI.ArExplicit.TrivialInduction.instIsScalarTowerTrivialExtensionCoinduced _root_.OAI.ArExplicit.TrivialInduction.instIsScalarTowerTrivialExtensionQuotient _root_.OAI.ArExplicit.TrivialInduction.instPreservesHomologyModuleCatTrivialExtensionInflate _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionCoinduced _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionMulOppositeCoinduced _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionMulOppositeQuotient _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionQuotient _root_.OAI.ArExplicit.TrivialInduction.quotientModule _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.instInjectiveMulOppositeA _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ArExplicit.T
open CategoryTheory
open scoped TensorProduct
universe u
variable {k : Type u} [Field k] [CharP k 2] (q : k) (H : kˣ)
attribute [local instance] moduleCatBaseModule moduleCatBaseTower
local notation "R" => T k q
local notation "Te" => AbsoluteBar.Enveloping k R
local notation "P₀" => AbsoluteBar.complex k R
local notation "Q₀" => AbsoluteBar.twistedComplex k R (TrivialExtension.twist H)

def tensorEndpoint :=
  ExternalTensor.bottomMap k Te Te P₀ P₀ Q₀ Q₀ 0 0 (barDb q H) (barDb q H)

end ArExplicit.T

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Triangular_TriangularComparisonTransport
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
variable {P : CochainComplex (ModuleCat.{u} R) ℤ}
variable (v : P ⟶ tensorCochain (k := k) (F := F) P) (n : ℤ)

def comparisonSourceEquiv :
    (CohomologyClass P P n × CohomologyClass P P n) ≃+
      (CohomologyClass (eCochain (k := k) (F := F) P)
        (eCochain (k := k) (F := F) P) n ×
       CohomologyClass (jCochain (k := k) (F := F) P)
        (jCochain (k := k) (F := F) P) n) :=
  AddEquiv.prodCongr (fullHomCohomologyEquiv (eFunctor k R F) P P n)
    (fullHomCohomologyEquiv (jFunctor k R F) P P n)

@[simp] theorem comparisonSourceEquiv_apply (a b : CohomologyClass P P n) :
    comparisonSourceEquiv (F := F) (P := P) n (a,b) =
      (fullHomCohomologyEquiv (eFunctor k R F) P P n a,
        fullHomCohomologyEquiv (jFunctor k R F) P P n b) := rfl

end ArExplicit.TriangularInduction

end

end OAI
end


