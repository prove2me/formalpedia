-- Prove2me | Definitions.Def_OAIQ031A067
-- name    : OAIQ031A067
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T14:14:20.56339+00:00
-- url     : https://prove2.me/theorems/af8a43b1-50fa-46de-9e06-7d60cf9be63f
-- title:
--   Definitions bundle OAIQ031A067 of the split of OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.ArExplicit.Statement.main`, carved from OpenAI's openai/math development (OpenAI, *An explicit counterexample to the Auslander-Reiten conjecture (result family 199)*, OpenAI Math Release, September 23, 2026, result family 199, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 13 declarations of OpenAI's Lean: 1 definition and 12 theorems. The definitions and types are `OAI.ArExplicit.BalancedTensor.runitLeft`.
--
--   **Sources.** They come from these modules of lean/OAI/Algebra, in whole or in part: [`AuslanderReiten_Algebras_SimpleModule`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Algebras/SimpleModule.lean), [`AuslanderReiten_Cocycles_CocycleDetector`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Cocycles/CocycleDetector.lean), [`AuslanderReiten_Ext_TensorExtCoefficients`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Ext/TensorExtCoefficients.lean), [`AuslanderReiten_Homology_VectorCochainKunnethLiteral`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Homology/VectorCochainKunnethLiteral.lean), [`AuslanderReiten_Resolutions_ResolutionExtIdentity`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Resolutions/ResolutionExtIdentity.lean), [`AuslanderReiten_Resolutions_ResolutionExtZero`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Resolutions/ResolutionExtZero.lean), [`AuslanderReiten_Resolutions_ResolutionProductCompatibility`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Resolutions/ResolutionProductCompatibility.lean), [`AuslanderReiten_Tensor_BalancedTensorPi`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Tensor/BalancedTensorPi.lean), [`AuslanderReiten_Tensor_BalancedTensorUnit`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Tensor/BalancedTensorUnit.lean), [`AuslanderReiten_Tensor_ExternalTensorScalarProducts`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Tensor/ExternalTensorScalarProducts.lean).
--
--   **Imports.** It imports the bundles `OAIQ031A044`, `OAIQ031A048`, `OAIQ031A049`, `OAIQ031A050` and `OAIQ031A051` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ031A081`, `OAIQ031A082`, `OAIQ031A083` and `OAIQ031A103`.
-- source:
--   OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 199; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/An-explicit-counterexample-to-the-Auslander-Reiten-conjecture-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algebra at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ031A044
import Definitions.Def_OAIQ031A048
import Definitions.Def_OAIQ031A049
import Definitions.Def_OAIQ031A050
import Definitions.Def_OAIQ031A051

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Algebras_SimpleModule
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.Resolution.instIsScalarTowerMulOppositeBaseAlgebraSimple _root_.OAI.ArExplicit.Resolution.instIsScalarTowerTSimple _root_.OAI.ArExplicit.Resolution.instModuleTSimple _root_.OAI.ArExplicit.Resolution.simpleRightAction _root_.OAI.ArExplicit.Resolution.simpleRightModule _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open CategoryTheory

namespace ArExplicit.Resolution

open ArExplicit.Letter ArExplicit.BaseAlgebra

variable {k : Type*} [Field k] (q : k)

local notation "C" => BaseAlgebra k q

theorem e_smul_simple (hq : 1 + q ≠ 0) (a : Simple q) : basisVector q e • a = 0 := by
  apply simpleCoordinate_injective q hq
  rw [simpleCoordinate_smul, map_zero]
  simp

theorem hom_E_simple_eq_zero (hq : 1 + q ≠ 0) (g : E q →ₗ[C] Simple q) : g = 0 := by
  have hz : g (vertexE q) = 0 := by
    calc
      g (vertexE q) = g (basisVector q e • vertexE q) := congrArg g (e_smul_vertexE q).symm
      _ = basisVector q e • g (vertexE q) := g.map_smul _ _
      _ = 0 := e_smul_simple q hq _
  ext a
  calc
    g a = g ((a : C) • vertexE q) := congrArg g (smul_vertexE q a).symm
    _ = (a : C) • g (vertexE q) := g.map_smul _ _
    _ = 0 := by rw [hz, smul_zero]

end ArExplicit.Resolution

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Cocycles_CocycleDetector
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.Resolution.instIsScalarTowerMulOppositeBaseAlgebraSimple _root_.OAI.ArExplicit.Resolution.simpleRightAction _root_.OAI.ArExplicit.Resolution.simpleRightModule _root_.OAI.ArExplicit.TrivialInduction.dualModule _root_.OAI.ArExplicit.TrivialInduction.instAdditiveModuleCatTrivialExtensionInflate _root_.OAI.ArExplicit.TrivialInduction.instPreservesHomologyModuleCatTrivialExtensionInflate _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionCoinduced _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionMulOppositeCoinduced _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionMulOppositeQuotient _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionQuotient _root_.OAI.ArExplicit.TrivialInduction.quotientModule _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory
open scoped TensorProduct

namespace ArExplicit.CocycleData

variable {k : Type*} [Field k] (q : k)
local notation "S" => Resolution.Simple q

theorem vector_smul_simple (hq1 : 1 + q ≠ 0) (i : TIndex) (s : S) :
    T.vector q i • s = if i = (false, .f) then s else 0 := by
  apply Resolution.simpleCoordinate_injective q hq1
  rw [Resolution.t_simple_character]
  have hc : (T.vector q i).base.coeff .f = if i = (false, .f) then 1 else 0 := by
    change T.coefficient q (false, .f) (T.vector q i) = _
    simp [eq_comm]
  rw [hc]
  split_ifs <;> simp

end ArExplicit.CocycleData

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Resolutions_ResolutionProductCompatibility
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Abelian
open CochainComplex CochainComplex.HomComplex
namespace ArExplicit.ResolutionProducts
universe u v
variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory C]

variable [HasExt.{v} C]

theorem endExt_product {X : C} (P : ProjectiveResolution X) {n m : ℕ}
    (x : Cocycle P.cochainComplex P.cochainComplex (n : ℤ))
    (y : Cocycle P.cochainComplex P.cochainComplex (m : ℤ)) :
    (endExt P x).comp (endExt P y) rfl = endExt P (natCocycleProduct x y) := by
  apply Ext.homEquiv.injective
  change ((endExt P x).comp (endExt P y) rfl).hom = (endExt P (natCocycleProduct x y)).hom
  simp only [Ext.comp_hom, endExt_hom]
  rw [cocycleHom_comp (by omega) x y (natCocycleProduct x y) rfl,
    ShiftedHom.map_comp]
  exact (conjugate_comp_of_eq _ _ _ _).symm

end ArExplicit.ResolutionProducts

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Resolutions_ResolutionExtIdentity
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Abelian
open CochainComplex CochainComplex.HomComplex
namespace ArExplicit.ResolutionProducts
universe u v
variable {C : Type u} [Category.{v} C] [Abelian C]

variable [HasDerivedCategory C] [HasExt.{v} C]

theorem extMk_augmentation {X : C} (P : ProjectiveResolution X) :
    P.extMk (Y := X) (P.π.f 0) 1 rfl P.complex_d_comp_π_f_zero = Ext.mk₀ (𝟙 X) := by
  rw [← endExt_identity P, endExt_eq_augmented]
  unfold ProjectiveResolution.extMk
  apply congrArg P.extEquivCohomologyClass.symm
  apply congrArg CohomologyClass.mk
  apply Subtype.ext
  apply (Cochain.toSingleEquiv (show (0 : ℤ)+0=0 by omega)).injective
  change (Cochain.toSingleMk ((P.cochainComplexXIso 0 0 rfl).hom ≫ P.π.f 0)
      (by omega : (0 : ℤ)+0=0)).v 0 0 (by omega) ≫
        (HomologicalComplex.singleObjXSelf (.up ℤ) 0 X).hom =
    ((Cochain.ofHom (𝟙 P.cochainComplex)).comp (Cochain.ofHom P.π') (add_zero 0)).v 0 0
      (by omega) ≫ (HomologicalComplex.singleObjXSelf (.up ℤ) 0 X).hom
  rw [Cochain.id_comp, Cochain.ofHom_v, Cochain.toSingleMk_v, P.π'_f_zero]
  dsimp only [ChainComplex.single₀_obj_zero]
  exact congrArg (fun morphism =>
      morphism ≫ (HomologicalComplex.singleObjXSelf (.up ℤ) 0 X).hom)
    (Category.assoc (P.cochainComplexXIso 0 0 rfl).hom (P.π.f 0)
      (HomologicalComplex.singleObjXSelf (.up ℤ) 0 X).inv)

end ArExplicit.ResolutionProducts

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Resolutions_ResolutionExtZero
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
namespace ArExplicit.ResolutionHomology
universe u v
variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{v} C]
variable {X Y : C} (P : ProjectiveResolution X)

theorem extMk_zeroDegree_eq_zero_iff (f : P.complex.X 0 ⟶ Y)
    (hf : P.complex.d 1 0 ≫ f = 0) : P.extMk f 1 rfl hf = 0 ↔ f = 0 := by
  let := HasDerivedCategory.standard C
  obtain ⟨g,hg⟩ := CokernelCofork.IsColimit.desc' P.isColimitCokernelCofork f hf
  change X ⟶ Y at g
  change P.π.f 0 ≫ g = f at hg
  have he : P.extMk (P.π.f 0 ≫ g) 1 rfl
      (by erw [← Category.assoc, P.complex_d_comp_π_f_zero, zero_comp]) = Ext.mk₀ g := by
    erw [← P.extMk_comp_mk₀ (P.π.f 0) 1 rfl P.complex_d_comp_π_f_zero g,
      ResolutionProducts.extMk_augmentation, Ext.mk₀_id_comp]
    rfl
  have he' : P.extMk f 1 rfl hf = Ext.mk₀ g := by simpa only [hg] using he
  constructor
  · intro hz
    have hg0 : g=0 := Ext.homEquiv₀.symm.injective (by
      change Ext.mk₀ g = Ext.mk₀ (0 : X ⟶ Y)
      erw [← he', hz, Ext.mk₀_zero])
    erw [← hg, hg0, comp_zero]
  · intro hz
    cases hz
    exact P.extMk_zero 1 rfl

end ArExplicit.ResolutionHomology

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Ext_TensorExtCoefficients
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Abelian
open scoped TensorProduct ModuleCat.Algebra
namespace ArExplicit.ExternalTensor
universe u
variable (k A B : Type u) [Field k] [Ring A] [Ring B] [Algebra k A] [Algebra k B]
variable (X U : ModuleCat.{u} A) (Y V : ModuleCat.{u} B)

variable (a : Ext X X 3) (b : Ext Y Y 3)

theorem coefficientFirst_single (n : ℕ) (d : Diagonal n)
    (x : Ext X U d.val.1) (y : Ext Y V d.val.2) :
    coefficientFirst k A B X U Y V a n (Pi.single d (x ⊗ₜ[k] y)) =
      Pi.single (diagonalFirst n d) (a.comp x (by change 3+d.val.1=d.val.1+3; omega) ⊗ₜ[k] y) := by
  classical
  simp only [coefficientFirst, diagonalFirst, LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.proj_apply]
  rw [Finset.sum_eq_single d]
  · simp only [Pi.single_eq_same, TensorProduct.map_tmul, LinearMap.id_apply,
      LinearMap.single_apply]
    rfl
  · intro e he hne
    rw [Pi.single_eq_of_ne hne, map_zero, map_zero]
  · simp

theorem coefficientSecond_single (n : ℕ) (d : Diagonal n)
    (x : Ext X U d.val.1) (y : Ext Y V d.val.2) :
    coefficientSecond k A B X U Y V b n (Pi.single d (x ⊗ₜ[k] y)) =
      Pi.single (diagonalSecond n d) (x ⊗ₜ[k] b.comp y (by change 3+d.val.2=d.val.2+3; omega)) := by
  classical
  simp only [coefficientSecond, diagonalSecond, LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.proj_apply]
  rw [Finset.sum_eq_single d]
  · simp only [Pi.single_eq_same, TensorProduct.map_tmul, LinearMap.id_apply,
      LinearMap.single_apply]
    rfl
  · intro e he hne
    rw [Pi.single_eq_of_ne hne, map_zero, map_zero]
  · simp

end ArExplicit.ExternalTensor

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Homology_VectorCochainKunnethLiteral
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped TensorProduct
namespace ArExplicit.VectorCochain
universe u
variable (k : Type u) [Field k]
variable (F : ModuleCat.{u} k ⥤ ModuleCat.{u} k ⥤ ModuleCat.{u} k)
  [F.Additive] [∀ X, (F.obj X).Additive]

variable (P Q : CochainComplex (ModuleCat.{u} k) ℕ)

theorem kunneth_literal_cycles (n : ℕ)
    (z : LinearMap.ker ((mapBifunctor (gradedCycles k P) (gradedCycles k Q) F (.up ℕ)).d n (n+1)).hom)
    (w : LinearMap.ker ((mapBifunctor P Q F (.up ℕ)).d n (n+1)).hom)
    (hw : ((mapBifunctorMap (cyclesInclusion k P) (cyclesInclusion k Q) F (.up ℕ)).f n).hom z.val = w.val) :
    (kunnethIso k F P Q n).hom.hom (literalClass k (mapBifunctor P Q F (.up ℕ)) n w) =
      ((mapBifunctorMap (cyclesQuotient k P) (cyclesQuotient k Q) F (.up ℕ)).f n).hom z.val := by
  rw [← literalClass_map k _ n z w hw]
  have h := congrArg (fun f => f.hom
    (literalClass k (mapBifunctor (gradedCycles k P) (gradedCycles k Q) F (.up ℕ)) n z))
      (tensorCycles_kunneth k P F Q n)
  change _ = ((mapBifunctorMap (cyclesQuotient k P) (cyclesQuotient k Q) F (.up ℕ)).f n).hom
    ((totalZeroHomologyIso k F (fun i => P.cycles i) (fun i => Q.cycles i) n).hom.hom
      (literalClass k (mapBifunctor (gradedCycles k P) (gradedCycles k Q) F (.up ℕ)) n z)) at h
  rw [totalZero_literalClass] at h
  exact h

end ArExplicit.VectorCochain

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Tensor_BalancedTensorPi
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.EnvelopingBimodule.regular_projective _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ArExplicit.BalancedTensor

variable {k R S F M : Type*} [CommRing k] [Ring R] [Algebra k R] [Ring S]
variable [AddCommGroup F] [Module k F] [Module Rᵐᵒᵖ F]
variable [Module S F] [SMulCommClass k S F] [SMulCommClass S Rᵐᵒᵖ F]
variable [AddCommGroup M] [Module k M] [Module R M] [IsScalarTower k R M]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Algebra k R] [IsScalarTower k R M] [Fintype ι] [DecidableEq ι] in
theorem tmul_sum (f : F) (s : Finset ι) (m : ι → M) :
    tmul (k := k) (R := R) f (∑ i ∈ s, m i) = ∑ i ∈ s, tmul f (m i) := by
  exact map_sum (mk (k := k) (R := R) f) m s

omit [Fintype ι] in
theorem piRightMap_single (i j : ι) (z : BalancedTensor k R F M) :
    piRightMap (S := S) (mapRight (k := k) (S := S) (LinearMap.single R (fun _ : ι => M) j) z) i = if i = j then z else 0 := by
  induction z using induction_on with
  | zero => simp
  | tmul f m =>
    simp only [mapRight_tmul, piRightMap_tmul, LinearMap.single_apply]
    by_cases h : i = j
    · subst i; simp
    · simp [h]
  | add x y hx hy =>
    simp only [map_add, Pi.add_apply, hx, hy]
    split_ifs <;> simp

end ArExplicit.BalancedTensor

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Tensor_BalancedTensorUnit
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.EnvelopingBimodule.regular_projective _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ArExplicit.BalancedTensor

variable {k R : Type*} [CommRing k] [Ring R] [Algebra k R]

section Right

variable {F : Type*} [AddCommGroup F] [Module k F] [Module Rᵐᵒᵖ F]
variable [IsScalarTower k Rᵐᵒᵖ F]

variable {S : Type*} [Ring S] [Module S F]
variable [SMulCommClass k S F] [SMulCommClass S Rᵐᵒᵖ F]

def runitLeft : BalancedTensor k R F R ≃ₗ[S] F where
  __ := (runit (k := k) (R := R) (F := F)).toAddEquiv
  map_smul' s z := by
    change runit (s • z) = s • runit z
    induction z using induction_on with
    | zero => simp
    | tmul f r => simpa only [smul_tmul, runit_tmul] using (smul_comm s (MulOpposite.op r) f).symm
    | add x y hx hy => simp only [smul_add, map_add] at *; rw [hx, hy]

end Right

end ArExplicit.BalancedTensor

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Tensor_ExternalTensorScalarProducts
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ExternalTensor.freeFree _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Abelian
open scoped TensorProduct ModuleCat.Algebra
namespace ArExplicit.ExternalTensor
universe u
variable (k A B : Type u) [Field k] [Ring A] [Ring B] [Algebra k A] [Algebra k B]
variable (M N : Type u) [AddCommGroup M] [AddCommGroup N]
variable [Module A M] [Module B N] [mM : Module k M] [mN : Module k N]
variable [IsScalarTower k A M] [IsScalarTower k B N]

theorem selfExtScalarEquiv_comp {i j n : ℕ}
    (x : Ext (moduleObject k A B M N) (moduleObject k A B M N) i)
    (y : Ext (moduleObject k A B M N) (moduleObject k A B M N) j) (h : i+j=n) :
    selfExtScalarEquiv k A B M N n (x.comp y h) =
      (selfExtScalarEquiv k A B M N i x).comp (selfExtScalarEquiv k A B M N j y) h := by
  cases canonicalScalar_eq k A M (mM := mM)
  cases canonicalScalar_eq k B N (mM := mN)
  rfl

end ArExplicit.ExternalTensor

end

end OAI
end


