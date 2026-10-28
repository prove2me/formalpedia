-- Prove2me | Definitions.Def_OAIQ031A095
-- name    : OAIQ031A095
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T14:34:59.842129+00:00
-- url     : https://prove2.me/theorems/b549b24f-a603-4217-afba-5add137a6a0c
-- title:
--   Definitions bundle OAIQ031A095 of the split of OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.ArExplicit.Statement.main`, carved from OpenAI's openai/math development (OpenAI, *An explicit counterexample to the Auslander-Reiten conjecture (result family 199)*, OpenAI Math Release, September 23, 2026, result family 199, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 26 declarations of OpenAI's Lean: 8 definitions and 18 theorems. The definitions and types are `OAI.ArExplicit.ExternalTensor.canonicalHomCochain`, `OAI.ArExplicit.ExternalTensor.elementaryExt`, `OAI.ArExplicit.ExternalTensor.elementaryHom`, `OAI.ArExplicit.ExternalTensor.homCochainScalarEquiv`, `OAI.ArExplicit.ExternalTensor.homCochainScalarIso`, `OAI.ArExplicit.ExternalTensor.homCochainTotalIso`, `OAI.ArExplicit.ExternalTensor.secondComparison`, `OAI.ArExplicit.ExternalTensor.secondCubicExt`.
--
--   **Sources.** They come from these modules of lean/OAI/Algebra, in whole or in part: [`AuslanderReiten_Bar_ModuleBarCochain`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Bar/ModuleBarCochain.lean), [`AuslanderReiten_Bar_TwistedBar`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Bar/TwistedBar.lean), [`AuslanderReiten_Cocycles_CocycleDetector`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Cocycles/CocycleDetector.lean), [`AuslanderReiten_Ext_ExtTensorAction`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Ext/ExtTensorAction.lean), [`AuslanderReiten_HomComplex_HomCochainNativeClass`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/HomComplex/HomCochainNativeClass.lean), [`AuslanderReiten_HomComplex_HomCochainScalar`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/HomComplex/HomCochainScalar.lean), [`AuslanderReiten_HomComplex_HomKunnethClass`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/HomComplex/HomKunnethClass.lean), [`AuslanderReiten_Tensor_ExternalTensorCubicExt`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Tensor/ExternalTensorCubicExt.lean), [`AuslanderReiten_Tensor_ExternalTensorHomCubic`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Tensor/ExternalTensorHomCubic.lean), [`AuslanderReiten_Tensor_ExternalTensorHomDifferential`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Tensor/ExternalTensorHomDifferential.lean).
--
--   **Imports.** It imports the bundles `OAIQ031A078`, `OAIQ031A079`, `OAIQ031A080` and `OAIQ031A081` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ031A107`, `OAIQ031A108`, `OAIQ031A109`, `OAIQ031A111`, `OAIQ031A114`, `OAIQ031A115` and `OAIQ031A119`.
-- source:
--   OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 199; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/An-explicit-counterexample-to-the-Auslander-Reiten-conjecture-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algebra at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ031A078
import Definitions.Def_OAIQ031A079
import Definitions.Def_OAIQ031A080
import Definitions.Def_OAIQ031A081

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Bar_ModuleBarCochain
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory
open scoped TensorProduct
namespace ArExplicit.ModuleBar
universe u
variable (k R M : Type u) [Field k] [Ring R] [Algebra k R]
  [AddCommGroup M] [Module R M] [Module k M] [IsScalarTower k R M]

variable [CharP k 2]

theorem extClass3_eq_zero_iff (p : AbsoluteBar.Cochain3 k R) (hp : AbsoluteBar.IsCocycle3 k R p) :
    extClass3 k R M p hp = 0 ↔
      ∃ g : moduleObject k R M 3 →ₗ[R] moduleObject k R M 0,
        g.comp (differential k R M 3) = cochain3 k R M p := by
  trans ∃ g : (complex k R M).X 2 ⟶ moduleObject k R M 0,
      (complex k R M).d 3 2 ≫ g = ModuleCat.ofHom
        (X := moduleObject k R M 4) (Y := moduleObject k R M 0) (cochain3 k R M p)
  · exact (resolution k R M).extMk_eq_zero_iff _ 4 rfl _ 2 rfl
  constructor
  · rintro ⟨g, hg⟩
    refine ⟨g.hom, ?_⟩
    rw [complex_d k R M 2] at hg
    exact congrArg ModuleCat.Hom.hom hg
  · rintro ⟨g, hg⟩
    refine ⟨ModuleCat.ofHom (X := moduleObject k R M 3) (Y := moduleObject k R M 0) g, ?_⟩
    rw [complex_d k R M 2]
    apply ModuleCat.hom_ext
    exact hg

theorem extClass3_ne_zero_of_detector (p : AbsoluteBar.Cochain3 k R)
    (hp : AbsoluteBar.IsCocycle3 k R p) (x : moduleObject k R M 4)
    (hx : cochain3 k R M p x ≠ 0)
    (hboundary : ∀ g : moduleObject k R M 3 →ₗ[R] moduleObject k R M 0,
      g (differential k R M 3 x) = 0) : extClass3 k R M p hp ≠ 0 := by
  intro h
  obtain ⟨g, hg⟩ := (extClass3_eq_zero_iff k R M p hp).mp h
  apply hx
  rw [← hg]
  exact hboundary g

end ArExplicit.ModuleBar

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Bar_TwistedBar
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory
open scoped TensorProduct
namespace ArExplicit.AbsoluteBar
universe u
variable (k R : Type u) [Field k] [Ring R] [Algebra k R]

variable [CharP k 2]

omit [CharP k 2] in

theorem casimirInsertionMap_boundary_zero (h : R ≃ₐ[k] R) (ξ : object k R 1)
    (hξ : ∀ a : R, left k R 1 (h a) ξ = right k R 1 (MulOpposite.op a) ξ)
    (hz : boundary k R 0 ξ = 0) :
    (differential k R 1).comp (casimirInsertionMap k R h ξ hξ 1) =
      (casimirInsertionMap k R h ξ hξ 0).comp (twistedDifferential k R h 0) := by
  apply LinearMap.ext
  exact casimirInsertion_boundary_zero k R ξ hz

end ArExplicit.AbsoluteBar

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Cocycles_CocycleDetector
attribute [-instance] _root_.OAI.ArExplicit.A.instIsTwoSidedAugmentationIdeal _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.Resolution.cResolution_finite_terms _root_.OAI.ArExplicit.Resolution.complex_scalarTower _root_.OAI.ArExplicit.Resolution.instIsScalarTowerMulOppositeBaseAlgebraSimple _root_.OAI.ArExplicit.Resolution.simpleRightAction _root_.OAI.ArExplicit.Resolution.simpleRightModule _root_.OAI.ArExplicit.TrivialInduction.dualModule _root_.OAI.ArExplicit.TrivialInduction.instAdditiveModuleCatTrivialExtensionInflate _root_.OAI.ArExplicit.TrivialInduction.instPreservesHomologyModuleCatTrivialExtensionInflate _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionCoinduced _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionMulOppositeCoinduced _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionMulOppositeQuotient _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionQuotient _root_.OAI.ArExplicit.TrivialInduction.quotientModule _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.Resolution.homETower _root_.OAI.ArExplicit.Resolution.homFTower _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
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
local notation "R" => T k q
local notation "S" => Resolution.Simple q

theorem detector_evaluation_ne_zero (hq : q ≠ 0) (hq1 : 1 + q ≠ 0) :
    ModuleBar.cochain3 k R S (p q) (detector q) ≠ 0 := by
  rw [detector_evaluation q hq1]
  intro hz
  change q ^ 3 • (simpleGenerator q : S) = 0 at hz
  have hh := congrArg (Resolution.simpleCoordinate q) hz
  apply pow_ne_zero 3 hq
  simpa only [map_smul, simpleGenerator_coordinate, smul_eq_mul, mul_one, map_zero] using hh

end ArExplicit.CocycleData

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_HomComplex_HomCochainScalar
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory
namespace ArExplicit.ExternalTensor
universe u
variable (k R : Type u) [Field k] [Ring R] [Algebra k R]
attribute [local instance] moduleCatBaseModule moduleCatBaseTower
variable (P : ChainComplex (ModuleCat.{u} R) ℕ)

def canonicalHomCochain (U : ModuleCat.{u} R) : CochainComplex (ModuleCat.{u} k) ℕ :=
  letI := moduleCatBaseModule (k := k) (R := R) U
  letI := moduleCatBaseTower (k := k) (R := R) U
  homCochain k R P U

variable (U : Type u) [AddCommGroup U] [Module R U] [Module k U] [IsScalarTower k R U]

def homCochainScalarEquiv (n : ℕ) :
    (homCochain k R P U).X n ≃ₗ[k] (canonicalHomCochain k R P (ModuleCat.of R U)).X n where
  toFun f := f
  invFun f := f
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' a f := by
    change P.X n →ₗ[R] U at f
    apply LinearMap.ext
    intro x
    change a • f x = (algebraMap k R a) • f x
    exact (IsScalarTower.algebraMap_smul R a (f x)).symm

def homCochainScalarIso : homCochain k R P U ≅
    canonicalHomCochain k R P (ModuleCat.of R U) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n => (homCochainScalarEquiv k R P U n).toModuleIso)
    (fun i j hij => by
      have h : i+1=j := hij
      subst j
      dsimp only [canonicalHomCochain]
      rw [homCochain_d, homCochain_d]
      rfl)

end ArExplicit.ExternalTensor

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Tensor_ExternalTensorHomDifferential
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.VectorCochain.hasMapBifunctor _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped TensorProduct
namespace ArExplicit.ExternalTensor
universe u
variable (k A B : Type u) [Field k] [Ring A] [Ring B] [Algebra k A] [Algebra k B]
attribute [local instance] moduleCatBaseModule moduleCatBaseTower
variable (P : ChainComplex (ModuleCat.{u} A) ℕ) (Q : ChainComplex (ModuleCat.{u} B) ℕ)
variable (U : ModuleCat.{u} A) (V : ModuleCat.{u} B)

theorem homCochainInclusion_d_tmul (i j n : ℕ) (h : i+j=n)
    (f : P.X i →ₗ[A] U) (g : Q.X j →ₗ[B] V) :
    (homCochainTotal k A B P Q U V).d n (n+1)
      (homCochainInclusion k A B P Q U V i j n h (f ⊗ₜ[k] g)) =
      homCochainInclusion k A B P Q U V (i+1) j (n+1) (show i+1+j=n+1 by omega)
        ((f.comp (P.d (i+1) i).hom) ⊗ₜ[k] g) +
      (-1 : ℤˣ)^i • homCochainInclusion k A B P Q U V i (j+1) (n+1) (by omega)
        (f ⊗ₜ[k] (g.comp (Q.d (j+1) j).hom)) := by
  have hd : homCochainInclusion k A B P Q U V i j n h ≫
      (homCochainTotal k A B P Q U V).d n (n+1) =
      mapBifunctor.d₁ (homCochain k A P U) (homCochain k B Q V)
        (MonoidalCategory.curriedTensor (ModuleCat.{u} k)) (ComplexShape.up ℕ) i j (n+1) +
      mapBifunctor.d₂ (homCochain k A P U) (homCochain k B Q V)
        (MonoidalCategory.curriedTensor (ModuleCat.{u} k)) (ComplexShape.up ℕ) i j (n+1) := by
    change ιMapBifunctor (homCochain k A P U) (homCochain k B Q V)
      (MonoidalCategory.curriedTensor (ModuleCat.{u} k)) (ComplexShape.up ℕ) i j n h ≫ _ = _
    rw [mapBifunctor.d_eq, Preadditive.comp_add, mapBifunctor.ι_D₁, mapBifunctor.ι_D₂]
  rw [mapBifunctor.d₁_eq _ _ _ _ (show (ComplexShape.up ℕ).Rel i (i+1) from rfl) j (n+1) (show i+1+j=n+1 by omega),
    mapBifunctor.d₂_eq _ _ _ _ i (show (ComplexShape.up ℕ).Rel j (j+1) from rfl) (n+1) (show i+(j+1)=n+1 by omega)] at hd
  rw [show ComplexShape.ε₁ (ComplexShape.up ℕ) (ComplexShape.up ℕ) (ComplexShape.up ℕ) (i,j) = (1 : ℤˣ) from rfl,
    show ComplexShape.ε₂ (ComplexShape.up ℕ) (ComplexShape.up ℕ) (ComplexShape.up ℕ) (i,j) = (-1 : ℤˣ)^i from rfl,
    one_smul] at hd
  have hh := congrArg (fun l => l.hom (f ⊗ₜ[k] g)) hd
  simp only [homCochain_d, ModuleCat.hom_comp, LinearMap.comp_apply] at hh
  exact hh

variable [∀ n, Module.Finite A (P.X n)] [∀ n, Module.Projective A (P.X n)]
variable [∀ n, Module.Finite B (Q.X n)] [∀ n, Module.Projective B (Q.X n)]

abbrev elementaryHom (i j n : ℕ) (h : i+j=n)
    (f : P.X i →ₗ[A] U) (g : Q.X j →ₗ[B] V) :
    (complex k A B P Q).X n →ₗ[A ⊗[k] B] moduleObject k A B U V :=
  homCochainTermEquiv k A B P Q U V n
    (homCochainInclusion k A B P Q U V i j n h (f ⊗ₜ[k] g))

theorem elementary_horizontal_same (i j n : ℕ) (h : i+j=n)
    (f : P.X i →ₗ[A] U) (g : Q.X j →ₗ[B] V) :
    (elementaryHom k A B P Q U V i j n h f g).comp
      (horizontal k A B P Q (i+1) j n).hom =
      map k A B (f.comp (P.d (i+1) i).hom) g := by
  rw [horizontal_succ k A B P Q i j n h, ModuleCat.hom_comp, ← LinearMap.comp_assoc]
  rw [homCochainTermEquiv_inclusion_same, homMap_tmul]
  apply LinearMap.restrictScalars_injective k
  apply TensorProduct.ext
  apply LinearMap.ext
  intro x
  apply LinearMap.ext
  intro y
  rfl

theorem elementary_horizontal_zero (i j n : ℕ) (h : i+j=n)
    (f : P.X i →ₗ[A] U) (g : Q.X j →ₗ[B] V)
    (a b : ℕ) (hab : a+b=n+1) (hne : (a,b) ≠ (i+1,j)) :
    (elementaryHom k A B P Q U V i j n h f g).comp
      (horizontal k A B P Q a b n).hom = 0 := by
  cases a with
  | zero => rw [horizontal_zero, ModuleCat.hom_zero, LinearMap.comp_zero]
  | succ a =>
    have hh : a+b=n := by omega
    have hn : (a,b) ≠ (i,j) := by intro he; rcases Prod.mk.inj he with ⟨rfl,rfl⟩; exact hne rfl
    rw [horizontal_succ k A B P Q a b n hh, ModuleCat.hom_comp, ← LinearMap.comp_assoc,
      homCochainTermEquiv_inclusion_ne k A B P Q U V i j n h (f ⊗ₜ[k] g) a b hh hn,
      LinearMap.zero_comp]

theorem elementary_vertical_same (i j n : ℕ) (h : i+j=n)
    (f : P.X i →ₗ[A] U) (g : Q.X j →ₗ[B] V) :
    (elementaryHom k A B P Q U V i j n h f g).comp
      (vertical k A B P Q i (j+1) n).hom =
      (-1 : ℤˣ)^i • map k A B f (g.comp (Q.d (j+1) j).hom) := by
  rw [vertical_succ k A B P Q i j n h, ModuleCat.hom_smul, ModuleCat.hom_comp,
    LinearMap.comp_smul, ← LinearMap.comp_assoc, homCochainTermEquiv_inclusion_same, homMap_tmul]
  congr 1
  apply LinearMap.restrictScalars_injective k
  apply TensorProduct.ext
  apply LinearMap.ext
  intro x
  apply LinearMap.ext
  intro y
  rfl

theorem elementary_vertical_zero (i j n : ℕ) (h : i+j=n)
    (f : P.X i →ₗ[A] U) (g : Q.X j →ₗ[B] V)
    (a b : ℕ) (hab : a+b=n+1) (hne : (a,b) ≠ (i,j+1)) :
    (elementaryHom k A B P Q U V i j n h f g).comp
      (vertical k A B P Q a b n).hom = 0 := by
  cases b with
  | zero => rw [vertical_zero, ModuleCat.hom_zero, LinearMap.comp_zero]
  | succ b =>
    have hh : a+b=n := by omega
    have hn : (a,b) ≠ (i,j) := by intro he; rcases Prod.mk.inj he with ⟨rfl,rfl⟩; exact hne rfl
    rw [vertical_succ k A B P Q a b n hh, ModuleCat.hom_smul, ModuleCat.hom_comp,
      LinearMap.comp_smul, ← LinearMap.comp_assoc,
      homCochainTermEquiv_inclusion_ne k A B P Q U V i j n h (f ⊗ₜ[k] g) a b hh hn,
      LinearMap.zero_comp, smul_zero]

theorem elementary_d (i j n : ℕ) (h : i+j=n)
    (f : P.X i →ₗ[A] U) (g : Q.X j →ₗ[B] V) :
    (elementaryHom k A B P Q U V i j n h f g).comp
      ((complex k A B P Q).d (n+1) n).hom =
      elementaryHom k A B P Q U V (i+1) j (n+1) (by omega)
        (f.comp (P.d (i+1) i).hom) g +
      (-1 : ℤˣ)^i • elementaryHom k A B P Q U V i (j+1) (n+1) (by omega)
        f (g.comp (Q.d (j+1) j).hom) := by
  suffices hh : ModuleCat.ofHom (X := (complex k A B P Q).X (n+1)) (Y := moduleObject k A B U V)
      ((elementaryHom k A B P Q U V i j n h f g).comp ((complex k A B P Q).d (n+1) n).hom) =
      ModuleCat.ofHom (X := (complex k A B P Q).X (n+1)) (Y := moduleObject k A B U V)
      (elementaryHom k A B P Q U V (i+1) j (n+1) (by omega) (f.comp (P.d (i+1) i).hom) g +
        (-1 : ℤˣ)^i • elementaryHom k A B P Q U V i (j+1) (n+1) (by omega) f (g.comp (Q.d (j+1) j).hom)) by
    exact congrArg (fun z => z.hom) hh
  apply hom_ext k A B P Q
  intro a b hab
  apply ModuleCat.hom_ext
  change ((elementaryHom k A B P Q U V i j n h f g).comp
    ((complex k A B P Q).d (n+1) n).hom).comp (inclusion k A B P Q a b (n+1) hab).hom =
    (elementaryHom k A B P Q U V (i+1) j (n+1) (by omega) (f.comp (P.d (i+1) i).hom) g +
      (-1 : ℤˣ)^i • elementaryHom k A B P Q U V i (j+1) (n+1) (by omega) f (g.comp (Q.d (j+1) j).hom)).comp
        (inclusion k A B P Q a b (n+1) hab).hom
  rw [LinearMap.comp_assoc,
    show ((complex k A B P Q).d (n+1) n).hom.comp (inclusion k A B P Q a b (n+1) hab).hom =
      (horizontal k A B P Q a b n).hom + (vertical k A B P Q a b n).hom from
      congrArg (fun z => z.hom) (inclusion_d k A B P Q a b (n+1) n hab),
    LinearMap.comp_add, LinearMap.add_comp, LinearMap.smul_comp]
  by_cases ha : a=i+1
  · have hb : b=j := by omega
    subst a
    subst b
    have hn : (i+1,j) ≠ (i,j+1) := by intro hh; have := congrArg Prod.fst hh; omega
    rw [elementary_horizontal_same, elementary_vertical_zero k A B P Q U V i j n h f g _ _ hab hn,
      homCochainTermEquiv_inclusion_same, homMap_tmul,
      homCochainTermEquiv_inclusion_ne k A B P Q U V i (j+1) (n+1) (by omega)
        (f ⊗ₜ[k] (g.comp (Q.d (j+1) j).hom)) _ _ hab hn, smul_zero]
  · by_cases hb : b=j+1
    · have hai : a=i := by omega
      subst a
      subst b
      have hn : (i,j+1) ≠ (i+1,j) := by intro hh; have := congrArg Prod.fst hh; omega
      rw [elementary_horizontal_zero k A B P Q U V i j n h f g _ _ hab hn, elementary_vertical_same,
        homCochainTermEquiv_inclusion_ne k A B P Q U V (i+1) j (n+1) (by omega)
          ((f.comp (P.d (i+1) i).hom) ⊗ₜ[k] g) _ _ hab hn,
        homCochainTermEquiv_inclusion_same, homMap_tmul]
    · have hna : (a,b) ≠ (i+1,j) := by intro hh; exact ha (congrArg Prod.fst hh)
      have hnb : (a,b) ≠ (i,j+1) := by intro hh; exact hb (congrArg Prod.snd hh)
      rw [elementary_horizontal_zero k A B P Q U V i j n h f g _ _ hab hna,
        elementary_vertical_zero k A B P Q U V i j n h f g _ _ hab hnb,
        homCochainTermEquiv_inclusion_ne k A B P Q U V (i+1) j (n+1) (by omega)
          ((f.comp (P.d (i+1) i).hom) ⊗ₜ[k] g) _ _ hab hna,
        homCochainTermEquiv_inclusion_ne k A B P Q U V i (j+1) (n+1) (by omega)
          (f ⊗ₜ[k] (g.comp (Q.d (j+1) j).hom)) _ _ hab hnb, smul_zero]

def homCochainTotalIso : homCochainTotal k A B P Q U V ≅
    homCochain k (A ⊗[k] B) (complex k A B P Q) (moduleObject k A B U V) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n => (homCochainTermEquiv k A B P Q U V n).toModuleIso)
    (fun n m h => by
      have hnm : n+1=m := h
      subst m
      apply mapBifunctor.hom_ext
      intro i j hij
      apply ModuleCat.hom_ext
      apply TensorProduct.ext
      apply LinearMap.ext
      intro f
      apply LinearMap.ext
      intro g
      change (P.X i →ₗ[A] U) at f
      change (Q.X j →ₗ[B] V) at g
      change i+j=n at hij
      change (homCochain k (A ⊗[k] B) (complex k A B P Q) (moduleObject k A B U V)).d n (n+1)
        (elementaryHom k A B P Q U V i j n hij f g) =
        homCochainTermEquiv k A B P Q U V (n+1)
          ((homCochainTotal k A B P Q U V).d n (n+1)
            (homCochainInclusion k A B P Q U V i j n hij (f ⊗ₜ[k] g)))
      rw [homCochainInclusion_d_tmul, homCochain_d]
      simp only [map_add, Units.smul_def, map_zsmul]
      exact elementary_d k A B P Q U V i j n hij f g)

end ArExplicit.ExternalTensor

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_HomComplex_HomCochainNativeClass
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Abelian HomologicalComplex
open scoped ModuleCat.Algebra
namespace ArExplicit.ExternalTensor
universe u
variable (k R : Type u) [Field k] [Ring R] [Algebra k R]
attribute [local instance] moduleCatBaseModule moduleCatBaseTower
variable {X : ModuleCat.{u} R} (P : ProjectiveResolution X)
variable (Y : Type u) [AddCommGroup Y] [Module R Y] [Module k Y] [IsScalarTower k R Y]

theorem homCochain_mem_cycles (n : ℕ) (f : P.complex.X n →ₗ[R] Y)
    (hf : f.comp (P.complex.d (n+1) n).hom=0) :
    f ∈ LinearMap.ker ((homCochain k R P.complex Y).d n (n+1)).hom := by
  change ((homCochain k R P.complex Y).d n (n+1)).hom f=0
  rw [homCochain_d]
  exact hf

end ArExplicit.ExternalTensor

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_HomComplex_HomKunnethClass
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped TensorProduct
namespace ArExplicit.ExternalTensor
universe u
variable (k A B : Type u) [Field k] [Ring A] [Ring B] [Algebra k A] [Algebra k B]
attribute [local instance] moduleCatBaseModule moduleCatBaseTower
variable (P : ChainComplex (ModuleCat.{u} A) ℕ) (Q : ChainComplex (ModuleCat.{u} B) ℕ)
variable (U : ModuleCat.{u} A) (V : ModuleCat.{u} B)
variable [∀ n, Module.Finite A (P.X n)] [∀ n, Module.Projective A (P.X n)]
variable [∀ n, Module.Finite B (Q.X n)] [∀ n, Module.Projective B (Q.X n)]
variable (i j n : ℕ) (h : i+j=n)
variable (f : P.X i →ₗ[A] U) (g : Q.X j →ₗ[B] V)
variable (hf : f.comp (P.d (i+1) i).hom=0) (hg : g.comp (Q.d (j+1) j).hom=0)
include hf hg

theorem elementary_closed :
    (elementaryHom k A B P Q U V i j n h f g).comp ((complex k A B P Q).d (n+1) n).hom=0 := by
  rw [elementary_d, hf, hg]
  simp [elementaryHom]
  change (0 : (complex k A B P Q).X (n+1) →ₗ[A ⊗[k] B] moduleObject k A B U V) +
    ((-1 : ℤˣ)^i) • 0 = 0
  simp only [smul_zero, add_zero]

omit [∀ n, Module.Finite A (P.X n)] [∀ n, Module.Projective A (P.X n)]
    [∀ n, Module.Finite B (Q.X n)] [∀ n, Module.Projective B (Q.X n)] in
theorem elementary_total_closed :
    ((homCochainTotal k A B P Q U V).d n (n+1)).hom
      ((homCochainInclusion k A B P Q U V i j n h).hom (f ⊗ₜ[k] g))=0 := by
  rw [homCochainInclusion_d_tmul, hf, hg]
  simp

end ArExplicit.ExternalTensor

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Tensor_ExternalTensorHomCubic
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory
open scoped TensorProduct
namespace ArExplicit.ExternalTensor
universe u
variable (k A B : Type u) [Field k] [Ring A] [Ring B] [Algebra k A] [Algebra k B]
attribute [local instance] moduleCatBaseModule moduleCatBaseTower
variable (P : ChainComplex (ModuleCat.{u} A) ℕ) (Q : ChainComplex (ModuleCat.{u} B) ℕ)
variable (U : ModuleCat.{u} A) (V : ModuleCat.{u} B)
variable [∀ n, Module.Finite A (P.X n)] [∀ n, Module.Projective A (P.X n)]
variable [∀ n, Module.Finite B (Q.X n)] [∀ n, Module.Projective B (Q.X n)]

theorem elementary_cubicInsert_same (i j n : ℕ) (h : i+j=n)
    (f : P.X i →ₗ[A] U) (g : Q.X j →ₗ[B] V)
    (x : moduleObject k A B (P.X i) (Q.X j)) :
    elementaryHom k A B P Q U V i j n h f g
      (cubicInsert k A B P Q n ⟨(i,j),h⟩ x) = map k A B f g x := by
  have hh := homCochainTermEquiv_inclusion_same k A B P Q U V i j n h (f ⊗ₜ[k] g)
  rw [inclusion_eq_cubicInsert, homMap_tmul] at hh
  exact DFunLike.congr_fun hh x

theorem elementary_cubicInsert_ne (i j n : ℕ) (h : i+j=n)
    (f : P.X i →ₗ[A] U) (g : Q.X j →ₗ[B] V)
    (a b : ℕ) (hab : a+b=n) (hne : (a,b) ≠ (i,j))
    (x : moduleObject k A B (P.X a) (Q.X b)) :
    elementaryHom k A B P Q U V i j n h f g
      (cubicInsert k A B P Q n ⟨(a,b),hab⟩ x) = 0 := by
  have hh := homCochainTermEquiv_inclusion_ne k A B P Q U V i j n h (f ⊗ₜ[k] g) a b hab hne
  rw [inclusion_eq_cubicInsert] at hh
  exact DFunLike.congr_fun hh x

theorem map_first_comp {M M' : ModuleCat.{u} A} {N : ModuleCat.{u} B}
    (f : M →ₗ[A] U) (g : N →ₗ[B] V) (p : M' →ₗ[A] M)
    (x : moduleObject k A B M' N) :
    map k A B f g (map k A B p (LinearMap.id : N →ₗ[B] N) x) =
      map k A B (f.comp p) g x := by
  have h : (map k A B f g).comp (map k A B p (LinearMap.id : N →ₗ[B] N)) =
      map k A B (f.comp p) g := by
    apply LinearMap.restrictScalars_injective k
    apply TensorProduct.ext
    apply LinearMap.ext
    intro a
    apply LinearMap.ext
    intro b
    rfl
  exact DFunLike.congr_fun h x

theorem map_second_comp {M : ModuleCat.{u} A} {N N' : ModuleCat.{u} B}
    (f : M →ₗ[A] U) (g : N →ₗ[B] V) (r : N' →ₗ[B] N)
    (x : moduleObject k A B M N') :
    map k A B f g (map k A B (LinearMap.id : M →ₗ[A] M) r x) =
      map k A B f (g.comp r) x := by
  have h : (map k A B f g).comp (map k A B (LinearMap.id : M →ₗ[A] M) r) =
      map k A B f (g.comp r) := by
    apply LinearMap.restrictScalars_injective k
    apply TensorProduct.ext
    apply LinearMap.ext
    intro a
    apply LinearMap.ext
    intro b
    rfl
  exact DFunLike.congr_fun h x

end ArExplicit.ExternalTensor

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Tensor_ExternalTensorCubicExt
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Abelian
open scoped TensorProduct
namespace ArExplicit.ExternalTensor
universe u
variable (k A B : Type u) [Field k] [Ring A] [Ring B] [Algebra k A] [Algebra k B]
variable [CharP k 2] [Module.Finite k A] [Module.Finite k B]
variable [HasDerivedCategory (ModuleCat.{u} (A ⊗[k] B))]
attribute [local instance] moduleCatBaseModule moduleCatBaseTower
variable {X : ModuleCat.{u} A} {Y : ModuleCat.{u} B}
variable (P : ProjectiveResolution X) (Q : ProjectiveResolution Y)
variable [∀ n, Module.Finite A (P.complex.X n)] [∀ n, Module.Finite B (Q.complex.X n)]
variable (p : ∀ n, P.complex.X (n+3) ⟶ P.complex.X n)
variable (r : ∀ n, Q.complex.X (n+3) ⟶ Q.complex.X n)

def secondComparison (n : ℕ) : (projectiveResolution k A B P Q).complex.X (n+3) ⟶
    (projectiveResolution k A B P Q).complex.X n :=
  ModuleCat.ofHom (secondCubic k A B P.complex Q.complex r n)

variable (hp : ∀ n, p (n+1) ≫ P.complex.d (n+1) n = P.complex.d (n+4) (n+3) ≫ p n)
variable (hr : ∀ n, r (n+1) ≫ Q.complex.d (n+1) n = Q.complex.d (n+4) (n+3) ≫ r n)

include hr in
omit [Module.Finite k A] [Module.Finite k B]
  [HasDerivedCategory (ModuleCat.{u} (A ⊗[k] B))] in
theorem secondComparison_comm (n : ℕ) :
    secondComparison k A B P Q r (n+1) ≫ (projectiveResolution k A B P Q).complex.d (n+1) n =
      (projectiveResolution k A B P Q).complex.d (n+4) (n+3) ≫ secondComparison k A B P Q r n :=
  ModuleCat.hom_ext (secondCubic_chain k A B P.complex Q.complex r hr n)

def secondCubicExt : Ext (moduleObject k A B X Y) (moduleObject k A B X Y) 3 :=
  ResolutionProducts.endExt (projectiveResolution k A B P Q)
    (ResolutionProducts.natCubicCocycle (k := k) (projectiveResolution k A B P Q)
      (secondComparison k A B P Q r) (secondComparison_comm k A B P Q r hr))

end ArExplicit.ExternalTensor

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Ext_ExtTensorAction
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
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
variable [CharP k 2] [Module.Finite k A] [Module.Finite k B]
variable [HasDerivedCategory (ModuleCat.{u} A)] [HasDerivedCategory (ModuleCat.{u} B)]
variable [HasDerivedCategory (ModuleCat.{u} (A ⊗[k] B))]
attribute [local instance] moduleCatBaseModule moduleCatBaseTower
variable {X : ModuleCat.{u} A} {Y : ModuleCat.{u} B}
variable (P : ProjectiveResolution X) (Q : ProjectiveResolution Y)
variable [∀ n, Module.Finite A (P.complex.X n)] [∀ n, Module.Finite B (Q.complex.X n)]
variable (U : ModuleCat.{u} A) (V : ModuleCat.{u} B)

def elementaryExt (i j n : ℕ) (h : i+j=n)
    (f : P.complex.X i →ₗ[A] U) (g : Q.complex.X j →ₗ[B] V)
    (hf : f.comp (P.complex.d (i+1) i).hom=0) (hg : g.comp (Q.complex.d (j+1) j).hom=0) :
    Ext (moduleObject k A B X Y) (moduleObject k A B U V) n :=
  (projectiveResolution k A B P Q).extMk
    (ModuleCat.ofHom (X := (complex k A B P.complex Q.complex).X n)
      (Y := moduleObject k A B U V) (elementaryHom k A B P.complex Q.complex U V i j n h f g))
    (n+1) rfl (ModuleCat.hom_ext (elementary_closed k A B P.complex Q.complex U V i j n h f g hf hg))

end ArExplicit.ExternalTensor

end

end OAI
end


