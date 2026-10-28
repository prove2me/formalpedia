-- Prove2me | Definitions.Def_OAIQ031A139
-- name    : OAIQ031A139
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T15:13:15.922565+00:00
-- url     : https://prove2.me/theorems/54a4c6d9-58af-40ea-887a-e847276103c1
-- title:
--   Definitions bundle OAIQ031A139 of the split of OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.ArExplicit.Statement.main`, carved from OpenAI's openai/math development (OpenAI, *An explicit counterexample to the Auslander-Reiten conjecture (result family 199)*, OpenAI Math Release, September 23, 2026, result family 199, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 22 declarations of OpenAI's Lean: 10 definitions and 12 theorems. The definitions and types are `OAI.ArExplicit.A.firstFullClass`, `OAI.ArExplicit.A.nonnegativeExtChart`, `OAI.ArExplicit.A.secondFullClass`, `OAI.ArExplicit.Resolution.aFirst`, `OAI.ArExplicit.Resolution.aSecond`, `OAI.ArExplicit.Resolution.polynomialDiagonal`, `OAI.ArExplicit.Resolution.tExplicitCoefficientEquiv`, `OAI.ArExplicit.Resolution.tExplicitPower`, `OAI.ArExplicit.Resolution.tPMulEquiv`, `OAI.ArExplicit.Resolution.tTensorScalarEquiv`.
--
--   **Sources.** They come from these modules of lean/OAI/Algebra, in whole or in part: [`AuslanderReiten_Coordinates_ConcreteCubicClasses`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Coordinates/ConcreteCubicClasses.lean), [`AuslanderReiten_Ext_AExtActions`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Ext/AExtActions.lean), [`AuslanderReiten_Ext_TExplicitGenerator`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Ext/TExplicitGenerator.lean), [`AuslanderReiten_Ext_TExplicitPolynomial`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Ext/TExplicitPolynomial.lean), [`AuslanderReiten_Ext_TTensorActions`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Ext/TTensorActions.lean), [`AuslanderReiten_Ext_TTensorPolynomial`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Ext/TTensorPolynomial.lean), [`AuslanderReiten_HomComplex_FiniteFullHomExt`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/HomComplex/FiniteFullHomExt.lean), [`AuslanderReiten_HomComplex_TensorFullHomPositive`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/HomComplex/TensorFullHomPositive.lean).
--
--   **Imports.** It imports the bundles `OAIQ031A129` and `OAIQ031A130` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ031A146`, `OAIQ031A147` and `OAIQ031A150`.
-- source:
--   OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 199; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/An-explicit-counterexample-to-the-Auslander-Reiten-conjecture-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algebra at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ031A129
import Definitions.Def_OAIQ031A130

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Ext_TExplicitGenerator
attribute [-instance] _root_.OAI.ArExplicit.A.instIsTwoSidedAugmentationIdeal _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory
namespace ArExplicit.Resolution
universe u
variable {k : Type u} [Field k] [CharP k 2] (q : k)

variable [hD : HasDerivedCategory (ModuleCat.{u} (ArExplicit.T k q))]
include hD
variable (hq : q ≠ 0) (hq1 : 1 + q ≠ 0) (h : NoPositivePowerOne q)
include hq hq1 h

theorem tExplicitP_multiply_bijective (n : ℕ) :
    Function.Bijective (fun b : TSelfExt q n => (tExplicitP q).comp b (by omega : 3 + n = n + 3)) := by
  obtain ⟨a, ha, hp⟩ := tExplicitP_generator q hq hq1 h
  rw [hp]
  simpa only [Function.comp_def, Abelian.Ext.smul_comp, LinearEquiv.smulOfNeZero_apply] using
    ((LinearEquiv.smulOfNeZero (K := k) (M := TSelfExt q (n + 3)) a ha).bijective.comp
      (tTau_multiply_bijective q hq hq1 h n))

end ArExplicit.Resolution

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Ext_TExplicitPolynomial
attribute [-instance] _root_.OAI.ArExplicit.A.instIsTwoSidedAugmentationIdeal _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory
namespace ArExplicit.Resolution
universe u
variable {k : Type u} [Field k] [CharP k 2] (q : k)
local notation "T" => ArExplicit.T k q
local notation "S" => ModuleCat.of T (Simple q)
variable [hD : HasDerivedCategory (ModuleCat.{u} (ArExplicit.T k q))]
include hD
variable (hq : q ≠ 0) (hq1 : 1 + q ≠ 0) (h : NoPositivePowerOne q)
include hq hq1 h

def tPMulEquiv (n : ℕ) : TSelfExt q n ≃ₗ[k] TSelfExt q (n + 3) :=
  LinearEquiv.ofBijective (tPMul q n) (tExplicitP_multiply_bijective q hq hq1 h n)

def tExplicitCoefficientEquiv : (n : ℕ) → k ≃ₗ[k] TSelfExt q (3 * n)
  | 0 => tSimpleExtZeroEquiv q hq1
  | n + 1 => (tExplicitCoefficientEquiv n).trans (tPMulEquiv q hq hq1 h (3 * n))

def tExplicitPower (n : ℕ) : TSelfExt q (3 * n) := tExplicitCoefficientEquiv q hq hq1 h n 1

@[simp] theorem tExplicitPower_zero : tExplicitPower q hq hq1 h 0 = Abelian.Ext.mk₀ (𝟙 S) :=
  tSimpleExtZeroEquiv_one q hq1

@[simp] theorem tExplicitPower_succ (n : ℕ) :
    tExplicitPower q hq hq1 h (n + 1) =
      (tExplicitP q).comp (tExplicitPower q hq hq1 h n) (by omega) := rfl

end ArExplicit.Resolution

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Ext_TTensorPolynomial
attribute [-instance] _root_.OAI.ArExplicit.A.instIsTwoSidedAugmentationIdeal _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory
open scoped TensorProduct ModuleCat.Algebra
namespace ArExplicit.Resolution
universe u
variable {k : Type u} [Field k] [CharP k 2] (q : k)
variable [HasDerivedCategory (ModuleCat.{u} (ArExplicit.T k q))]
variable (hq : q ≠ 0) (hq1 : 1+q ≠ 0) (h : NoPositivePowerOne q)

def polynomialDiagonal (n : ℕ) (i : Fin (n+1)) : ExternalTensor.Diagonal (3*n) :=
  ⟨(3*i.val,3*(n-i.val)), by have := i.isLt; dsimp; omega⟩

theorem polynomialDiagonal_injective (n : ℕ) :
    Function.Injective (polynomialDiagonal n) := by
  intro i j hij
  apply Fin.ext
  have he := congrArg (fun p : ExternalTensor.Diagonal (3*n) => p.val.1) hij
  dsimp [polynomialDiagonal] at he
  omega

theorem polynomialDiagonal_hits (n : ℕ) (p : ExternalTensor.Diagonal (3*n))
    (h₁ : 3 ∣ p.val.1) (h₂ : 3 ∣ p.val.2) :
    ∃ i, polynomialDiagonal n i = p := by
  obtain ⟨a, ha⟩ := h₁
  obtain ⟨b, hb⟩ := h₂
  have hp := p.property
  let i : Fin (n+1) := ⟨a, by omega⟩
  refine ⟨i, ?_⟩
  apply Subtype.ext
  apply Prod.ext
  · exact ha.symm
  · dsimp [polynomialDiagonal, i]
    omega

omit [CharP k 2] in
theorem tensor_zero_left {U V : Type u} [AddCommGroup U] [AddCommGroup V]
    [Module k U] [Module k V] (hu : ∀ x : U, x=0) (z : U ⊗[k] V) : z=0 := by
  induction z using OAI.tensorInductionOn with
  | tmul x y => rw [hu x, TensorProduct.zero_tmul]
  | add x y hx hy => rw [hx, hy, add_zero]

omit [CharP k 2] in
theorem tensor_zero_right {U V : Type u} [AddCommGroup U] [AddCommGroup V]
    [Module k U] [Module k V] (hv : ∀ y : V, y=0) (z : U ⊗[k] V) : z=0 := by
  induction z using OAI.tensorInductionOn with
  | tmul x y => rw [hv y, TensorProduct.tmul_zero]
  | add x y hx hy => rw [hx, hy, add_zero]

end ArExplicit.Resolution

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Ext_AExtActions
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Abelian
open scoped TensorProduct ModuleCat.Algebra
namespace ArExplicit.Resolution
universe u
variable {k : Type u} [Field k] [CharP k 2] (q : k)
local notation "T" => ArExplicit.T k q
attribute [local instance] moduleCatBaseModule moduleCatBaseTower
variable [HasDerivedCategory (ModuleCat.{u} (ArExplicit.T k q))]
variable [HasDerivedCategory (ModuleCat.{u} (ArExplicit.T k q ⊗[k] ArExplicit.T k q))]

abbrev aFirst :=
  ModuleBar.tensorFirst k T T (Simple q) (Simple q)
    (CocycleData.p q) (CocycleData.p_isCocycle3 q)

abbrev aSecond :=
  ModuleBar.tensorSecond k T T (Simple q) (Simple q)
    (CocycleData.p q) (CocycleData.p_isCocycle3 q)

end ArExplicit.Resolution

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_HomComplex_FiniteFullHomExt
attribute [-instance] _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Abelian
open CochainComplex CochainComplex.HomComplex
open scoped ModuleCat.Algebra
namespace ArExplicit.FiniteLeftModule
universe u
variable {k R : Type u} [Field k] [Ring R] [Algebra k R] [Module.Finite k R] [CharP k 2]
variable [HasDerivedCategory (ModuleCat.{u} R)]
open CompleteComparison
variable (τ : FrobeniusTrace k R) (M : FiniteLeftModule k R)

theorem fullPositiveModuleExtEquiv_product (n m : ℕ)
    (x : CohomologyClass (M.completeCochain τ) (M.completeCochain τ) ((n+1:ℕ):ℤ))
    (y : CohomologyClass (M.completeCochain τ) (M.completeCochain τ) ((m+1:ℕ):ℤ)) :
    fullPositiveModuleExtEquiv τ M (n+1+m)
      (TateKoszul.degreeEquiv (k := k) (CohomologyClass (M.completeCochain τ) (M.completeCochain τ))
        (show ((n+1:ℕ):ℤ)+((m+1:ℕ):ℤ)=((n+1+m+1:ℕ):ℤ) by omega) (fullHomProduct x y)) =
      (fullPositiveModuleExtEquiv τ M n x).comp (fullPositiveModuleExtEquiv τ M m y) (by omega) := by
  obtain ⟨x,rfl⟩ := CohomologyClass.mk_surjective x
  obtain ⟨y,rfl⟩ := CohomologyClass.mk_surjective y
  rw [fullHomProduct_degree_mk _ x y (ResolutionProducts.natCocycleProduct x y) rfl]
  change selfExtIso _ _ (fullPositiveExtEquiv _ _ _ _ _ _) =
    (selfExtIso _ _ (fullPositiveExtEquiv _ _ _ _ _ _)).comp
      (selfExtIso _ _ (fullPositiveExtEquiv _ _ _ _ _ _)) _
  rw [← selfExtIso_comp, fullPositiveExtEquiv_product]

end ArExplicit.FiniteLeftModule

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_HomComplex_TensorFullHomPositive
attribute [-instance] _root_.OAI.ArExplicit.Resolution.cResolution_finite_terms _root_.OAI.ArExplicit.Resolution.complex_scalarTower _root_.OAI.ArExplicit.Resolution.instIsScalarTowerMulOppositeBaseAlgebraSimple _root_.OAI.ArExplicit.Resolution.simpleRightAction _root_.OAI.ArExplicit.Resolution.simpleRightModule _root_.OAI.ArExplicit.Resolution.tInducedCochain_kprojective _root_.OAI.ArExplicit.TrivialInduction.dualModule _root_.OAI.ArExplicit.TrivialInduction.induced_term_projective _root_.OAI.ArExplicit.TrivialInduction.instAdditiveModuleCatTrivialExtensionInflate _root_.OAI.ArExplicit.TrivialInduction.instIsScalarTowerTrivialExtensionCoinduced _root_.OAI.ArExplicit.TrivialInduction.instPreservesHomologyModuleCatTrivialExtensionInflate _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionCoinduced _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionMulOppositeCoinduced _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionMulOppositeQuotient _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionQuotient _root_.OAI.ArExplicit.TrivialInduction.quotientModule _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.Resolution.homETower _root_.OAI.ArExplicit.Resolution.homFTower _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Abelian
open CochainComplex CochainComplex.HomComplex
open scoped ModuleCat.Algebra
namespace ArExplicit.A
universe u
variable {k : Type u} [Field k] [CharP k 2] (q : k)
open CompleteComparison
variable [HasDerivedCategory (ModuleCat.{u} (A k q))]

omit [HasDerivedCategory (ModuleCat.{u} (A k q))] in
theorem fullHomZero_eq_scalar (hq1 : 1+q ≠ 0)
    (x : CohomologyClass (simpleComplete q) (simpleComplete q) 0) :
    x = fullHomZeroScalarEquiv q hq1 x • fullHomIdentity (simpleComplete q) := by
  apply (fullHomZeroScalarEquiv q hq1).injective
  rw [map_smul]
  change _ = _ • fullHomZeroScalarEquiv q hq1 (CohomologyClass.mk (Cocycle.ofHom (𝟙 _)))
  rw [fullHomZeroScalarEquiv_identity]
  exact (mul_one _).symm

theorem fullNonnegativeExtEquiv_product_of_eq (hq1 : 1+q ≠ 0) (n m r : ℕ) (hr : n+m=r)
    (x : CohomologyClass (simpleComplete q) (simpleComplete q) (n:ℤ))
    (y : CohomologyClass (simpleComplete q) (simpleComplete q) (m:ℤ)) :
    fullNonnegativeExtEquiv q hq1 r
      (TateKoszul.degreeEquiv (k := k) (CohomologyClass (simpleComplete q) (simpleComplete q))
        (show (n:ℤ)+(m:ℤ)=(r:ℤ) by omega) (fullHomProduct x y)) =
      (fullNonnegativeExtEquiv q hq1 n x).comp (fullNonnegativeExtEquiv q hq1 m y) hr := by
  cases n with
  | zero =>
      obtain rfl : r=m := by omega
      rw [fullHomZero_eq_scalar q hq1 x]
      simp only [fullHomProduct_smul_left, map_smul,
        fullNonnegativeExtEquiv_identity, Ext.smul_comp, Ext.mk₀_id_comp]
      erw [fullHomProduct_identity_left]
  | succ n =>
      cases m with
      | zero =>
          obtain rfl : r=n+1 := by omega
          rw [fullHomZero_eq_scalar q hq1 y]
          simp only [fullHomProduct_smul_right, map_smul,
            fullNonnegativeExtEquiv_identity, Ext.comp_smul, Ext.comp_mk₀_id]
          erw [fullHomProduct_identity_right]
      | succ m =>
          obtain rfl : r=n+1+m+1 := by omega
          exact FiniteLeftModule.fullPositiveModuleExtEquiv_product (AFrobeniusTrace k q)
            (simpleFiniteModule q) n m x y

theorem fullNonnegativeExtEquiv_product (hq1 : 1+q ≠ 0) (n m : ℕ)
    (x : CohomologyClass (simpleComplete q) (simpleComplete q) (n:ℤ))
    (y : CohomologyClass (simpleComplete q) (simpleComplete q) (m:ℤ)) :
    fullNonnegativeExtEquiv q hq1 (n+m)
      (TateKoszul.degreeEquiv (k := k) (CohomologyClass (simpleComplete q) (simpleComplete q))
        (show (n:ℤ)+(m:ℤ)=((n+m:ℕ):ℤ) by omega) (fullHomProduct x y)) =
      (fullNonnegativeExtEquiv q hq1 n x).comp (fullNonnegativeExtEquiv q hq1 m y) rfl :=
  fullNonnegativeExtEquiv_product_of_eq q hq1 n m (n+m) rfl x y

end ArExplicit.A

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Coordinates_ConcreteCubicClasses
attribute [-instance] _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory
open CochainComplex CochainComplex.HomComplex
open scoped ModuleCat.Algebra
namespace ArExplicit.A
universe u
variable {k : Type u} [Field k] [CharP k 2] (q : k)
variable [HasDerivedCategory (ModuleCat.{u} (ArExplicit.T k q))]
variable [HasDerivedCategory (ModuleCat.{u} (ArExplicit.A k q))]
open CompleteComparison

def firstFullClass (hq1 : 1+q ≠ 0) : CohomologyClass (simpleComplete q) (simpleComplete q) 3 :=
  (fullNonnegativeExtEquiv q hq1 3).symm (Resolution.aFirst q)

def secondFullClass (hq1 : 1+q ≠ 0) : CohomologyClass (simpleComplete q) (simpleComplete q) 3 :=
  (fullNonnegativeExtEquiv q hq1 3).symm (Resolution.aSecond q)

def nonnegativeExtChart (hq1 : 1+q ≠ 0) : FullPositive.NonnegativeChart (k := k) (simpleComplete q) (Simple q) where
  equiv := fullNonnegativeExtEquiv q hq1
  product := fullNonnegativeExtEquiv_product q hq1

end ArExplicit.A

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Ext_TTensorActions
attribute [-instance] _root_.OAI.ArExplicit.A.instIsTwoSidedAugmentationIdeal _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Abelian
open scoped TensorProduct ModuleCat.Algebra

namespace ArExplicit.Resolution
universe u
variable {k : Type u} [Field k] [CharP k 2] (q : k)
variable [HasDerivedCategory (ModuleCat.{u} (ArExplicit.T k q))]
variable (hq : q ≠ 0) (hq1 : 1+q ≠ 0) (h : NoPositivePowerOne q)

def tTensorScalarEquiv (a b : ℕ) :
    TSelfExt q (3*a) ⊗[k] TSelfExt q (3*b) ≃ₗ[k] k :=
  (TensorProduct.congr (tExplicitCoefficientEquiv q hq hq1 h a).symm
    (tExplicitCoefficientEquiv q hq hq1 h b).symm).trans (TensorProduct.lid k k)

@[simp]
theorem tTensorScalarEquiv_tmul (a b : ℕ) (x : TSelfExt q (3*a)) (y : TSelfExt q (3*b)) :
    tTensorScalarEquiv q hq hq1 h a b (x ⊗ₜ[k] y) =
      (tExplicitCoefficientEquiv q hq hq1 h a).symm x *
        (tExplicitCoefficientEquiv q hq hq1 h b).symm y := rfl

end ArExplicit.Resolution

end

end OAI
end


