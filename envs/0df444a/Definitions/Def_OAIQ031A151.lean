-- Prove2me | Definitions.Def_OAIQ031A151
-- name    : OAIQ031A151
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T15:31:34.511263+00:00
-- url     : https://prove2.me/theorems/9717ea8d-e5a3-4ad2-81ee-6dcec8e122ae
-- title:
--   Definitions bundle OAIQ031A151 of the split of OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.ArExplicit.Statement.main`, carved from OpenAI's openai/math development (OpenAI, *An explicit counterexample to the Auslander-Reiten conjecture (result family 199)*, OpenAI Math Release, September 23, 2026, result family 199, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 9 declarations of OpenAI's Lean: 3 definitions and 6 theorems. The definitions and types are `OAI.ArExplicit.ExternalBalanced.productRegularEndpointPureProof`, `OAI.ArExplicit.ModuleBar.tensorPositiveModel`, `OAI.ArExplicit.TwoCone.bottomCokernelInclusion`.
--
--   **Sources.** They come from these modules of lean/OAI/Algebra, in whole or in part: [`AuslanderReiten_Bar_ModuleBarPositiveModel`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Bar/ModuleBarPositiveModel.lean), [`AuslanderReiten_Bar_ModuleBarTensorCentral`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Bar/ModuleBarTensorCentral.lean), [`AuslanderReiten_Bar_ModuleBarTensorCentralAction`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Bar/ModuleBarTensorCentralAction.lean), [`AuslanderReiten_Cones_TwoConeSkeleton`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Cones/TwoConeSkeleton.lean), [`AuslanderReiten_Ext_ExternalRegularEvaluation`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Ext/ExternalRegularEvaluation.lean), [`AuslanderReiten_Ext_TTensorActions`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Ext/TTensorActions.lean), [`AuslanderReiten_Ext_TTensorPolynomial`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Ext/TTensorPolynomial.lean).
--
--   **Imports.** It imports the bundles `OAIQ031A146`, `OAIQ031A147` and `OAIQ031A148` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ031A155`.
-- source:
--   OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 199; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/An-explicit-counterexample-to-the-Auslander-Reiten-conjecture-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algebra at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ031A146
import Definitions.Def_OAIQ031A147
import Definitions.Def_OAIQ031A148

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Bar_ModuleBarTensorCentral
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Abelian
open scoped TensorProduct ModuleCat.Algebra
namespace ArExplicit.ModuleBar
universe u
variable (k R S M N : Type u) [Field k] [CharP k 2]
  [Ring R] [Algebra k R] [Module.Finite k R] [Ring S] [Algebra k S] [Module.Finite k S]
  [AddCommGroup M] [Module R M] [Module k M] [IsScalarTower k R M] [Module.Finite k M]
  [AddCommGroup N] [Module S N] [Module k N] [IsScalarTower k S N] [Module.Finite k N]
variable [HasDerivedCategory (ModuleCat.{u} R)] [HasDerivedCategory (ModuleCat.{u} S)]
  [HasDerivedCategory (ModuleCat.{u} (R ⊗[k] S))]
variable (p : AbsoluteBar.Cochain3 k R) (hp : AbsoluteBar.IsCocycle3 k R p)
variable (r : AbsoluteBar.Cochain3 k S) (hr : AbsoluteBar.IsCocycle3 k S r)
variable (a : Ext (ModuleCat.of R M) (ModuleCat.of R M) 3)
  (ha : extClass3 k R M p hp = a)
  (b : Ext (ModuleCat.of S N) (ModuleCat.of S N) 3)
  (hb : extClass3 k S N r hr = b)
local notation "X" => ExternalTensor.moduleObject k R S M N
variable (hgen : ∀ n : ℕ, ∀ z : ExternalTensor.extCoefficients k R S
    (ModuleCat.of R M) (ModuleCat.of R M) (ModuleCat.of S N) (ModuleCat.of S N) (3*n+3),
  ∃ u v : ExternalTensor.extCoefficients k R S
    (ModuleCat.of R M) (ModuleCat.of R M) (ModuleCat.of S N) (ModuleCat.of S N) (3*n),
    z = ExternalTensor.coefficientFirst k R S
      (ModuleCat.of R M) (ModuleCat.of R M) (ModuleCat.of S N) (ModuleCat.of S N) a (3*n) u +
    ExternalTensor.coefficientSecond k R S
      (ModuleCat.of R M) (ModuleCat.of R M) (ModuleCat.of S N) (ModuleCat.of S N) b (3*n) v)
include ha hb hgen

theorem tensor_cubic_central
    (hhom : ∀ f : ExternalTensor.moduleObject k R S M N ⟶ ExternalTensor.moduleObject k R S M N,
      ∃ c : k, ∀ z : ExternalTensor.moduleObject k R S M N,
        f.hom z = (algebraMap k (R ⊗[k] S) c) • z)
    (n : ℕ) (x : Ext X X (3*n)) :
    (tensorFirst k R S M N p hp).comp x (by omega : 3+3*n=3*(n+1)) =
      x.comp (tensorFirst k R S M N p hp) (by omega) ∧
    (tensorSecond k R S M N r hr).comp x (by omega : 3+3*n=3*(n+1)) =
      x.comp (tensorSecond k R S M N r hr) (by omega) := by
  refine ResolutionProducts.cubicCentral_of_generation
    (tensorFirst k R S M N p hp) (tensorSecond k R S M N r hr)
    (tensorCubics_commute k R S M N p hp r hr) ?_ ?_ n x
  · intro y
    obtain ⟨c, rfl⟩ := ResolutionProducts.extZero_scalar_of_hom (k := k)
      (fun f => by
        obtain ⟨c, hc⟩ := hhom f
        exact ⟨c, ResolutionProducts.scalar_end_hom X f c hc⟩) y
    constructor <;>
      rw [Ext.comp_smul, Ext.smul_comp, Ext.comp_mk₀_id, Ext.mk₀_id_comp]
  · intro j y
    exact tensor_generation k R S M N p hp r hr a ha b hb (3*j) (hgen j) y

end ArExplicit.ModuleBar

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Bar_ModuleBarTensorCentralAction
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Abelian
open scoped TensorProduct ModuleCat.Algebra
namespace ArExplicit.ModuleBar
universe u
variable (k R S M N : Type u) [Field k] [CharP k 2]
  [Ring R] [Algebra k R] [Module.Finite k R] [Ring S] [Algebra k S] [Module.Finite k S]
  [AddCommGroup M] [Module R M] [Module k M] [IsScalarTower k R M] [Module.Finite k M]
  [AddCommGroup N] [Module S N] [Module k N] [IsScalarTower k S N] [Module.Finite k N]
variable [HasDerivedCategory (ModuleCat.{u} R)] [HasDerivedCategory (ModuleCat.{u} S)]
  [HasDerivedCategory (ModuleCat.{u} (R ⊗[k] S))]
variable (p : AbsoluteBar.Cochain3 k R) (hp : AbsoluteBar.IsCocycle3 k R p)
variable (r : AbsoluteBar.Cochain3 k S) (hr : AbsoluteBar.IsCocycle3 k S r)
variable (a : Ext (ModuleCat.of R M) (ModuleCat.of R M) 3)
  (ha : extClass3 k R M p hp = a)
  (b : Ext (ModuleCat.of S N) (ModuleCat.of S N) 3)
  (hb : extClass3 k S N r hr = b)
variable (hgen : ∀ n : ℕ, ∀ z : ExternalTensor.extCoefficients k R S
    (ModuleCat.of R M) (ModuleCat.of R M) (ModuleCat.of S N) (ModuleCat.of S N) (3*n+3),
  ∃ u v : ExternalTensor.extCoefficients k R S
    (ModuleCat.of R M) (ModuleCat.of R M) (ModuleCat.of S N) (ModuleCat.of S N) (3*n),
    z = ExternalTensor.coefficientFirst k R S
      (ModuleCat.of R M) (ModuleCat.of R M) (ModuleCat.of S N) (ModuleCat.of S N) a (3*n) u +
    ExternalTensor.coefficientSecond k R S
      (ModuleCat.of R M) (ModuleCat.of R M) (ModuleCat.of S N) (ModuleCat.of S N) b (3*n) v)
include ha hb hgen

theorem tensorFirst_action_right
    (hhom : ∀ f : ExternalTensor.moduleObject k R S M N ⟶ ExternalTensor.moduleObject k R S M N,
      ∃ c : k, ∀ z : ExternalTensor.moduleObject k R S M N,
        f.hom z = (algebraMap k (R ⊗[k] S) c) • z)
    (n : ℕ) (x : Ext (ExternalTensor.moduleObject k R S M N)
      (ExternalTensor.moduleObject k R S M N) (3*n)) :
    tensorKunneth k R S M N (3*n+3) (x.comp (tensorFirst k R S M N p hp) rfl) =
      ExternalTensor.coefficientFirst k R S (ModuleCat.of R M) (ModuleCat.of R M)
        (ModuleCat.of S N) (ModuleCat.of S N) a (3*n) (tensorKunneth k R S M N (3*n) x) := by
  rw [← (tensor_cubic_central k R S M N p hp r hr a ha b hb hgen hhom n x).1]
  exact tensorFirst_action_of_class k R S M N p hp a ha (3*n) x

theorem tensorSecond_action_right
    (hhom : ∀ f : ExternalTensor.moduleObject k R S M N ⟶ ExternalTensor.moduleObject k R S M N,
      ∃ c : k, ∀ z : ExternalTensor.moduleObject k R S M N,
        f.hom z = (algebraMap k (R ⊗[k] S) c) • z)
    (n : ℕ) (x : Ext (ExternalTensor.moduleObject k R S M N)
      (ExternalTensor.moduleObject k R S M N) (3*n)) :
    tensorKunneth k R S M N (3*n+3) (x.comp (tensorSecond k R S M N r hr) rfl) =
      ExternalTensor.coefficientSecond k R S (ModuleCat.of R M) (ModuleCat.of R M)
        (ModuleCat.of S N) (ModuleCat.of S N) b (3*n) (tensorKunneth k R S M N (3*n) x) := by
  rw [← (tensor_cubic_central k R S M N p hp r hr a ha b hb hgen hhom n x).2]
  exact tensorSecond_action_of_class k R S M N r hr b hb (3*n) x

end ArExplicit.ModuleBar

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Bar_ModuleBarPositiveModel
attribute [-instance] _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Abelian
open CochainComplex.HomComplex
open scoped TensorProduct ModuleCat.Algebra
namespace ArExplicit.ModuleBar
universe u
variable (k R S M N : Type u) [Field k] [CharP k 2]
  [Ring R] [Algebra k R] [Module.Finite k R] [Ring S] [Algebra k S] [Module.Finite k S]
  [AddCommGroup M] [Module R M] [Module k M] [IsScalarTower k R M] [Module.Finite k M]
  [AddCommGroup N] [Module S N] [Module k N] [IsScalarTower k S N] [Module.Finite k N]
variable [HasDerivedCategory (ModuleCat.{u} R)] [HasDerivedCategory (ModuleCat.{u} S)]
  [HasDerivedCategory (ModuleCat.{u} (R ⊗[k] S))]
variable (p : AbsoluteBar.Cochain3 k R) (hp : AbsoluteBar.IsCocycle3 k R p)
variable (r : AbsoluteBar.Cochain3 k S) (hr : AbsoluteBar.IsCocycle3 k S r)
variable (a : Ext (ModuleCat.of R M) (ModuleCat.of R M) 3)
  (ha : extClass3 k R M p hp = a)
  (b : Ext (ModuleCat.of S N) (ModuleCat.of S N) 3)
  (hb : extClass3 k S N r hr = b)
variable (hgen : ∀ n : ℕ, ∀ z : ExternalTensor.extCoefficients k R S
    (ModuleCat.of R M) (ModuleCat.of R M) (ModuleCat.of S N) (ModuleCat.of S N) (3*n+3),
  ∃ u v : ExternalTensor.extCoefficients k R S
    (ModuleCat.of R M) (ModuleCat.of R M) (ModuleCat.of S N) (ModuleCat.of S N) (3*n),
    z = ExternalTensor.coefficientFirst k R S
      (ModuleCat.of R M) (ModuleCat.of R M) (ModuleCat.of S N) (ModuleCat.of S N) a (3*n) u +
    ExternalTensor.coefficientSecond k R S
      (ModuleCat.of R M) (ModuleCat.of R M) (ModuleCat.of S N) (ModuleCat.of S N) b (3*n) v)
include ha hb hgen

def tensorPositiveModel
    (hhom : ∀ g : ExternalTensor.moduleObject k R S M N ⟶ ExternalTensor.moduleObject k R S M N,
      ∃ c : k, ∀ z : ExternalTensor.moduleObject k R S M N,
        g.hom z = (algebraMap k (R ⊗[k] S) c) • z)
    (K : CochainComplex (ModuleCat.{u} (R ⊗[k] S)) ℤ)
    (D : FullPositive.NonnegativeChart (k := k) K (ExternalTensor.moduleObject k R S M N))
    (f : ∀ n, ExternalTensor.extCoefficients k R S
      (ModuleCat.of R M) (ModuleCat.of R M) (ModuleCat.of S N) (ModuleCat.of S N) (3*n) ≃ₗ[k]
        BinaryKoszul.Piece k n)
    (off : ∀ n, (¬ 3 ∣ n) → ∀ x : ExternalTensor.extCoefficients k R S
      (ModuleCat.of R M) (ModuleCat.of R M) (ModuleCat.of S N) (ModuleCat.of S N) n, x = 0)
    (lx : ∀ n (x : ExternalTensor.extCoefficients k R S
      (ModuleCat.of R M) (ModuleCat.of R M) (ModuleCat.of S N) (ModuleCat.of S N) (3*n)),
      f (n+1) (ExternalTensor.coefficientFirst k R S
        (ModuleCat.of R M) (ModuleCat.of R M) (ModuleCat.of S N) (ModuleCat.of S N) a (3*n) x) =
          BinaryKoszul.mulX k n (f n x))
    (ly : ∀ n (x : ExternalTensor.extCoefficients k R S
      (ModuleCat.of R M) (ModuleCat.of R M) (ModuleCat.of S N) (ModuleCat.of S N) (3*n)),
      f (n+1) (ExternalTensor.coefficientSecond k R S
        (ModuleCat.of R M) (ModuleCat.of R M) (ModuleCat.of S N) (ModuleCat.of S N) b (3*n) x) =
          BinaryKoszul.mulY k n (f n x)) :
    FullTate.PositiveModel (k := k) K
      ((D.equiv 3).symm (tensorFirst k R S M N p hp))
      ((D.equiv 3).symm (tensorSecond k R S M N r hr)) := by
  apply FullPositive.modelOfComposite K (ExternalTensor.moduleObject k R S M N) D
    (tensorKunneth k R S M N) f (tensorFirst k R S M N p hp) (tensorSecond k R S M N r hr)
  · intro n hn x
    apply (tensorKunneth k R S M N n).injective
    rw [map_zero]
    exact off n hn _
  · intro n x
    rw [tensorFirst_action_of_class k R S M N p hp a ha (3*n) x]
    exact lx n _
  · intro n x
    rw [tensorSecond_action_of_class k R S M N r hr b hb (3*n) x]
    exact ly n _
  · intro n x
    rw [tensorFirst_action_right k R S M N p hp r hr a ha b hb hgen hhom n x]
    exact lx n _
  · intro n x
    rw [tensorSecond_action_right k R S M N p hp r hr a ha b hb hgen hhom n x]
    exact ly n _

end ArExplicit.ModuleBar

end

end OAI
end

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

def bottomCokernelInclusion (n : ℕ) : BaseCokernel D n →ₗ[R] SkeletonCokernel D n :=
  ConeCokernel.inclusion (D.d n) (middleD D n) (attachingRow D n)

end ArExplicit.TwoCone

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Ext_ExternalRegularEvaluation
attribute [-instance] _root_.OAI.ArExplicit.AbsoluteBar.twistInvPair _root_.OAI.ArExplicit.AbsoluteBar.twistInvPairSymm _root_.OAI.ArExplicit.AbsoluteBar.twistedBaseModule _root_.OAI.ArExplicit.AbsoluteBar.twistedModuleTower _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.EnvelopingBimodule.regular_projective _root_.OAI.ArExplicit.ExternalTensor.hasHomCochainTotal _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.moduleCatBaseComm _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ArExplicit.ExternalBalanced
open CategoryTheory
open scoped TensorProduct
universe u
variable (k A B : Type u) [Field k] [Ring A] [Ring B] [Algebra k A] [Algebra k B]
attribute [local instance 2000] moduleCatBaseModule moduleCatBaseTower
variable (X : ModuleCat.{u} A) (Y : ModuleCat.{u} B)
local notation "UA" => AbsoluteBar.moduleObject k A 0
local notation "UB" => AbsoluteBar.moduleObject k B 0
local notation "XY" => ExternalTensor.moduleObject k A B X Y

abbrev productRegularEndpointPureProof (a : EnvelopingBimodule k A UA)
    (b : EnvelopingBimodule k B UB) (x : X) (y : Y) :=
  BarBalanced.namedRegularMap_tmul_of_smul k (A ⊗[k] B) XY
    (ExternalTensor.envelopingObject k A B
      (ExternalTensor.moduleObject k (A ⊗[k] Aᵐᵒᵖ) (B ⊗[k] Bᵐᵒᵖ) UA UB))
    (barTensorZeroEquiv k A B).toModuleIso.hom
    (productRegularEndpoint k A B X Y) (productRegularEndpoint_eq_map k A B X Y)
    ((bimoduleCoordinates k A B UA UB).symm (a ⊗ₜ[k] b))
    ((ExternalTensor.moduleScalarCoordinates k A B X Y).symm (x ⊗ₜ[k] y))
    (((show A from a.value) • x) ⊗ₜ[k] ((show B from b.value) • y))
    (productRegularEndpoint_scalar_action k A B X Y a b x y)

end ArExplicit.ExternalBalanced

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

include hq hq1 h

theorem tTensorCoefficient_zero_of_not_dvd (n : ℕ) (hn : ¬ 3 ∣ n)
    (z : tTensorCoefficients q n) : z=0 := by
  funext p
  by_cases h₁ : 3 ∣ p.val.1
  · have h₂ : ¬ 3 ∣ p.val.2 := by
      intro h₂
      exact hn (p.property ▸ dvd_add h₁ h₂)
    exact tensor_zero_right (tSelfExt_zero_of_not_dvd q hq hq1 h p.val.2 h₂) (z p)
  · exact tensor_zero_left (tSelfExt_zero_of_not_dvd q hq hq1 h p.val.1 h₁) (z p)

end ArExplicit.Resolution

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
local notation "T" => ArExplicit.T k q
local notation "S" => ModuleCat.of T (Simple q)
variable [HasDerivedCategory (ModuleCat.{u} (ArExplicit.T k q))]
variable (hq : q ≠ 0) (hq1 : 1+q ≠ 0) (h : NoPositivePowerOne q)

theorem tTensorCoefficient_first (n : ℕ) (z : tTensorCoefficients q (3*n)) :
    tTensorCoefficientEquiv q hq hq1 h (n+1)
      (ExternalTensor.coefficientFirst k T T S S S S (tExplicitP q) (3*n) z) =
      BinaryKoszul.mulX k n (tTensorCoefficientEquiv q hq hq1 h n z) := by
  funext i
  cases i using Fin.cases with
  | zero =>
      rw [BinaryKoszul.mulX_zero, tTensorCoefficientEquiv_apply]
      rw [ExternalTensor.coefficientFirst_zero k T T S S S S (tExplicitP q) (3*n)
        (polynomialDiagonal (n+1) 0) (by simp [polynomialDiagonal]) z]
      exact map_zero _
  | succ i =>
      rw [BinaryKoszul.mulX_succ, tTensorCoefficientEquiv_apply, tTensorCoefficientEquiv_apply]
      have hc := ExternalTensor.coefficientFirst_apply k T T S S S S (tExplicitP q)
        (3*n) (polynomialDiagonal n i) z
      have hd := congrArg (tTensorScalarEquiv q hq hq1 h (i.val+1) (n-i.val)) hc
      have he := hd.trans (tTensorScalarEquiv_first q hq hq1 h i.val (n-i.val) _)
      change tTensorScalarAt q hq hq1 h (3*(n+1)) _ (i.val+1)
        ((n+1)-(i.val+1)) _ = _
      exact (tTensorScalarAt_congr q hq hq1 h (3*(n+1)) _ rfl
        (show (n+1)-(i.val+1)=n-i.val by omega) _ (by have := i.isLt; omega)).trans he

theorem tTensorCoefficient_second (n : ℕ) (z : tTensorCoefficients q (3*n)) :
    tTensorCoefficientEquiv q hq hq1 h (n+1)
      (ExternalTensor.coefficientSecond k T T S S S S (tExplicitP q) (3*n) z) =
      BinaryKoszul.mulY k n (tTensorCoefficientEquiv q hq hq1 h n z) := by
  funext i
  cases i using Fin.lastCases with
  | last =>
      rw [BinaryKoszul.mulY_last, tTensorCoefficientEquiv_apply]
      rw [ExternalTensor.coefficientSecond_zero k T T S S S S (tExplicitP q) (3*n)
        (polynomialDiagonal (n+1) (Fin.last (n+1))) (by simp [polynomialDiagonal]) z]
      exact map_zero _
  | cast i =>
      rw [BinaryKoszul.mulY_castSucc, tTensorCoefficientEquiv_apply, tTensorCoefficientEquiv_apply]
      have hc := ExternalTensor.coefficientSecond_apply k T T S S S S (tExplicitP q)
        (3*n) (polynomialDiagonal n i) z
      have hd := congrArg (tTensorScalarEquiv q hq hq1 h i.val ((n-i.val)+1)) hc
      have he := hd.trans (tTensorScalarEquiv_second q hq hq1 h i.val (n-i.val) _)
      change tTensorScalarAt q hq hq1 h (3*(n+1)) _ i.val ((n+1)-i.val) _ = _
      exact (tTensorScalarAt_congr q hq hq1 h (3*(n+1)) _ rfl
        (show (n+1)-i.val=(n-i.val)+1 by have := i.isLt; omega) _
        (by have := i.isLt; omega)).trans he

end ArExplicit.Resolution

end

end OAI
end


