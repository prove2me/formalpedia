-- Prove2me | Definitions.Def_OAIQ031A156
-- name    : OAIQ031A156
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T15:41:26.449017+00:00
-- url     : https://prove2.me/theorems/859e33ef-3738-4089-8a98-9b71b46b75d1
-- title:
--   Definitions bundle OAIQ031A156 of the split of OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.ArExplicit.Statement.main`, carved from OpenAI's openai/math development (OpenAI, *An explicit counterexample to the Auslander-Reiten conjecture (result family 199)*, OpenAI Math Release, September 23, 2026, result family 199, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 12 declarations of OpenAI's Lean: 12 theorems.
--
--   **Sources.** They come from these modules of lean/OAI/Algebra, in whole or in part: [`AuslanderReiten_Bar_ModuleBarTensorAction`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Bar/ModuleBarTensorAction.lean), [`AuslanderReiten_Coordinates_FiniteExtSourceComparison`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Coordinates/FiniteExtSourceComparison.lean), [`AuslanderReiten_Ext_ATwistExt`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Ext/ATwistExt.lean), [`AuslanderReiten_Ext_TTensorTwist`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Ext/TTensorTwist.lean), [`AuslanderReiten_Ext_TTwistExtPolynomial`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Ext/TTwistExtPolynomial.lean), [`AuslanderReiten_Homology_TTwistFactor`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Homology/TTwistFactor.lean).
--
--   **Imports.** It imports the bundles `OAIQ031A150`, `OAIQ031A152`, `OAIQ031A153` and `OAIQ031A154` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ031A158`.
-- source:
--   OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 199; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/An-explicit-counterexample-to-the-Auslander-Reiten-conjecture-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algebra at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ031A150
import Definitions.Def_OAIQ031A152
import Definitions.Def_OAIQ031A153
import Definitions.Def_OAIQ031A154

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Bar_ModuleBarTensorAction
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
variable (h : R ≃ₐ[k] R) (j : S ≃ₐ[k] S) (e : M ≃ₗ[k] M) (f : N ≃ₗ[k] N)
variable (he : ∀ a m, e (a • m) = h a • e m)
variable (hf : ∀ a n, f (a • n) = j a • f n)
variable (α : ∀ n, Ext (ModuleCat.of R M) (ModuleCat.of R M) n →ₗ[k]
  Ext (ModuleCat.of R M) (ModuleCat.of R M) n)
variable (β : ∀ n, Ext (ModuleCat.of S N) (ModuleCat.of S N) n →ₗ[k]
  Ext (ModuleCat.of S N) (ModuleCat.of S N) n)
variable (hα : ∀ n, twistExtAction k R M h e he n = α n)
variable (hβ : ∀ n, twistExtAction k S N j f hf n = β n)
variable (Φ : ∀ n, (ExternalTensor.extCoefficients k R S (ModuleCat.of R M) (ModuleCat.of R M) (ModuleCat.of S N) (ModuleCat.of S N) n) →ₗ[k] (ExternalTensor.extCoefficients k R S (ModuleCat.of R M) (ModuleCat.of R M) (ModuleCat.of S N) (ModuleCat.of S N) n))
variable (hΦ : ∀ n (x : (ExternalTensor.extCoefficients k R S (ModuleCat.of R M) (ModuleCat.of R M) (ModuleCat.of S N) (ModuleCat.of S N) n)) (p : ExternalTensor.Diagonal n), Φ n x p = TensorProduct.map (α p.val.1) (β p.val.2) (x p))
include hα hβ hΦ

theorem tensorTwist_kunneth_action (n : ℕ)
    (x : Ext (ExternalTensor.moduleObject k R S M N) (ExternalTensor.moduleObject k R S M N) n) :
    tensorKunneth k R S M N n (tensorTwist k R S M N h j e f he hf n x) =
      Φ n (tensorKunneth k R S M N n x) := by
  funext p
  rw [hΦ]
  exact tensorTwist_kunneth_of_factors k R S M N h j e f he hf α β hα hβ n x p

end ArExplicit.ModuleBar

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Coordinates_FiniteExtSourceComparison
attribute [-instance] _root_.OAI.ArExplicit.FiniteLeftModule.resolutionPairHasBiproduct _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.twistedEnvelopingFunctor_equivalence _root_.OAI.ArExplicit.twistedEnveloping_left_finite _root_.OAI.ArExplicit.twistedEnveloping_left_projective _root_.OAI.ArExplicit.twistedEnveloping_right_finite _root_.OAI.ArExplicit.twistedEnveloping_right_projective _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ArExplicit.FiniteLeftModule
open CategoryTheory CategoryTheory.Abelian
open CochainComplex CochainComplex.HomComplex CompleteComparison
open scoped ModuleCat.Algebra
universe u
variable {k R : Type u} [Field k] [Ring R] [Algebra k R] [Module.Finite k R]
variable (τ : FrobeniusTrace k R) (M : FiniteLeftModule k R)

theorem fullPositiveModuleExtEquiv_eq_precomp_extMk
    (L : ModuleCat.{u} R) (g : M.carrier ⟶ L) (P : ProjectiveResolution L)
    (φ : ProjectiveResolution.Hom
      (completeExtResolution (M.completeCochain_totallyAcyclic τ).to_chain) P
      ((M.fullCokernelEquiv τ).toModuleIso.hom ≫ g))
    (n : ℕ) (f : P.complex.X (n+1) ⟶ M.carrier)
    (hf : P.complex.d (n+2) (n+1) ≫ f = 0)
    (u : CohomologyClass (M.completeCochain τ) (M.completeCochain τ) ((n+1 : ℕ) : ℤ))
    (t : RawCokernelAt (M.completeCochain τ) ((n+1 : ℕ) : ℤ) →ₗ[R] M.carrier)
    (hu : resolutionSourceAtStableEquiv τ M M ((n+1 : ℕ) : ℤ) u = StableHom.classOf R _ _ t)
    (ht : ∀ z : (M.completeCochain τ).X (-((n+1 : ℕ) : ℤ)),
      t (Submodule.Quotient.mk z) = f.hom ((φ.hom.f (n+1)).hom
        ((tailTermIso (M.completeCochain τ) (n+1)).inv.hom z))) :
    fullPositiveModuleExtEquiv τ M n u =
      (Ext.mk₀ g).comp (P.extMk f (n+2) rfl hf) (zero_add _) := by
  apply (moduleExtSourceStableEquiv τ M M.carrier n).injective
  rw [moduleExtSourceStableEquiv_fullPositive, hu,
    moduleExtSourceStableEquiv_precomp_extMk τ M L M.carrier g P φ n f hf t ht]

end ArExplicit.FiniteLeftModule

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Ext_TTwistExtPolynomial
attribute [-instance] _root_.OAI.ArExplicit.A.instIsTwoSidedAugmentationIdeal _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.instInjectiveA _root_.OAI.ArExplicit.instInjectiveMulOppositeA _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Abelian
open scoped ModuleCat.Algebra
namespace ArExplicit.Resolution
universe u
variable {k : Type u} [Field k] [CharP k 2] (q : k) (H : kˣ)
local notation "T" => ArExplicit.T k q
variable [HasDerivedCategory (ModuleCat.{u} (ArExplicit.T k q))]

theorem tInverseTwistExt_identity :
    tInverseTwistExt q H 0 (Ext.mk₀ (𝟙 (ModuleCat.of T (Simple q)))) =
      Ext.mk₀ (𝟙 (ModuleCat.of T (Simple q))) :=
  ModuleBar.twistExtAction_identity k T (Simple q) (TrivialExtension.twist H).symm
    (LinearEquiv.refl k _) (ArExplicit.T.inverseTwist_simple_compatible q H)

theorem tInverseTwistExt_mul (n : ℕ) (x : TSelfExt q n) :
    tInverseTwistExt q H (n+3) ((tExplicitP q).comp x (by omega : 3+n=n+3)) =
      ((H⁻¹ : kˣ) : k) •
        (tExplicitP q).comp (tInverseTwistExt q H n x) (by omega : 3+n=n+3) := by
  have ht := ModuleBar.twistExtAction_cubic k T (Simple q) (TrivialExtension.twist H).symm
    (LinearEquiv.refl k _) (ArExplicit.T.inverseTwist_simple_compatible q H)
    (CocycleData.p q) (CocycleData.p_isCocycle3 q) ((H⁻¹ : kˣ) : k)
    (by
      intro a b d m
      simp only [LinearEquiv.refl_apply]
      convert ArExplicit.T.p_inverse_twist_simple q H a b d m using 1) n x
  change tInverseTwistExt q H (n+3) ((tExplicitP q).comp x (by omega : 3+n=n+3)) =
    ((H⁻¹ : kˣ) : k) • (tExplicitP q).comp (tInverseTwistExt q H n x)
      (by omega : 3+n=n+3) at ht
  exact ht

variable (hq : q ≠ 0) (hq1 : 1+q ≠ 0) (hp : NoPositivePowerOne q)

theorem tInverseTwistExt_power (n : ℕ) :
    tInverseTwistExt q H (3*n) (tExplicitPower q hq hq1 hp n) =
      (((H⁻¹ : kˣ) : k)^n) • tExplicitPower q hq hq1 hp n := by
  induction n with
  | zero =>
    simp only [tExplicitPower_zero, pow_zero, one_smul, Nat.mul_zero]
    exact tInverseTwistExt_identity q H
  | succ n ih =>
    rw [tExplicitPower_succ]
    change tInverseTwistExt q H (3*n+3)
        ((tExplicitP q).comp (tExplicitPower q hq hq1 hp n) (by omega)) = _
    rw [tInverseTwistExt_mul, ih, Ext.comp_smul, smul_smul, pow_succ]
    congr 1
    exact mul_comm _ _

include hq hq1 hp in
theorem tInverseTwistExt_all (n : ℕ) (x : TSelfExt q (3*n)) :
    tInverseTwistExt q H (3*n) x = (((H⁻¹ : kˣ) : k)^n) • x := by
  obtain ⟨a, ha, _⟩ := tExplicit_coefficient q hq hq1 hp n x
  rw [← ha, map_smul, tInverseTwistExt_power q H hq hq1 hp n]
  exact smul_comm _ _ _

end ArExplicit.Resolution

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Ext_TTensorTwist
attribute [-instance] _root_.OAI.ArExplicit.A.instIsTwoSidedAugmentationIdeal _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.instInjectiveA _root_.OAI.ArExplicit.instInjectiveMulOppositeA _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
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
variable {k : Type u} [Field k] [CharP k 2] (q : k) (H : kˣ)
variable [HasDerivedCategory (ModuleCat.{u} (ArExplicit.T k q))]

omit [HasDerivedCategory (ModuleCat.{u} (ArExplicit.T k q))] in
theorem tTensorInverseTwist_apply (n : ℕ) (x : tTensorCoefficients q n)
    (p : ExternalTensor.Diagonal n) :
    tTensorInverseTwist q H n x p = TensorProduct.map
      (tInverseTwistExt q H p.val.1) (tInverseTwistExt q H p.val.2) (x p) := rfl

variable (hq : q ≠ 0) (hq1 : 1+q ≠ 0) (hp : NoPositivePowerOne q)
include hq hq1 hp

theorem tInverseTwist_tensor_scalar (a b : ℕ)
    (x : TSelfExt q (3*a) ⊗[k] TSelfExt q (3*b)) :
    TensorProduct.map (tInverseTwistExt q H (3*a)) (tInverseTwistExt q H (3*b)) x =
      (((H⁻¹ : kˣ) : k)^(a+b)) • x := by
  induction x using OAI.tensorInductionOn with
  | add x y hx hy => simp only [map_add, smul_add, hx, hy]
  | tmul x y =>
    rw [TensorProduct.map_tmul, tInverseTwistExt_all q H hq hq1 hp,
      tInverseTwistExt_all q H hq hq1 hp, TensorProduct.smul_tmul_smul, pow_add]

theorem tTensorInverseTwist_diagonal (n : ℕ) (i : Fin (n+1))
    (x : tTensorCoefficients q (3*n)) :
    tTensorInverseTwist q H (3*n) x (polynomialDiagonal n i) =
      (((H⁻¹ : kˣ) : k)^n) • x (polynomialDiagonal n i) := by
  have h := tInverseTwist_tensor_scalar q H hq hq1 hp i.val (n-i.val)
    (x (polynomialDiagonal n i))
  have hi : i.val + (n-i.val) = n := Nat.add_sub_of_le (Nat.le_of_lt_succ i.isLt)
  rw [hi] at h
  rw [tTensorInverseTwist_apply]
  dsimp only [polynomialDiagonal]
  dsimp only [polynomialDiagonal] at h
  exact h

end ArExplicit.Resolution

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Homology_TTwistFactor
attribute [-instance] _root_.OAI.ArExplicit.A.instIsTwoSidedAugmentationIdeal _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.instInjectiveA _root_.OAI.ArExplicit.instInjectiveMulOppositeA _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ArExplicit.Resolution
universe u
variable {k : Type u} [Field k] [CharP k 2] (q : k) (H : kˣ)

theorem tInverseTwistExt_factor (n : ℕ) :
    ModuleBar.twistExtAction k (ArExplicit.T k q) (Simple q) (TrivialExtension.twist H).symm
      (LinearEquiv.refl k _) (ArExplicit.T.inverseTwist_simple_compatible q H) n =
      tInverseTwistExt q H n := rfl

end ArExplicit.Resolution

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Ext_ATwistExt
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
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
variable (h : R ≃ₐ[k] R) (j : S ≃ₐ[k] S) (e : M ≃ₗ[k] M) (f : N ≃ₗ[k] N)
variable (he : ∀ a m, e (a • m) = h a • e m)
variable (hf : ∀ a n, f (a • n) = j a • f n)
variable (α : ∀ n, Ext (ModuleCat.of R M) (ModuleCat.of R M) n →ₗ[k]
  Ext (ModuleCat.of R M) (ModuleCat.of R M) n)
variable (β : ∀ n, Ext (ModuleCat.of S N) (ModuleCat.of S N) n →ₗ[k]
  Ext (ModuleCat.of S N) (ModuleCat.of S N) n)
variable (hα : ∀ n, twistExtAction k R M h e he n = α n)
variable (hβ : ∀ n, twistExtAction k S N j f hf n = β n)
variable (Φ : ∀ n, (ExternalTensor.extCoefficients k R S (ModuleCat.of R M) (ModuleCat.of R M) (ModuleCat.of S N) (ModuleCat.of S N) n) →ₗ[k] (ExternalTensor.extCoefficients k R S (ModuleCat.of R M) (ModuleCat.of R M) (ModuleCat.of S N) (ModuleCat.of S N) n))
variable (hΦ : ∀ n (x : (ExternalTensor.extCoefficients k R S (ModuleCat.of R M) (ModuleCat.of R M) (ModuleCat.of S N) (ModuleCat.of S N) n)) (p : ExternalTensor.Diagonal n), Φ n x p = TensorProduct.map (α p.val.1) (β p.val.2) (x p))
include hα hβ hΦ

theorem tensorTwist_image_scalar (n : ℕ) (c : k)
    (hscalar : ∀ z, Φ n z = c • z)
    (x : Ext (ExternalTensor.moduleObject k R S M N) (ExternalTensor.moduleObject k R S M N) n) :
    tensorKunneth k R S M N n (tensorTwist k R S M N h j e f he hf n x) =
      c • tensorKunneth k R S M N n x :=
  (tensorTwist_kunneth_action k R S M N h j e f he hf α β hα hβ Φ hΦ n x).trans
    (hscalar _)

theorem tensorTwist_scalar (n : ℕ) (c : k)
    (hscalar : ∀ z, Φ n z = c • z)
    (x : Ext (ExternalTensor.moduleObject k R S M N) (ExternalTensor.moduleObject k R S M N) n) :
    tensorTwist k R S M N h j e f he hf n x = c • x :=
  (tensorKunneth k R S M N n).injective
    ((tensorTwist_image_scalar k R S M N h j e f he hf α β hα hβ Φ hΦ n c hscalar x).trans
      ((tensorKunneth k R S M N n).map_smul c x).symm)

end ArExplicit.ModuleBar

end

end OAI
end


