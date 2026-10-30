-- Prove2me | Definitions.Def_OAIQ116Ta007
-- name    : OAIQ116Ta007
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-30T01:43:58.223725+00:00
-- url     : https://prove2.me/theorems/2a9b38d9-4786-4be7-991a-487fdd92570a
-- title:
--   Definitions bundle OAIQ116Ta007 of the split of OpenAI, A counterexample to Tachikawa's second conjecture
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Tachikawa.main_theorem`, carved from OpenAI's openai/math development (OpenAI, *A counterexample to Tachikawa's second conjecture*, OpenAI Math Release, September 23, 2026, result family 199, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 171 declarations of OpenAI's Lean: 81 definitions, 40 instances and 50 theorems. The definitions and types are `OAI.Tachikawa.C.leftDualResObj`, `OAI.Tachikawa.C.nuTopCycle`, `OAI.Tachikawa.C.nuTwoAug`, `OAI.Tachikawa.C.nuTwoCycle`, `OAI.Tachikawa.C.rightDualResObj`, `OAI.Tachikawa.CompleteStableExt.Q`, `OAI.Tachikawa.Construction.TLeftObj`, `OAI.Tachikawa.Construction.TRightObj`, `OAI.Tachikawa.Construction.U`, `OAI.Tachikawa.Construction.Y`, `OAI.Tachikawa.Construction.eLeftTensorEquiv`, `OAI.Tachikawa.Construction.formE`, `OAI.Tachikawa.Construction.inclusionB`, `OAI.Tachikawa.Construction.inclusionC`, `OAI.Tachikawa.Construction.tLeftUnderlying`, `OAI.Tachikawa.Enveloping.RightIndType`, `OAI.Tachikawa.Enveloping.RightObj`, `OAI.Tachikawa.Enveloping.envelopingForm`, `OAI.Tachikawa.Enveloping.envelopingMap`, `OAI.Tachikawa.Enveloping.inducedCokerFive`, `OAI.Tachikawa.Enveloping.inducedFactorIso`, `OAI.Tachikawa.Enveloping.inducedRegularComplex`, `OAI.Tachikawa.Enveloping.inducedY`, `OAI.Tachikawa.Enveloping.leftCokerEquiv`, `OAI.Tachikawa.Enveloping.leftComplex`, `OAI.Tachikawa.Enveloping.leftIndComparison`, `OAI.Tachikawa.Enveloping.leftIndComparisonHom`, `OAI.Tachikawa.Enveloping.leftIndComparisonInv`, `OAI.Tachikawa.Enveloping.leftIndComparisonIso`, `OAI.Tachikawa.Enveloping.leftIndFunctor`, `OAI.Tachikawa.Enveloping.leftIndMap`, `OAI.Tachikawa.Enveloping.leftIndUnderlyingComparison`, `OAI.Tachikawa.Enveloping.leftIndUnderlyingIso`, `OAI.Tachikawa.Enveloping.leftResolutionOf`, `OAI.Tachikawa.Enveloping.leftRestrictedRegular`, `OAI.Tachikawa.Enveloping.leftRestrictedRegularIso`, `OAI.Tachikawa.Enveloping.regularFinite`, `OAI.Tachikawa.Enveloping.regularResolution`, `OAI.Tachikawa.Enveloping.regularRightEquiv`, `OAI.Tachikawa.Enveloping.regularRightUnitTarget` and 41 more.
--
--   **Sources.** They come from these modules of lean/OAI/RingTheory, in whole or in part: `Tachikawa_Bimodule`, `Tachikawa_Coinduction`, `Tachikawa_CompleteResolution`, `Tachikawa_CompleteTensor`, `Tachikawa_Corner`, `Tachikawa_DerivedInduction`, `Tachikawa_HomProfile`, `Tachikawa_Induction`, `Tachikawa_Nakayama`, `Tachikawa_OuterTensor`, `Tachikawa_Period`, `Tachikawa_ReverseResolution`, `Tachikawa_RightInduction`, `Tachikawa_Socle`, `Tachikawa_StableLift`, `Tachikawa_Symmetry`, `Tachikawa_Tensor`, `Tachikawa_Twisting`.
--
--   **Imports.** It imports the published bundle `Def_Tachikawa`; the bundles `OAIQ116Ta003` and `OAIQ116Ta004` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ116Ta010`, `OAIQ116Ta011`, `OAIQ116Ta012` and `OAIQ116Ta013`.
-- source:
--   OpenAI, A counterexample to Tachikawa's second conjecture, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 199; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-counterexample-to-Tachikawas-second-conjecture-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/RingTheory at commit adc7f12

import Mathlib
import Definitions.Def_Tachikawa
import Definitions.Def_OAIQ116Ta003
import Definitions.Def_OAIQ116Ta004

section
-- module Solutions.OAIQ116_Tach.Tachikawa_Symmetry
attribute [-instance] _root_.OAI.Tachikawa.Construction.instModuleEX _root_.OAI.Tachikawa.LeftCoinduced.coextend_additive _root_.OAI.Tachikawa.LeftCoinduced.coextend_preservesInjective _root_.OAI.Tachikawa.OuterTensor.restrictionPreservesHomology _root_.OAI.Tachikawa.TotalDualPairing.instTensorSignsNatUp_solutions _root_.OAI.Tachikawa.TotalMap.sourceHasCoproduct _root_.OAI.Tachikawa.TrivialInduction.instModuleTrivialExtensionObj _root_.OAI.Tachikawa.TrivialInflation.instModuleTrivialExtension _root_.OAI.Tachikawa.downIntTensorSigns
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



noncomputable section



namespace Tachikawa



variable {k R : Type*} [Field k] [Ring R] [Algebra k R]

namespace TrivialExtension

def symmetrizingForm : SymmetrizingForm (k := k) (R := TrivialExtension k R) where
  linear := trace
  comm := trace_comm
  nondegenerate := trace_nondegenerate

end TrivialExtension
end Tachikawa



end

end OAI
end

section
-- module Solutions.OAIQ116_Tach.Tachikawa_CompleteResolution
attribute [-instance] _root_.OAI.Tachikawa.FiniteModule.instAddCommGroupCarrierObj _root_.OAI.Tachikawa.LeftCoinduced.coextend_additive _root_.OAI.Tachikawa.LeftCoinduced.coextend_preservesInjective _root_.OAI.Tachikawa.OuterTensor.restrictionPreservesHomology _root_.OAI.Tachikawa.TotalDualPairing.instTensorSignsNatUp_solutions _root_.OAI.Tachikawa.TotalMap.sourceHasCoproduct _root_.OAI.Tachikawa.downIntTensorSigns
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section



namespace Tachikawa
open CategoryTheory
open scoped ModuleCat.Algebra
variable {k R : Type} [Field k] [Ring R] [Algebra k R]
variable (P : ChainComplex (ModuleCat R) ℤ)

def completeResolutionTail (hex : ComplexExact P)
    (proj : ∀ j, Module.Projective R (P.X j)) :
    ProjectiveResolution (ModuleCat.of R (CokerAt P 0)) := by
  let X (n : ℕ) : ModuleCat R := P.X (n : ℤ)
  let d (n : ℕ) : X (n+1) ⟶ X n := P.d ((n+1 : ℕ) : ℤ) (n : ℤ)
  let ε : X 0 ⟶ ModuleCat.of R (CokerAt P 0) := ModuleCat.ofHom (CokerAt.π P 0)
  apply resolutionOfExact _ X d ε
  · intro n
    exact hex.adjacent P _ _ _ (by omega) (by omega)
  · intro x
    change CokerAt.π P 0 x = 0 ↔ ∃ y, P.d 1 0 y = x
    exact Submodule.Quotient.mk_eq_zero _
  · exact CokerAt.π_surjective P 0
  · intro n
    let := proj (n : ℤ)
    infer_instance

lemma completeResolutionTail_d (hex : ComplexExact P)
    (proj : ∀ j, Module.Projective R (P.X j)) (n : ℕ) :
    (completeResolutionTail P hex proj).complex.d (n+1) n =
      P.d ((n+1 : ℕ) : ℤ) (n : ℤ) := by
  dsimp only [completeResolutionTail, resolutionOfExact]
  exact ChainComplex.of_d _ _ n

end Tachikawa



end

end OAI
end

section
-- module Solutions.OAIQ116_Tach.Tachikawa_Tensor
attribute [-instance] _root_.OAI.Tachikawa.LeftCoinduced.coextend_additive _root_.OAI.Tachikawa.LeftCoinduced.coextend_preservesInjective _root_.OAI.Tachikawa.OuterTensor.restrictionPreservesHomology _root_.OAI.Tachikawa.TotalDualPairing.instTensorSignsNatUp_solutions _root_.OAI.Tachikawa.TotalMap.sourceHasCoproduct _root_.OAI.Tachikawa.downIntTensorSigns
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section



namespace Tachikawa.Enveloping
open CategoryTheory
open scoped TensorProduct ModuleCat.Algebra
variable {k R S : Type} [Field k] [Ring R] [Ring S] [Algebra k R] [Algebra k S]

instance instAdditiveModuleCatAlgMulOppositeRightFunctor : (rightFunctor (k := k) (R := R) (S := S)).Additive where
  map_add := rfl

end Tachikawa.Enveloping

end

end OAI
end

section
-- module Solutions.OAIQ116_Tach.Tachikawa_CompleteTensor
attribute [-instance] _root_.OAI.Tachikawa.LeftCoinduced.coextend_additive _root_.OAI.Tachikawa.LeftCoinduced.coextend_preservesInjective _root_.OAI.Tachikawa.OuterTensor.restrictionPreservesHomology _root_.OAI.Tachikawa.TotalDualPairing.instTensorSignsNatUp_solutions _root_.OAI.Tachikawa.TotalMap.sourceHasCoproduct _root_.OAI.Tachikawa.downIntTensorSigns
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section



namespace Tachikawa.Enveloping
open CategoryTheory
open scoped ModuleCat.Algebra
variable {k R S : Type} [Field k] [Ring R] [Ring S] [Algebra k R] [Algebra k S]
  (X : ModuleCat R)

instance instAdditiveModuleCatAlgEvaluation : (evaluation (S := S) (k := k) X).Additive where
  map_add {M N f g} := by
    apply ModuleCat.hom_ext
    apply BalancedTensor.hom_ext
    intro m x
    change BalancedTensor.mk (k := k) (R := R) (S := S) (N := X) (leftMap (f+g) m) x =
      BalancedTensor.mk (k := k) (R := R) (S := S) (N := X) (leftMap f m) x + BalancedTensor.mk (k := k) (R := R) (S := S) (N := X) (leftMap g m) x
    exact congrArg (fun h : X →ₗ[k] evalType X N => h x)
      ((BalancedTensor.mk (k := k) (R := R) (S := S) (M := Obj N) (N := X)).map_add
        (leftMap f m) (leftMap g m))

end Tachikawa.Enveloping



end

end OAI
end

section
-- module Solutions.OAIQ116_Tach.Tachikawa_Twisting
attribute [-instance] _root_.OAI.Tachikawa.AlgebraInduction.resFinite _root_.OAI.Tachikawa.LeftCoinduced.C_finite _root_.OAI.Tachikawa.LeftCoinduced.J_finite _root_.OAI.Tachikawa.LeftCoinduced.coextend_additive _root_.OAI.Tachikawa.LeftCoinduced.coextend_preservesInjective _root_.OAI.Tachikawa.LeftCoinduced.iterate_finite _root_.OAI.Tachikawa.OuterTensor.restrictionPreservesHomology _root_.OAI.Tachikawa.TotalDualPairing.instTensorSignsNatUp_solutions _root_.OAI.Tachikawa.TotalMap.sourceHasCoproduct _root_.OAI.Tachikawa.downIntTensorSigns
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section



namespace Tachikawa.Enveloping
open CategoryTheory
open scoped TensorProduct ModuleCat.Algebra
variable {k R : Type} [Field k] [Ring R] [Algebra k R]

def regularUnderlyingEquiv : regular (k := k) (R := R) ≃ₗ[k] R where
  toFun := id
  invFun := id
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' c x := by
    change (action (k := k) (R := R) (S := R) R (algebraMap k (Alg k R R) c)) (show R from x) = c • (show R from x)
    rw [AlgHom.commutes]
    rfl

def regularRightEquiv : Obj (regular (k := k) (R := R)) ≃ₗ[Rᵐᵒᵖ] R where
  toFun := id
  invFun := id
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' r x := by
    change 1 * ((show R from x) * r.unop) = (show R from x) * r.unop
    rw [one_mul]

instance instFiniteDimensionalCarrierAlgRegular [FiniteDimensional k R] : FiniteDimensional k (regular (k := k) (R := R)) :=
  Module.Finite.equiv regularUnderlyingEquiv.symm

variable [FiniteDimensional k R]

def regularFinite : FiniteModule k (Alg k R R) :=
  ⟨regular, Module.Finite.of_restrictScalars_finite k (Alg k R R) _⟩

def regularResolution : ProjectiveResolution (regular (k := k) (R := R)) :=
  (regularFinite (k := k) (R := R)).projectiveResolution

instance instFiniteAlgCarrierXNatModuleCatComplexRegularResolution (n : ℕ) : Module.Finite (Alg k R R)
    ((regularResolution (k := k) (R := R)).complex.X n) := by
  change Module.Finite (Alg k R R) ((regularFinite (k := k) (R := R)).posTerm n)
  infer_instance

end Tachikawa.Enveloping



namespace Tachikawa.Enveloping
open CategoryTheory
open scoped TensorProduct ModuleCat.Algebra
variable {k R : Type} [Field k] [Ring R] [Algebra k R] (σ : R ≃ₐ[k] R)

def twistedRegular : ModuleCat (Alg k R R) :=
  ofBimodule (k := k) (R := R) (S := R) (AlgebraInduction.Bimod σ.toAlgHom)

def twistedUnderlying : twistedRegular σ ≃ₗ[k] R where
  toFun := id
  invFun := id
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' c x := by
    change action (k := k) (R := R) (S := R)
      (AlgebraInduction.Bimod σ.toAlgHom) (algebraMap k (Alg k R R) c) x = c • (show R from x)
    rw [AlgHom.commutes]
    rfl

def twistedLeftEquiv : Obj (twistedRegular σ) ≃ₗ[R] R where
  toFun := id
  invFun := id
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' r x := by
    change r * ((show R from x) * σ 1) = r * (show R from x)
    rw [map_one,mul_one]

instance instFiniteDimensionalCarrierAlgTwistedRegular [FiniteDimensional k R] : FiniteDimensional k (twistedRegular σ) :=
  Module.Finite.equiv (twistedUnderlying σ).symm

end Tachikawa.Enveloping



namespace Tachikawa.Enveloping
open CategoryTheory
open scoped ModuleCat.Algebra
variable {k R : Type} [Field k] [Ring R] [Algebra k R]
  (σ : R ≃ₐ[k] R) (X : ModuleCat R)

def twistedEvalBilinear : Obj (twistedRegular σ) →ₗ[R] X →ₗ[k] X where
  toFun m :=
    { toFun := fun x => (twistedLeftEquiv σ m) • x
      map_add' := fun x y => smul_add _ x y
      map_smul' := fun c x => smul_comm _ c x }
  map_add' m n := by ext x; exact add_smul _ _ x
  map_smul' r m := by
    ext x
    change (twistedLeftEquiv σ (r • m)) • x = r • ((twistedLeftEquiv σ m) • x)
    rw [map_smul,smul_eq_mul,mul_smul]

variable (hσ : ∀ r : R, ∀ x : X, σ r • x = r • x)
include hσ

def twistedEval : evalObj X (twistedRegular σ) ⟶ X :=
  ModuleCat.ofHom (BalancedTensor.lift (twistedEvalBilinear σ X) (by
    intro r m x
    change (twistedLeftEquiv σ (MulOpposite.op r • m)) • x =
      twistedLeftEquiv σ m • (r • x)
    change (1 * ((show R from m) * σ r)) • x = (show R from m) • (r • x)
    rw [one_mul,mul_smul,hσ]))

lemma twistedTensor_move (r : R) (x : X) :
    BalancedTensor.mk (k := k) (R := R) (S := R)
      (M := Obj (twistedRegular σ)) (N := X) (show Obj (twistedRegular σ) from r) x =
    BalancedTensor.mk (show Obj (twistedRegular σ) from (1:R)) (r • x) := by
  have hb := BalancedTensor.balance (k := k) (S := R)
    (M := Obj (twistedRegular σ)) (N := X) (σ.symm r)
    (show Obj (twistedRegular σ) from (1:R)) x
  have hm : MulOpposite.op (σ.symm r) • (show Obj (twistedRegular σ) from (1:R)) =
      (show Obj (twistedRegular σ) from r) := by
    change 1 * (1 * σ (σ.symm r)) = r
    rw [σ.apply_symm_apply,one_mul,one_mul]
  rw [hm] at hb
  have hh : σ.symm r • x = r • x := by
    have := hσ (σ.symm r) x
    rw [σ.apply_symm_apply] at this
    exact this.symm
  rw [hh] at hb
  exact hb

def twistedEvalInv : X ⟶ evalObj X (twistedRegular σ) :=
  ModuleCat.ofHom
    { toFun := fun x => BalancedTensor.mk (show Obj (twistedRegular σ) from (1:R)) x
      map_add' := fun x y => map_add _ x y
      map_smul' := fun r x => by
        change BalancedTensor.mk (show Obj (twistedRegular σ) from (1:R)) (r • x) =
          r • BalancedTensor.mk (show Obj (twistedRegular σ) from (1:R)) x
        rw [← twistedTensor_move σ X hσ r x]
        have hm : r • (show Obj (twistedRegular σ) from (1:R)) =
            (show Obj (twistedRegular σ) from r) := by
          change r * (1 * σ 1) = r
          rw [map_one,mul_one,mul_one]
        conv_lhs => rw [← hm]
        rw [LinearMap.map_smul]
        rfl }

def twistedEvalIso : evalObj X (twistedRegular σ) ≅ X where
  hom := twistedEval σ X hσ
  inv := twistedEvalInv σ X hσ
  hom_inv_id := by
    apply ModuleCat.hom_ext
    apply BalancedTensor.hom_ext
    intro m x
    change BalancedTensor.mk (show Obj (twistedRegular σ) from (1:R))
      ((show R from m) • x) = BalancedTensor.mk m x
    exact (twistedTensor_move σ X hσ (show R from m) x).symm
  inv_hom_id := by
    apply ModuleCat.hom_ext
    ext x
    change (1:R) • x = x
    exact one_smul R x

end Tachikawa.Enveloping



end

end OAI
end

section
-- module Solutions.OAIQ116_Tach.Tachikawa_OuterTensor
attribute [-instance] _root_.OAI.Tachikawa.LeftCoinduced.coextend_additive _root_.OAI.Tachikawa.LeftCoinduced.coextend_preservesInjective _root_.OAI.Tachikawa.OuterTensor.objFinite _root_.OAI.Tachikawa.OuterTensor.restrictionPreservesHomology _root_.OAI.Tachikawa.TotalDualPairing.instTensorSignsNatUp_solutions _root_.OAI.Tachikawa.downIntTensorSigns
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
set_option backward.isDefEq.respectTransparency false


noncomputable section
set_option backward.isDefEq.respectTransparency true



namespace Tachikawa.OuterTensor
open CategoryTheory
open scoped TensorProduct ModuleCat.Algebra
variable (k A B : Type) [Field k] [Ring A] [Ring B] [Algebra k A] [Algebra k B]

lemma projective (M : ModuleCat A) (N : ModuleCat B)
    [Module.Finite A M] [Module.Finite B N] [Module.Projective A M] [Module.Projective B N] :
    Module.Projective (A ⊗[k] B) (Obj k A B M N) := by
  let c := finiteFreeCover (R := A) (M := M)
  let d := finiteFreeCover (R := B) (M := N)
  obtain ⟨i,hi⟩ := Module.projective_lifting_property c.map LinearMap.id c.surjective
  obtain ⟨j,hj⟩ := Module.projective_lifting_property d.map LinearMap.id d.surjective
  have : Module.Projective (A ⊗[k] B)
      (Obj k A B (ModuleCat.of A (Fin c.rank → A))
        (ModuleCat.of B (Fin d.rank → B))) := freeProjective k A B c.rank d.rank
  apply Module.Projective.of_split
    (map (k := k) (ModuleCat.ofHom i) (ModuleCat.ofHom j))
    (map (k := k) (ModuleCat.ofHom c.map) (ModuleCat.ofHom d.map))
  rw [map_comp]
  have hi' : ModuleCat.ofHom i ≫ ModuleCat.ofHom c.map = 𝟙 M := ModuleCat.hom_ext hi
  have hj' : ModuleCat.ofHom j ≫ ModuleCat.ofHom d.map = 𝟙 N := ModuleCat.hom_ext hj
  rw [hi',hj',map_id]

end Tachikawa.OuterTensor



end

end OAI
end

section
-- module Solutions.OAIQ116_Tach.Tachikawa_Nakayama
attribute [-instance] _root_.OAI.Tachikawa.Construction.instModuleEX _root_.OAI.Tachikawa.LeftCoinduced.coextend_additive _root_.OAI.Tachikawa.LeftCoinduced.coextend_preservesInjective _root_.OAI.Tachikawa.downIntTensorSigns
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section



namespace Tachikawa
variable {k R : Type} [Field k] [Ring R] [Algebra k R]
variable {M N : Type} [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N]

namespace Nakayama

variable [Module k M] [IsScalarTower k R M]

variable [Module k N] [IsScalarTower k R N]

variable [FiniteDimensional k R]
local notation "V" => BalancedTensor.T (k := k) (R := R) (S := R) (M := DualBimodule k R) (N := M)

def transpose (l : Module.Dual k V) : M →ₗ[R] R where
  toFun := transposeFun l
  map_add' x y := by
    apply (Module.evalEquiv k R).injective
    ext φ
    change φ (transposeFun l (x+y)) = φ (transposeFun l x + transposeFun l y)
    rw [map_add]
    exact (transposeFun_eval l (x+y) φ).trans (by
      rw [map_add, map_add]
      exact congrArg₂ (· + ·) (transposeFun_eval l x φ).symm (transposeFun_eval l y φ).symm)
  map_smul' r m := by
    apply (Module.evalEquiv k R).injective
    ext φ
    change φ (transposeFun l (r • m)) = φ (r * transposeFun l m)
    let φ' : DualBimodule k R := φ
    change φ' (transposeFun l (r • m)) = (MulOpposite.op r • φ') (transposeFun l m)
    rw [transposeFun_eval, transposeFun_eval, BalancedTensor.balance]

lemma transpose_evaluation (l : Module.Dual k V) (z : V) :
    l z = evaluation z (transpose l) := by
  induction z using BalancedTensor.induction_on with
  | h0 => simp
  | ht φ m => exact (transposeFun_eval l m φ).symm
  | ha x y hx hy => simp only [map_add, add_apply, hx, hy]

lemma evaluation_injective : Function.Injective (evaluation (k := k) (R := R) (M := M)) := by
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro z hz
  apply (Module.forall_dual_apply_eq_zero_iff k z).mp
  intro l
  rw [transpose_evaluation, hz, zero_apply]

end Nakayama
end Tachikawa



namespace Tachikawa
variable {k R : Type} [Field k] [Ring R] [Algebra k R]
variable {P Q Z : Type} [AddCommGroup P] [Module R P]
  [AddCommGroup Q] [Module R Q] [AddCommGroup Z] [Module R Z]
  [Module k Z] [IsScalarTower k R Z]

namespace Nakayama

lemma map_comp {T : Type} [AddCommGroup T] [Module R T]
    (f : P →ₗ[R] Q) (g : Q →ₗ[R] T) : map (k := k) (g.comp f) = (map g).comp (map f) := by
  ext ψ a
  rfl

end Nakayama
end Tachikawa



namespace Tachikawa
open CategoryTheory
open scoped ModuleCat.Algebra
variable {k R : Type} [Field k] [Ring R] [Algebra k R]
namespace Nakayama

def functor : ModuleCat R ⥤ ModuleCat R where
  obj M := ModuleCat.of R (Nakayama k R M)
  map f := ModuleCat.ofHom (map f.hom)
  map_id _ := ModuleCat.hom_ext map_id
  map_comp f g := ModuleCat.hom_ext (map_comp f.hom g.hom)

instance instAdditiveModuleCatFunctor : (functor (k := k) (R := R)).Additive where
  map_add {X Y f g} := by
    apply ModuleCat.hom_ext
    change map (k := k) (f.hom+g.hom) = map f.hom + map g.hom
    ext ψ a
    change ψ (a.comp (f.hom+g.hom)) = ψ (a.comp f.hom) + ψ (a.comp g.hom)
    rw [LinearMap.comp_add, map_add]

def complex (P : ChainComplex (ModuleCat R) ℤ) : ChainComplex (ModuleCat R) ℤ :=
  ((functor (k := k)).mapHomologicalComplex (ComplexShape.down ℤ)).obj P

end Nakayama
end Tachikawa



namespace Tachikawa
namespace TrivialInduction
variable {k R : Type} [Field k] [Ring R] [Algebra k R]
variable {M N : Type} [AddCommGroup M] [Module R M] [Module k M] [IsScalarTower k R M]
  [AddCommGroup N] [Module R N] [Module k N] [IsScalarTower k R N]

instance instModuleObj_1 : Module k (Obj k R M) := inferInstanceAs (Module k (M × Nakayama k R M))
instance instIsScalarTowerObj : IsScalarTower k R (Obj k R M) := inferInstanceAs (IsScalarTower k R (M × Nakayama k R M))

instance instIsScalarTowerTrivialExtensionObj : IsScalarTower k (TrivialExtension k R) (Obj k R M) :=
  IsScalarTower.of_algebraMap_smul (fun c x => by
    change (TrivSqZeroExt.inl (algebraMap k R c) : TrivialExtension k R) • x = c • x
    rw [inl_smul, IsScalarTower.algebraMap_smul])

lemma map_exact {O : Type} [AddCommGroup O] [Module R O]
    [Module k O] [IsScalarTower k R O] (f : M →ₗ[R] N) (g : N →ₗ[R] O)
    (h : Function.Exact f g) (hν : Function.Exact (Nakayama.map (k := k) f) (Nakayama.map g)) :
    Function.Exact (map (k := k) f) (map g) := by
  intro x
  constructor
  · intro hx
    obtain ⟨m,hm⟩ := (h x.1).mp (congrArg Prod.fst hx)
    obtain ⟨ψ,hψ⟩ := (hν x.2).mp (congrArg Prod.snd hx)
    exact ⟨(m,ψ), Prod.ext hm hψ⟩
  · rintro ⟨y,rfl⟩
    exact Prod.ext (h.apply_apply_eq_zero y.1) (hν.apply_apply_eq_zero y.2)

end TrivialInduction
end Tachikawa



namespace Tachikawa.TrivialInduction
variable {k R : Type} [Field k] [Ring R] [Algebra k R]
variable (n : ℕ)

lemma sum_coordinateHom (f : (Fin n → R) →ₗ[R] R) :
    ∑ i, coordinateHom (k := k) n i (f (Pi.single i 1)) = f := by
  apply LinearMap.ext
  intro x
  rw [LinearMap.sum_apply]
  change (∑ i, x i * f (Pi.single i 1)) = f x
  have hx := congrArg f (Nakayama.decomposed n (LinearMap.id : (Fin n → R) →ₗ[R] (Fin n → R))
    LinearMap.id rfl x)
  simpa only [LinearMap.id_apply, map_sum, map_smul, smul_eq_mul] using hx

def freeMap : (Fin n → TrivialExtension k R) →ₗ[TrivialExtension k R] Obj k R (Fin n → R) where
  toFun a := ∑ i, a i • unit (Pi.single i 1)
  map_add' a b := by simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' a b := by simp only [Pi.smul_apply, smul_eq_mul, mul_smul, Finset.smul_sum, RingHom.id_apply]

lemma freeMap_first (a : Fin n → TrivialExtension k R) :
    first (freeMap (k := k) n a) = fun i => (a i).fst := by
  change first (∑ i, a i • unit (Pi.single i 1)) = _
  rw [map_sum]
  ext j
  change (∑ i, (a i).fst • Pi.single i (1:R)) j = _
  simp [Finset.sum_apply, Pi.single_apply]

lemma freeMap_second (a : Fin n → TrivialExtension k R) :
    second (freeMap (k := k) n a) = ∑ i, Nakayama.evaluationBilinear (a i).snd (Pi.single i 1) := by
  change second (∑ i, a i • unit (Pi.single i 1)) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  change Nakayama.evaluationBilinear (a i).snd (Pi.single i 1) + (a i).fst • (0 : Nakayama k R (Fin n → R)) = _
  simp

lemma freeMap_second_apply (a : Fin n → TrivialExtension k R) (f : (Fin n → R) →ₗ[R] R) :
    second (freeMap (k := k) n a) f = ∑ i, (a i).snd (f (Pi.single i 1)) := by
  rw [freeMap_second]
  change (∑ i, (Nakayama.evaluationBilinear (a i).snd (Pi.single i 1) : Module.Dual k ((Fin n → R) →ₗ[R] R))) f = _
  exact LinearMap.sum_apply Finset.univ (fun i => (Nakayama.evaluationBilinear (a i).snd (Pi.single i 1) : Module.Dual k ((Fin n → R) →ₗ[R] R))) f

def freeInv (x : Obj k R (Fin n → R)) : Fin n → TrivialExtension k R :=
  fun i => ⟨x.1 i, (x.2 : Module.Dual k ((Fin n → R) →ₗ[R] R)).comp (coordinateHom n i)⟩

lemma freeMap_freeInv (x : Obj k R (Fin n → R)) : freeMap (k := k) n (freeInv n x) = x := by
  apply Prod.ext
  · exact freeMap_first n (freeInv n x)
  · apply Nakayama.ext
    intro f
    rw [← second_apply, freeMap_second_apply]
    change (∑ i, x.2 (coordinateHom n i (f (Pi.single i 1)))) = x.2 f
    rw [← map_sum, sum_coordinateHom]

lemma freeInv_freeMap (a : Fin n → TrivialExtension k R) : freeInv n (freeMap (k := k) n a) = a := by
  funext i
  apply TrivSqZeroExt.ext
  · exact congrFun (freeMap_first n a) i
  · apply DualBimodule.ext
    intro r
    change second (freeMap (k := k) n a) (coordinateHom n i r) = (a i).snd r
    rw [freeMap_second_apply]
    simp only [coordinateHom_apply, Pi.single_apply]
    simp [ite_mul, apply_ite, _root_.map_zero]

def freeEquiv : (Fin n → TrivialExtension k R) ≃ₗ[TrivialExtension k R] Obj k R (Fin n → R) :=
  LinearEquiv.ofBijective (freeMap n) ⟨Function.LeftInverse.injective (freeInv_freeMap n),
    Function.RightInverse.surjective (freeMap_freeInv n)⟩

instance instProjectiveTrivialExtensionObjForallFin : Module.Projective (TrivialExtension k R) (Obj k R (Fin n → R)) :=
  Module.Projective.of_equiv (freeEquiv (k := k) (R := R) n)

variable {M : Type} [AddCommGroup M] [Module R M] [Module k M] [IsScalarTower k R M]

instance inducedProjective [Module.Finite R M] [Module.Projective R M] :
    Module.Projective (TrivialExtension k R) (Obj k R M) := by
  let c := finiteFreeCover (R := R) (M := M)
  obtain ⟨s,hs⟩ := Module.projective_lifting_property c.map (LinearMap.id (R := R) (M := M)) c.surjective
  apply Module.Projective.of_split (map (k := k) s) (map c.map)
  rw [← map_comp, hs, map_id]

end Tachikawa.TrivialInduction



namespace Tachikawa.TrivialInduction
variable {k R : Type} [Field k] [Ring R] [Algebra k R]
variable {M N P : Type} [AddCommGroup M] [Module R M] [Module k M] [IsScalarTower k R M]
  [AddCommGroup N] [Module R N] [Module k N] [IsScalarTower k R N]
  [AddCommGroup P] [Module R P] [Module k P] [IsScalarTower k R P]

variable [FiniteDimensional k R] [FiniteDimensional k M]

omit [FiniteDimensional k R] [FiniteDimensional k M] in
lemma map_unit (a : M →ₗ[R] N) (m : M) : map (k := k) a (unit m) = unit (a m) := by
  apply Prod.ext
  · rfl
  · exact (Nakayama.map a).map_zero

end Tachikawa.TrivialInduction



namespace Tachikawa
open CategoryTheory
open scoped ModuleCat.Algebra
variable {k R : Type} [Field k] [Ring R] [Algebra k R]
namespace TrivialInduction
variable {M : Type} [AddCommGroup M] [Module R M] [Module k M] [IsScalarTower k R M]

instance nakayamaFinite [FiniteDimensional k R] [FiniteDimensional k M] :
    FiniteDimensional k (Nakayama k R M) := by
  let : Module.Finite k (M →ₗ[R] R) :=
    Module.Finite.of_injective (LinearMap.restrictScalarsₗ k R M R k)
      (LinearMap.restrictScalars_injective k)
  exact inferInstanceAs (FiniteDimensional k (Module.Dual k (M →ₗ[R] R)))

instance inducedFinite [FiniteDimensional k R] [FiniteDimensional k M] :
    FiniteDimensional k (Obj k R M) := inferInstanceAs (FiniteDimensional k (M × Nakayama k R M))

end TrivialInduction



end Tachikawa

end

end OAI
end

section
-- module Solutions.OAIQ116_Tach.Tachikawa_Corner
attribute [-instance] _root_.OAI.Tachikawa.Construction.instModuleEX _root_.OAI.Tachikawa.LeftCoinduced.coextend_additive _root_.OAI.Tachikawa.LeftCoinduced.coextend_preservesInjective _root_.OAI.Tachikawa.downIntTensorSigns
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



noncomputable section



namespace Tachikawa.C
open CategoryTheory
variable {k : Type} [Field k] [CharP k 2] (q : k)

omit [CharP k 2] in
lemma hom_rhoU_injective : Function.Injective (homPrecomp (k := k) (Z := C k q) (rhoU q)) := by
  intro f g h
  apply (RightCorner.homEquiv (f_idempotent q)).injective
  apply lambdaU_injective q
  have hh := congrArg (RightCorner.homEquiv (e_idempotent q)) h
  simpa only [homPrecomp_apply, rhoU, lambdaU,
    RightCorner.homEquiv_precomp (e_idempotent q) (f_idempotent q) (u q) (e_mul_u q) (u_mul_f q)] using hh

lemma hom_exact_rhoU : Function.Exact
    (homPrecomp (k := k) (Z := C k q) (rhoU q))
    (homPrecomp (k := k) (Z := C k q) (rhoEll q 1)) := by
  intro f
  constructor
  · intro hf
    have hz : lambdaEll q 1 (RightCorner.homEquiv (e_idempotent q) f) = 0 := by
      have h := congrArg (RightCorner.homEquiv (e_idempotent q)) hf
      simpa only [homPrecomp_apply, rhoEll, lambdaEll,
        RightCorner.homEquiv_precomp (e_idempotent q) (e_idempotent q) (ell q 1) (e_mul_ell q 1) (ell_mul_e q 1), map_zero] using h
    obtain ⟨a,ha⟩ := (exact_lambdaU q _).mp hz
    refine ⟨(RightCorner.homEquiv (f_idempotent q)).symm a, ?_⟩
    apply (RightCorner.homEquiv (e_idempotent q)).injective
    change RightCorner.homEquiv (e_idempotent q) (((RightCorner.homEquiv (f_idempotent q)).symm a).comp (rhoU q)) = _
    rw [rhoU, RightCorner.homEquiv_precomp (e_idempotent q) (f_idempotent q) (u q) (e_mul_u q) (u_mul_f q)]
    simpa only [LinearEquiv.apply_symm_apply, lambdaU, lambdaEll] using ha
  · rintro ⟨g,rfl⟩
    apply LinearMap.ext
    intro x
    change g (rhoU q (rhoEll q 1 x)) = 0
    rw [rhoU_comp_zero, map_zero]

lemma hom_exact_rhoEll (hq : q ≠ 0)
    (hp : ∀ n : ℕ, 0 < n → 1+q^n ≠ 0) (n : ℕ) : Function.Exact
    (homPrecomp (k := k) (Z := C k q) (rhoEll q (q^(n+1))))
    (homPrecomp (k := k) (Z := C k q) (rhoEll q (q^(n+2)))) := by
  intro f
  constructor
  · intro hf
    have hz : lambdaEll q (q^(n+2)) (RightCorner.homEquiv (e_idempotent q) f) = 0 := by
      have h := congrArg (RightCorner.homEquiv (e_idempotent q)) hf
      simpa only [homPrecomp_apply, rhoEll, lambdaEll,
        RightCorner.homEquiv_precomp (e_idempotent q) (e_idempotent q) (ell q (q^(n+2)))
          (e_mul_ell q _) (ell_mul_e q _), map_zero] using h
    obtain ⟨a,ha⟩ := (dualComplex_exact q hq hp n _).mp hz
    refine ⟨(RightCorner.homEquiv (e_idempotent q)).symm a, ?_⟩
    apply (RightCorner.homEquiv (e_idempotent q)).injective
    change RightCorner.homEquiv (e_idempotent q) (((RightCorner.homEquiv (e_idempotent q)).symm a).comp (rhoEll q (q^(n+1)))) = _
    rw [rhoEll, RightCorner.homEquiv_precomp (e_idempotent q) (e_idempotent q) (ell q (q^(n+1)))
      (e_mul_ell q _) (ell_mul_e q _)]
    simpa only [LinearEquiv.apply_symm_apply, lambdaU, lambdaEll] using ha
  · rintro ⟨g,rfl⟩
    apply LinearMap.ext
    intro x
    change g (rhoEll q (q^(n+1)) (rhoEll q (q^(n+2)) x)) = 0
    rw [pow_succ' q (n+1), rhoEll_comp_zero, map_zero]

omit [CharP k 2] in
lemma nu_rhoU_surjective : Function.Surjective (Nakayama.map (k := k) (rhoU q)) :=
  LinearMap.dualMap_surjective_of_injective (hom_rhoU_injective q)

lemma nu_resD_exact (hq : q ≠ 0)
    (hp : ∀ n : ℕ, 0 < n → 1+q^n ≠ 0) (n : ℕ) (hn : n ≠ 1) :
    Function.Exact (Nakayama.map (k := k) (resD q (n+1)).hom) (Nakayama.map (resD q n).hom) := by
  cases n with
  | zero =>
    change Function.Exact (homPrecomp (k := k) (Z := C k q) (rhoEll q (q^0))).dualMap
      (homPrecomp (k := k) (Z := C k q) (rhoU q)).dualMap
    rw [pow_zero]
    exact exact_dual _ _ (hom_exact_rhoU q)
  | succ n =>
    cases n with
    | zero => exact (hn rfl).elim
    | succ n =>
      change Function.Exact (homPrecomp (k := k) (Z := C k q) (rhoEll q (q^(n+2)))).dualMap
        (homPrecomp (k := k) (Z := C k q) (rhoEll q (q^(n+1)))).dualMap
      exact exact_dual _ _ (hom_exact_rhoEll q hq hp n)

end Tachikawa.C

end

end OAI
end

section
-- module Solutions.OAIQ116_Tach.Tachikawa_Period
attribute [-instance] _root_.OAI.Tachikawa.Construction.instModuleEX _root_.OAI.Tachikawa.LeftCoinduced.coextend_additive _root_.OAI.Tachikawa.LeftCoinduced.coextend_preservesInjective _root_.OAI.Tachikawa.downIntTensorSigns
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section



namespace Tachikawa.C
variable {k : Type} [Field k] [CharP k 2] (q : k)

def nuTwoAug : Nakayama k (C k q) (Ce q) →ₗ[k] Simple q where
  toFun ψ := ψ (vHom q)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def nuTwoCycle : Nakayama k (C k q) (Ce q) where
  toFun f := (f (LeftCorner.generator (e_idempotent q))) 6
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

omit [CharP k 2] in
lemma nuTwoCycle_aug : nuTwoAug q (nuTwoCycle q) = (show Simple q from (1:k)) := by
  change (vHom q (LeftCorner.generator (e_idempotent q))) 6 = 1
  exact congrArg (fun a : C k q => a 6) (vHom_generator q)

end Tachikawa.C



end

end OAI
end

section
-- module Solutions.OAIQ116_Tach.Tachikawa_Socle
attribute [-instance] _root_.OAI.Tachikawa.LeftCoinduced.coextend_additive _root_.OAI.Tachikawa.LeftCoinduced.coextend_preservesInjective _root_.OAI.Tachikawa.downIntTensorSigns
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace Tachikawa
open scoped TensorProduct
namespace Construction
variable {k : Type*} [Field k] (q : k)

def formE : SymmetrizingForm (k := k) (R := E q) :=
  TrivialExtension.symmetrizingForm.tensor TrivialExtension.symmetrizingForm

end Construction
end Tachikawa



end

end OAI
end

section
-- module Solutions.OAIQ116_Tach.Tachikawa_ReverseResolution
attribute [-instance] _root_.OAI.Tachikawa.LeftCoinduced.coextend_additive _root_.OAI.Tachikawa.LeftCoinduced.coextend_preservesInjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section

namespace Tachikawa.C
open CategoryTheory
variable {k : Type} [Field k] [CharP k 2] (q : k)

def leftDualResObj : ℕ → ModuleCat (C k q)
  | 0 => ModuleCat.of _ (Ce q × Ce q)
  | 1 => ModuleCat.of _ (Ce q)
  | 2 => ModuleCat.of _ (Cf q)
  | _+3 => ModuleCat.of _ PUnit

end Tachikawa.C



namespace Tachikawa.C
variable {k : Type} [Field k] [CharP k 2] (q : k)

def nuTopCycle : Nakayama k (C k q) (Cf q) where
  toFun g := (g (LeftCorner.generator (f_idempotent q))) 1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

end Tachikawa.C



end



noncomputable section
namespace Tachikawa
open CategoryTheory CategoryTheory.Limits HomologicalComplex
variable {k : Type} [Field k]

lemma zeroDifferential_isIso_of_quasiIso
    {K L : ChainComplex (ModuleCat k) ℤ} (f : K ⟶ L)
    (hK : ∀ i j, K.d i j = 0) (hL : ∀ i j, L.d i j = 0) [QuasiIso f] : IsIso f := by
  have (j : ℤ) : IsIso (f.f j) := by
    apply (ConcreteCategory.isIso_iff_bijective _).mpr
    have hh := shortComplex_cycles_of_quasiIso _
      ((quasiIsoAt_iff' f (j+1) j (j-1) (by simp) (by simp)).mp inferInstance)
    constructor
    · apply LinearMap.ker_eq_bot.mp
      apply LinearMap.ker_eq_bot'.mpr
      intro x hx
      obtain ⟨z,hz⟩ := hh.1 x (by change K.d j (j-1) x = 0; rw [hK]; rfl)
        ⟨0, by change L.d (j+1) j 0 = f.f j x; rw [map_zero]; exact hx.symm⟩
      change K.d (j+1) j z = x at hz
      rw [hK] at hz
      exact hz.symm
    · intro y
      obtain ⟨x,_,z,hz⟩ := hh.2 y (by change L.d j (j-1) y = 0; rw [hL]; rfl)
      refine ⟨x, ?_⟩
      change L.d (j+1) j z = f.f j x - y at hz
      rw [hL] at hz
      exact sub_eq_zero.mp hz.symm
  exact HomologicalComplex.Hom.isIso_of_components f

end Tachikawa



end

end OAI
end

section
-- module Solutions.OAIQ116_Tach.Tachikawa_Bimodule
attribute [-instance] _root_.OAI.Tachikawa.AlgebraInduction.resFinite _root_.OAI.Tachikawa.LeftCoinduced.C_finite _root_.OAI.Tachikawa.LeftCoinduced.J_finite _root_.OAI.Tachikawa.LeftCoinduced.coextend_additive _root_.OAI.Tachikawa.LeftCoinduced.coextend_preservesInjective _root_.OAI.Tachikawa.LeftCoinduced.iterate_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section



namespace Tachikawa.Enveloping
open CategoryTheory
open scoped ModuleCat.Algebra
variable {k R S : Type} [Field k] [Ring R] [Ring S] [Algebra k R] [Algebra k S]
  [FiniteDimensional k R] [FiniteDimensional k S]
  (t : SymmetrizingForm (k := k) (R := R))
  (u : SymmetrizingForm (k := k) (R := S))
  (M : FiniteModule k (Alg k R S))

abbrev envelopingForm : SymmetrizingForm (k := k) (R := Alg k R S) := t.tensor u.op

end Tachikawa.Enveloping



namespace Tachikawa.Enveloping
open CategoryTheory
open scoped TensorProduct ModuleCat.Algebra
variable {k R S : Type} [Field k] [Ring R] [Ring S] [Algebra k R] [Algebra k S]
  [FiniteDimensional k R] [FiniteDimensional k S]
  (φ : R →ₐ[k] S)

abbrev envelopingMap : Alg k R R →ₐ[k] Alg k S S :=
  Algebra.TensorProduct.map φ φ.op

def inducedRegularComplex : ChainComplex (ModuleCat.{0} (Alg k S S)) ℕ :=
  ((AlgebraInduction.functor (envelopingMap φ)).mapHomologicalComplex (.down ℕ)).obj
    (regularResolution (k := k) (R := R)).complex

instance inducedRegularComplex_finite (n : ℕ) :
    FiniteDimensional k ((inducedRegularComplex φ).X n) := by
  change FiniteDimensional k
    ((AlgebraInduction.functor (envelopingMap φ)).obj ((regularResolution (k := k) (R := R)).complex.X n))
  let : FiniteDimensional k ((regularResolution (k := k) (R := R)).complex.X n) :=
    Module.Finite.trans (Alg k R R) _
  infer_instance

instance inducedRegularComplex_finiteAlg (n : ℕ) :
    Module.Finite (Alg k S S) ((inducedRegularComplex φ).X n) :=
  Module.Finite.of_restrictScalars_finite k _ _

instance inducedRegularComplex_projective (n : ℕ) :
    Module.Projective (Alg k S S) ((inducedRegularComplex φ).X n) := by
  change Module.Projective (Alg k S S)
    ((AlgebraInduction.functor (envelopingMap φ)).obj ((regularResolution (k := k) (R := R)).complex.X n))
  infer_instance

instance inducedRegularComplex_leftProjective (n : ℕ) :
    Module.Projective S (Obj ((inducedRegularComplex φ).X n)) := projective_left _

def inducedCokerFive : FiniteModule k (Alg k S S) where
  obj := ModuleCat.of (Alg k S S) (NatCoker.C (inducedRegularComplex φ) 4)
  finite := inferInstance

def inducedY (t : SymmetrizingForm (k := k) (R := S)) : FiniteModule k (Alg k S S) :=
  (inducedCokerFive φ).negative (envelopingForm t t) 4

end Tachikawa.Enveloping



namespace Tachikawa.Enveloping
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct ModuleCat.Algebra
variable {k R S : Type} [Field k] [Ring R] [Ring S] [Algebra k R] [Algebra k S]

lemma rightFunctor_eq : rightFunctor (k := k) (R := R) (S := S) =
    ModuleCat.restrictScalars (Algebra.TensorProduct.includeRight : Sᵐᵒᵖ →ₐ[k] Alg k R S).toRingHom := rfl

lemma leftFunctor_map_exact (T : ShortComplex (ModuleCat (Alg k R S))) (h : T.Exact) :
    (T.map (leftFunctor (k := k) (R := R) (S := S))).Exact := by
  rw [ShortComplex.ShortExact.moduleCat_exact_iff_function_exact] at h ⊢
  exact h
lemma rightFunctor_map_exact (T : ShortComplex (ModuleCat (Alg k R S))) (h : T.Exact) :
    (T.map (rightFunctor (k := k) (R := R) (S := S))).Exact := by
  rw [ShortComplex.ShortExact.moduleCat_exact_iff_function_exact] at h ⊢
  exact h

instance instPreservesFiniteLimitsModuleCatAlgLeftFunctor : PreservesFiniteLimits (leftFunctor (k := k) (R := R) (S := S)) := by
  have h := ((Functor.exact_tfae (leftFunctor (k := k) (R := R) (S := S))).out (2-1) (4-1)).mp
    (leftFunctor_map_exact (k := k) (R := R) (S := S))
  exact h.1
instance instPreservesFiniteColimitsModuleCatAlgLeftFunctor : PreservesFiniteColimits (leftFunctor (k := k) (R := R) (S := S)) := by
  have h := ((Functor.exact_tfae (leftFunctor (k := k) (R := R) (S := S))).out (2-1) (4-1)).mp
    (leftFunctor_map_exact (k := k) (R := R) (S := S))
  exact h.2
instance instPreservesFiniteLimitsModuleCatAlgMulOppositeRightFunctor : PreservesFiniteLimits (rightFunctor (k := k) (R := R) (S := S)) := by
  have h := ((Functor.exact_tfae (rightFunctor (k := k) (R := R) (S := S))).out (2-1) (4-1)).mp
    (rightFunctor_map_exact (k := k) (R := R) (S := S))
  exact h.1
instance instPreservesFiniteColimitsModuleCatAlgMulOppositeRightFunctor : PreservesFiniteColimits (rightFunctor (k := k) (R := R) (S := S)) := by
  have h := ((Functor.exact_tfae (rightFunctor (k := k) (R := R) (S := S))).out (2-1) (4-1)).mp
    (rightFunctor_map_exact (k := k) (R := R) (S := S))
  exact h.2

end Tachikawa.Enveloping

end

end OAI
end

section
-- module Solutions.OAIQ116_Tach.Tachikawa_RightInduction
attribute [-instance] _root_.OAI.Tachikawa.AlgebraInduction.resFinite _root_.OAI.Tachikawa.LeftCoinduced.coextend_additive _root_.OAI.Tachikawa.LeftCoinduced.coextend_preservesInjective _root_.OAI.Tachikawa.Triangular.instProjectiveCarrierOneFree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section



namespace Tachikawa.Enveloping
open CategoryTheory
open scoped TensorProduct ModuleCat.Algebra
variable {k R S U : Type} [Field k] [Ring R] [Ring S] [Ring U]
  [Algebra k R] [Algebra k S] [Algebra k U]

def leftIndMap (φ : R →ₐ[k] S) {M N : ModuleCat (Alg k R U)} (f : M ⟶ N) :
    leftIndObj φ M ⟶ leftIndObj φ N :=
  ofBimoduleHom (BalancedTensor.mapRight (k := k) (S := S) (M := AlgebraInduction.Bimod φ) (leftMap f))
    (by
      intro u x
      induction x using BalancedTensor.induction_on with
      | h0 => simp only [smul_zero, map_zero]
      | ht s m =>
        change BalancedTensor.mk (k := k) (R := R) (S := S) s (show Obj N from f (u • m)) =
          BalancedTensor.mk s (u • (show Obj N from f m))
        exact congrArg (BalancedTensor.mk s) ((rightMap f).map_smul u m)
      | ha x y hx hy => simp only [smul_add, map_add, hx, hy])

def leftIndFunctor (φ : R →ₐ[k] S) : ModuleCat (Alg k R U) ⥤ ModuleCat (Alg k S U) where
  obj := leftIndObj φ
  map := leftIndMap φ
  map_id M := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    induction x using BalancedTensor.induction_on with
    | h0 => rfl
    | ht s m => rfl
    | ha x y hx hy =>
      exact ((leftIndMap φ (𝟙 M)).hom.map_add x y).trans
        ((congrArg₂ (fun x y => x+y) hx hy).trans ((ModuleCat.Hom.hom (𝟙 (leftIndObj φ M))).map_add x y).symm)
  map_comp f g := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    induction x using BalancedTensor.induction_on with
    | h0 => rfl
    | ht s m => rfl
    | ha x y hx hy =>
      exact ((leftIndMap φ (f ≫ g)).hom.map_add x y).trans
        ((congrArg₂ (fun x y => x+y) hx hy).trans ((leftIndMap φ f ≫ leftIndMap φ g).hom.map_add x y).symm)

def leftIndUnderlyingIso (φ : R →ₐ[k] S) (M : ModuleCat (Alg k R U)) :
    (leftFunctor (k := k) (R := S) (S := U)).obj (leftIndObj φ M) ≅
      (AlgebraInduction.functor φ).obj ((leftFunctor (k := k) (R := R) (S := U)).obj M) :=
  LinearEquiv.toModuleIso
  { toFun := fun x => x
    invFun := fun x => x
    left_inv _ := rfl
    right_inv _ := rfl
    map_add' _ _ := rfl
    map_smul' s x := by
      change (action (k := k) (R := S) (S := U)
        (BalancedTensor.T (k := k) (R := R) (S := S)
          (M := AlgebraInduction.Bimod φ) (N := Obj M)) (s ⊗ₜ[k] (1:Uᵐᵒᵖ))) x = _
      change s • ((1:Uᵐᵒᵖ) • (show BalancedTensor.T (k := k) (R := R) (S := S)
        (M := AlgebraInduction.Bimod φ) (N := Obj M) from x)) = _
      rw [one_smul]
      rfl }

end Tachikawa.Enveloping



namespace Tachikawa.Enveloping
open CategoryTheory
open scoped TensorProduct ModuleCat.Algebra
variable {k U R : Type} [Field k] [Ring U] [Ring R] [Algebra k U] [Algebra k R]

def RightObj (M : ModuleCat (Alg k U R)) := (rightFunctor (k := k) (R := U) (S := R)).obj M
instance instAddCommGroupCarrierMulOppositeRightObj (M : ModuleCat (Alg k U R)) : AddCommGroup (RightObj M) :=
  inferInstanceAs (AddCommGroup ((rightFunctor (k := k) (R := U) (S := R)).obj M))
instance instModuleCarrierMulOppositeRightObj (M : ModuleCat (Alg k U R)) : Module k (RightObj M) :=
  inferInstanceAs (Module k ((rightFunctor (k := k) (R := U) (S := R)).obj M))
instance instIsScalarTowerMulOppositeCarrierRightObj (M : ModuleCat (Alg k U R)) : IsScalarTower k Rᵐᵒᵖ (RightObj M) :=
  inferInstanceAs (IsScalarTower k Rᵐᵒᵖ ((rightFunctor (k := k) (R := U) (S := R)).obj M))
instance instModuleCarrierMulOppositeRightObj_1 (M : ModuleCat (Alg k U R)) : Module U (RightObj M) :=
  inferInstanceAs (Module U (Obj M))
instance instSMulCommClassMulOppositeCarrierRightObj (M : ModuleCat (Alg k U R)) : SMulCommClass U Rᵐᵒᵖ (RightObj M) :=
  inferInstanceAs (SMulCommClass U Rᵐᵒᵖ (Obj M))
instance instIsScalarTowerCarrierMulOppositeRightObj (M : ModuleCat (Alg k U R)) : IsScalarTower k U (RightObj M) :=
  IsScalarTower.of_algebraMap_smul fun c x => by
    change (algebraMap k U c) • (show Obj M from x) =
      (algebraMap k Rᵐᵒᵖ c) • (show Obj M from x)
    rw [IsScalarTower.algebraMap_smul, IsScalarTower.algebraMap_smul]

def rightObjMap {M N : ModuleCat (Alg k U R)} (f : M ⟶ N) : RightObj M →ₗ[Rᵐᵒᵖ] RightObj N :=
  rightMap f

def rightObjLeftMap {M N : ModuleCat (Alg k U R)} (f : M ⟶ N) : RightObj M →ₗ[U] RightObj N :=
  leftMap f

end Tachikawa.Enveloping



namespace Tachikawa.Enveloping
open CategoryTheory
open scoped TensorProduct ModuleCat.Algebra
variable {k R S U : Type} [Field k] [Ring R] [Ring S] [Ring U]
  [Algebra k R] [Algebra k S] [Algebra k U]

def RightIndType (φ : R →ₐ[k] S) (M : ModuleCat (Alg k U R)) :=
  BalancedTensor.T (k := k) (R := Rᵐᵒᵖ) (S := Sᵐᵒᵖ)
    (M := AlgebraInduction.Bimod φ.op) (N := RightObj M)

instance instAddCommGroupRightIndType (φ : R →ₐ[k] S) (M : ModuleCat (Alg k U R)) : AddCommGroup (RightIndType φ M) :=
  inferInstanceAs (AddCommGroup (BalancedTensor.T (k := k) (R := Rᵐᵒᵖ) (S := Sᵐᵒᵖ)
    (M := AlgebraInduction.Bimod φ.op) (N := RightObj M)))
instance instModuleRightIndType (φ : R →ₐ[k] S) (M : ModuleCat (Alg k U R)) : Module k (RightIndType φ M) :=
  inferInstanceAs (Module k (BalancedTensor.T (k := k) (R := Rᵐᵒᵖ) (S := Sᵐᵒᵖ)
    (M := AlgebraInduction.Bimod φ.op) (N := RightObj M)))
instance instModuleMulOppositeRightIndType (φ : R →ₐ[k] S) (M : ModuleCat (Alg k U R)) : Module Sᵐᵒᵖ (RightIndType φ M) :=
  inferInstanceAs (Module Sᵐᵒᵖ (BalancedTensor.T (k := k) (R := Rᵐᵒᵖ) (S := Sᵐᵒᵖ)
    (M := AlgebraInduction.Bimod φ.op) (N := RightObj M)))
instance instIsScalarTowerMulOppositeRightIndType (φ : R →ₐ[k] S) (M : ModuleCat (Alg k U R)) : IsScalarTower k Sᵐᵒᵖ (RightIndType φ M) :=
  inferInstanceAs (IsScalarTower k Sᵐᵒᵖ (BalancedTensor.T (k := k) (R := Rᵐᵒᵖ) (S := Sᵐᵒᵖ)
    (M := AlgebraInduction.Bimod φ.op) (N := RightObj M)))
instance instModuleRightIndType_1 (φ : R →ₐ[k] S) (M : ModuleCat (Alg k U R)) : Module U (RightIndType φ M) :=
  show Module U (BalancedTensor.T (k := k) (R := Rᵐᵒᵖ) (S := Sᵐᵒᵖ)
    (M := AlgebraInduction.Bimod φ.op) (N := RightObj M)) from
  Module.compHom _ (BalancedTensor.commutingAction (k := k) (R := Rᵐᵒᵖ) (S := Sᵐᵒᵖ)
    (U := U) (M := AlgebraInduction.Bimod φ.op) (N := RightObj M))
instance instIsScalarTowerRightIndType (φ : R →ₐ[k] S) (M : ModuleCat (Alg k U R)) : IsScalarTower k U (RightIndType φ M) :=
  IsScalarTower.of_algebraMap_smul fun c x => by
    induction x using BalancedTensor.induction_on (k := k) (R := Rᵐᵒᵖ) (S := Sᵐᵒᵖ)
      (M := AlgebraInduction.Bimod φ.op) (N := RightObj M) with
    | h0 => exact (smul_zero (algebraMap k U c) : (algebraMap k U c) • (0 : RightIndType φ M) = 0).trans (smul_zero c).symm
    | ht s m =>
      change BalancedTensor.mk s ((algebraMap k U c) • m) = c • BalancedTensor.mk s m
      rw [IsScalarTower.algebraMap_smul]
      exact (BalancedTensor.mk s).map_smul c m
    | ha x y hx hy =>
      change ((algebraMap k U c) • (show RightIndType φ M from x+y)) = c • (show RightIndType φ M from x+y)
      exact (smul_add (algebraMap k U c) (show RightIndType φ M from x) (show RightIndType φ M from y)).trans
        ((congrArg₂ (fun x y : RightIndType φ M => x+y) hx hy).trans
          (smul_add c (show RightIndType φ M from x) (show RightIndType φ M from y)).symm)
instance instSMulCommClassMulOppositeRightIndType (φ : R →ₐ[k] S) (M : ModuleCat (Alg k U R)) : SMulCommClass U Sᵐᵒᵖ (RightIndType φ M) where
  smul_comm u s x := by
    change (BalancedTensor.commutingAction (k := k) (R := Rᵐᵒᵖ) (S := Sᵐᵒᵖ)
      (U := U) (M := AlgebraInduction.Bimod φ.op) (N := RightObj M) u) (s • x) =
      s • (BalancedTensor.commutingAction (k := k) (R := Rᵐᵒᵖ) (S := Sᵐᵒᵖ)
      (U := U) (M := AlgebraInduction.Bimod φ.op) (N := RightObj M) u) x
    exact (BalancedTensor.commutingAction (k := k) (R := Rᵐᵒᵖ) (S := Sᵐᵒᵖ)
      (U := U) (M := AlgebraInduction.Bimod φ.op) (N := RightObj M) u).map_smul s x

abbrev rightIndObj (φ : R →ₐ[k] S) (M : ModuleCat (Alg k U R)) : ModuleCat (Alg k U S) :=
  ofBimodule (k := k) (R := U) (S := S) (RightIndType φ M)

abbrev rightEnvelopingMap (φ : R →ₐ[k] S) : Alg k U R →ₐ[k] Alg k U S :=
  Algebra.TensorProduct.map (AlgHom.id k U) φ.op




def rightIndUnit (φ : R →ₐ[k] S) (M : ModuleCat (Alg k U R)) :
    M ⟶ (AlgebraInduction.res (rightEnvelopingMap (U := U) φ)).obj (rightIndObj φ M) :=
  ModuleCat.ofHom (X := M)
    (Y := (AlgebraInduction.res (rightEnvelopingMap (U := U) φ)).obj (rightIndObj φ M))
  { toFun := fun m => BalancedTensor.mk (k := k) (R := Rᵐᵒᵖ) (S := Sᵐᵒᵖ)
      (show AlgebraInduction.Bimod φ.op from (1:Sᵐᵒᵖ)) (show RightObj M from m)
    map_add' := by intro m n; exact (BalancedTensor.mk (k := k) (R := Rᵐᵒᵖ) (S := Sᵐᵒᵖ)
      (N := RightObj M) (show AlgebraInduction.Bimod φ.op from (1:Sᵐᵒᵖ))).map_add m n
    map_smul' a m := by
      let t : RightObj M →ₗ[k] RightIndType φ M := BalancedTensor.mk (k := k) (R := Rᵐᵒᵖ) (S := Sᵐᵒᵖ)
        (show AlgebraInduction.Bimod φ.op from (1:Sᵐᵒᵖ))
      change t (show RightObj M from a • m) =
        (action (k := k) (R := U) (S := S) (RightIndType φ M) (rightEnvelopingMap φ a)) (t m)
      induction a using OAI.tensorInductionOn with
      | tmul u r =>
        change t (show RightObj M from (u ⊗ₜ[k] r) • m) = u • (φ.op r • t m)
        rw [smul_comm u (φ.op r)]
        change t (show RightObj M from (u ⊗ₜ[k] r) • m) = φ.op r • t (u • (show RightObj M from m))
        trans t (r • u • (show RightObj M from m))
        · apply congrArg t
          exact (tmul_smul M u r m).trans (smul_comm u r (show RightObj M from m))
        exact (AlgebraInduction.unit φ.op (ModuleCat.of Rᵐᵒᵖ (RightObj M))).hom.map_smul r (u • (show RightObj M from m))
      | add a b ha hb =>
        rw [map_add, map_add]
        exact (congrArg (fun x : M => t (show RightObj M from x)) (add_smul a b m)).trans
          ((t.map_add _ _).trans (congrArg₂ (fun x y => x+y) ha hb)) }




def rightIndMapLinear (φ : R →ₐ[k] S) {M N : ModuleCat (Alg k U R)} (f : M ⟶ N) :
    RightIndType φ M →ₗ[U] RightIndType φ N where
  toFun := BalancedTensor.mapRight (k := k) (S := Sᵐᵒᵖ) (M := AlgebraInduction.Bimod φ.op) (rightObjMap f)
  map_add' := (BalancedTensor.mapRight (k := k) (S := Sᵐᵒᵖ)
    (M := AlgebraInduction.Bimod φ.op) (rightObjMap f)).map_add
  map_smul' u x := by
    induction x using BalancedTensor.induction_on (k := k) (R := Rᵐᵒᵖ) (S := Sᵐᵒᵖ)
      (M := AlgebraInduction.Bimod φ.op) (N := RightObj M) with
    | h0 => rfl
    | ht s m =>
      change BalancedTensor.mk (k := k) (R := Rᵐᵒᵖ) (S := Sᵐᵒᵖ) s (show RightObj N from f (u • m)) =
        BalancedTensor.mk s (u • (show RightObj N from f m))
      exact congrArg (BalancedTensor.mk s) ((rightObjLeftMap f).map_smul u m)
    | ha x y hx hy =>
      let g : RightIndType φ M →ₗ[k] RightIndType φ N :=
        (BalancedTensor.mapRight (k := k) (S := Sᵐᵒᵖ)
          (M := AlgebraInduction.Bimod φ.op) (rightObjMap f)).restrictScalars k
      change g (u • (show RightIndType φ M from x+y)) = u • g (x+y)
      exact (congrArg g (smul_add u (show RightIndType φ M from x) (show RightIndType φ M from y))).trans
        ((g.map_add _ _).trans ((congrArg₂ (fun x y : RightIndType φ N => x+y) hx hy).trans
          ((smul_add u (g x) (g y)).symm.trans
            (congrArg (fun z : RightIndType φ N => u • z) (g.map_add x y).symm))))

def rightIndMap (φ : R →ₐ[k] S) {M N : ModuleCat (Alg k U R)} (f : M ⟶ N) :
    rightIndObj φ M ⟶ rightIndObj φ N :=
  ofBimoduleHom (rightIndMapLinear φ f) (by
    intro s x
    exact (BalancedTensor.mapRight (k := k) (S := Sᵐᵒᵖ)
      (M := AlgebraInduction.Bimod φ.op) (rightObjMap f)).map_smul s x)

lemma rightInd_hom_ext (φ : R →ₐ[k] S) {M : ModuleCat (Alg k U R)} {N : ModuleCat (Alg k U S)}
    {f g : rightIndObj φ M ⟶ N}
    (h : ∀ (s : AlgebraInduction.Bimod φ.op) (m : RightObj M),
      f (BalancedTensor.mk s m) = g (BalancedTensor.mk s m)) : f = g := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  induction x using BalancedTensor.induction_on (k := k) (R := Rᵐᵒᵖ) (S := Sᵐᵒᵖ)
    (M := AlgebraInduction.Bimod φ.op) (N := RightObj M) with
  | h0 => exact f.hom.map_zero.trans g.hom.map_zero.symm
  | ht s m => exact h s m
  | ha x y hx hy =>
    exact (f.hom.map_add x y).trans
      ((congrArg₂ (fun x y => x+y) hx hy).trans (g.hom.map_add x y).symm)

def rightIndFunctor (φ : R →ₐ[k] S) : ModuleCat (Alg k U R) ⥤ ModuleCat (Alg k U S) where
  obj := rightIndObj φ
  map := rightIndMap φ
  map_id M := by apply rightInd_hom_ext φ; intro s m; rfl
  map_comp f g := by apply rightInd_hom_ext φ; intro s m; rfl

instance instAdditiveModuleCatAlgRightIndFunctor (φ : R →ₐ[k] S) : (rightIndFunctor (U := U) φ).Additive where
  map_add {_X _Y f g} := by
    apply rightInd_hom_ext φ
    intro s m
    exact (BalancedTensor.mk (k := k) (R := Rᵐᵒᵖ) (S := Sᵐᵒᵖ)
      (M := AlgebraInduction.Bimod φ.op) (N := RightObj _Y) s).map_add (f m) (g m)




def rightIndResMap (φ : R →ₐ[k] S) {M : ModuleCat (Alg k U R)} {N : ModuleCat (Alg k U S)}
    (f : M ⟶ (AlgebraInduction.res (rightEnvelopingMap (U := U) φ)).obj N) :
    ModuleCat.of Rᵐᵒᵖ (RightObj M) ⟶ (AlgebraInduction.res φ.op).obj (ModuleCat.of Sᵐᵒᵖ (RightObj N)) :=
  ModuleCat.ofHom (X := ModuleCat.of Rᵐᵒᵖ (RightObj M))
    (Y := (AlgebraInduction.res φ.op).obj (ModuleCat.of Sᵐᵒᵖ (RightObj N)))
  { toFun := fun m => (show RightObj N from f m)
    map_add' := f.hom.map_add
    map_smul' r m := by
      have h := f.hom.map_smul ((1:U) ⊗ₜ[k] r) m
      change (show N from f (((1:U) ⊗ₜ[k] r) • (show M from m))) =
        (rightEnvelopingMap φ ((1:U) ⊗ₜ[k] r)) • (show N from f m) at h
      exact h }

lemma rightIndResMap_left (φ : R →ₐ[k] S) {M : ModuleCat (Alg k U R)} {N : ModuleCat (Alg k U S)}
    (f : M ⟶ (AlgebraInduction.res (rightEnvelopingMap (U := U) φ)).obj N) (u : U) (m : RightObj M) :
    (show RightObj N from f (u • m)) = u • (show RightObj N from f m) := by
  have h := f.hom.map_smul (u ⊗ₜ[k] (1:Rᵐᵒᵖ)) m
  change (show N from f ((u ⊗ₜ[k] (1:Rᵐᵒᵖ)) • (show M from m))) =
    rightEnvelopingMap φ (u ⊗ₜ[k] (1:Rᵐᵒᵖ)) • (show N from f m) at h
  change (show N from f ((u ⊗ₜ[k] (1:Rᵐᵒᵖ)) • (show M from m))) =
    (u ⊗ₜ[k] (1:Sᵐᵒᵖ)) • (show N from f m)
  simpa only [rightEnvelopingMap, Algebra.TensorProduct.map_tmul, map_one, AlgHom.id_apply] using h

def rightIndExtendRightLinear (φ : R →ₐ[k] S) {M : ModuleCat (Alg k U R)} {N : ModuleCat (Alg k U S)}
    (f : M ⟶ (AlgebraInduction.res (rightEnvelopingMap (U := U) φ)).obj N) :
    RightIndType φ M →ₗ[Sᵐᵒᵖ] RightObj N :=
  (AlgebraInduction.extend φ.op (rightIndResMap φ f)).hom

lemma rightIndExtendRightLinear_left (φ : R →ₐ[k] S) {M : ModuleCat (Alg k U R)} {N : ModuleCat (Alg k U S)}
    (f : M ⟶ (AlgebraInduction.res (rightEnvelopingMap (U := U) φ)).obj N) (u : U) (x) :
    rightIndExtendRightLinear φ f (u • x) = u • rightIndExtendRightLinear φ f x := by
  induction x using BalancedTensor.induction_on (k := k) (R := Rᵐᵒᵖ) (S := Sᵐᵒᵖ)
    (M := AlgebraInduction.Bimod φ.op) (N := RightObj M) with
  | h0 =>
    exact (congrArg (rightIndExtendRightLinear φ f) (smul_zero u)).trans
      ((rightIndExtendRightLinear φ f).map_zero.trans (smul_zero u).symm)
  | ht s m =>
    change (show Sᵐᵒᵖ from s) • (show RightObj N from f (u • m)) =
      u • ((show Sᵐᵒᵖ from s) • (show RightObj N from f m))
    rw [rightIndResMap_left φ f]
    exact (smul_comm u (show Sᵐᵒᵖ from s) (show RightObj N from f m)).symm
  | ha x y hx hy =>
    change rightIndExtendRightLinear φ f (u • (show RightIndType φ M from x+y)) = _
    exact (congrArg (rightIndExtendRightLinear φ f)
      (smul_add u (show RightIndType φ M from x) (show RightIndType φ M from y))).trans
      (((rightIndExtendRightLinear φ f).map_add _ _).trans
        ((congrArg₂ (fun x y : RightObj N => x+y) hx hy).trans
          ((smul_add u _ _).symm.trans (congrArg (fun x : RightObj N => u • x)
            ((rightIndExtendRightLinear φ f).map_add x y).symm))))

def rightIndExtendLinear (φ : R →ₐ[k] S) {M : ModuleCat (Alg k U R)} {N : ModuleCat (Alg k U S)}
    (f : M ⟶ (AlgebraInduction.res (rightEnvelopingMap (U := U) φ)).obj N) :
    RightIndType φ M →ₗ[U] RightObj N where
  toFun := rightIndExtendRightLinear φ f
  map_add' := (rightIndExtendRightLinear φ f).map_add
  map_smul' := rightIndExtendRightLinear_left φ f

def rightReassembleIso (M : ModuleCat (Alg k U S)) :
    ofBimodule (k := k) (R := U) (S := S) (RightObj M) ≅ M :=
  LinearEquiv.toModuleIso (show (ofBimodule (k := k) (R := U) (S := S) (RightObj M)) ≃ₗ[Alg k U S] M from
  { toFun := fun x => x
    invFun := fun x => x
    left_inv _ := rfl
    right_inv _ := rfl
    map_add' _ _ := rfl
    map_smul' a x := by
      change (show M from (action (k := k) (R := U) (S := S) (RightObj M) a) x) = a • (show M from x)
      induction a using OAI.tensorInductionOn with
      | tmul r s => exact (tmul_smul M r s x).symm
      | add a b ha hb =>
        rw [map_add, add_smul]
        exact congrArg₂ (fun x y : M => x+y) ha hb })

def rightIndExtend (φ : R →ₐ[k] S) {M : ModuleCat (Alg k U R)} {N : ModuleCat (Alg k U S)}
    (f : M ⟶ (AlgebraInduction.res (rightEnvelopingMap (U := U) φ)).obj N) :
    rightIndObj φ M ⟶ N :=
  ofBimoduleHom (rightIndExtendLinear φ f)
    (fun s x => (rightIndExtendRightLinear φ f).map_smul s x) ≫ (rightReassembleIso N).hom




def rightIndComparisonHom (φ : R →ₐ[k] S) (M : ModuleCat (Alg k U R)) :
    (AlgebraInduction.functor (rightEnvelopingMap (U := U) φ)).obj M ⟶ rightIndObj φ M :=
  AlgebraInduction.extend (k := k) (R := Alg k U R) (S := Alg k U S)
    (N := M) (P := rightIndObj φ M) (rightEnvelopingMap φ) (rightIndUnit φ M)

def rightIndComparisonInv (φ : R →ₐ[k] S) (M : ModuleCat (Alg k U R)) :
    rightIndObj φ M ⟶ (AlgebraInduction.functor (rightEnvelopingMap (U := U) φ)).obj M :=
  rightIndExtend (k := k) (R := R) (S := S) (U := U) φ (M := M)
    (N := (AlgebraInduction.functor (rightEnvelopingMap (U := U) φ)).obj M)
    (AlgebraInduction.unit (k := k) (R := Alg k U R) (S := Alg k U S)
      (rightEnvelopingMap (U := U) φ) M)

lemma rightIndComparison_inv_unit (φ : R →ₐ[k] S) (M : ModuleCat (Alg k U R)) (m : M) :
    rightIndComparisonInv φ M (rightIndUnit φ M m) =
      AlgebraInduction.unit (k := k) (R := Alg k U R) (S := Alg k U S) (rightEnvelopingMap φ) M m := by
  change (1:Sᵐᵒᵖ) • (show RightObj ((AlgebraInduction.functor (k := k) (rightEnvelopingMap (U := U) φ)).obj M) from
    AlgebraInduction.unit (k := k) (rightEnvelopingMap (U := U) φ) M m) = _
  exact one_smul _ _

lemma rightIndComparison_hom_unit (φ : R →ₐ[k] S) (M : ModuleCat (Alg k U R)) (m : M) :
    rightIndComparisonHom φ M (AlgebraInduction.unit (k := k) (R := Alg k U R)
      (S := Alg k U S) (rightEnvelopingMap φ) M m) = rightIndUnit φ M m := by
  change (1:Alg k U S) • (show rightIndObj φ M from rightIndUnit φ M m) = _
  exact one_smul _ _

lemma rightIndComparison_hom_inv (φ : R →ₐ[k] S) (M : ModuleCat (Alg k U R)) :
    rightIndComparisonHom φ M ≫ rightIndComparisonInv φ M = 𝟙 _ := by
  apply (AlgebraInduction.homEquiv (k := k) (R := Alg k U R) (S := Alg k U S)
    (rightEnvelopingMap φ) M _).injective
  ext m
  change rightIndComparisonInv φ M (rightIndComparisonHom φ M
    (AlgebraInduction.unit (k := k) (rightEnvelopingMap (U := U) φ) M m)) =
      AlgebraInduction.unit (k := k) (rightEnvelopingMap (U := U) φ) M m
  rw [rightIndComparison_hom_unit, rightIndComparison_inv_unit]

lemma rightIndComparison_inv_hom (φ : R →ₐ[k] S) (M : ModuleCat (Alg k U R)) :
    rightIndComparisonInv φ M ≫ rightIndComparisonHom φ M = 𝟙 _ := by
  apply rightInd_hom_ext φ
  intro s m
  have h := (rightObjMap (rightIndComparisonHom φ M)).map_smul (show Sᵐᵒᵖ from s)
    (show RightObj ((AlgebraInduction.functor (k := k) (rightEnvelopingMap (U := U) φ)).obj M) from
      AlgebraInduction.unit (k := k) (rightEnvelopingMap (U := U) φ) M m)
  change rightIndComparisonHom φ M ((show Sᵐᵒᵖ from s) •
    (show RightObj ((AlgebraInduction.functor (k := k) (rightEnvelopingMap (U := U) φ)).obj M) from
      AlgebraInduction.unit (k := k) (rightEnvelopingMap (U := U) φ) M m)) = _
  apply h.trans
  apply Eq.trans (congrArg (fun x : RightObj (rightIndObj φ M) => (show Sᵐᵒᵖ from s) • x)
    (rightIndComparison_hom_unit φ M m))
  change (1:U) • ((show Sᵐᵒᵖ from s) •
    (show RightIndType φ M from BalancedTensor.mk (k := k) (R := Rᵐᵒᵖ) (S := Sᵐᵒᵖ)
      (M := AlgebraInduction.Bimod φ.op) (N := RightObj M)
      (show AlgebraInduction.Bimod φ.op from (1:Sᵐᵒᵖ)) m)) = BalancedTensor.mk s m
  rw [one_smul]
  exact (AlgebraInduction.mk_one_smul φ.op (ModuleCat.of Rᵐᵒᵖ (RightObj M)) (show Sᵐᵒᵖ from s) m).symm

def rightIndComparisonIso (φ : R →ₐ[k] S) (M : ModuleCat (Alg k U R)) :
    (AlgebraInduction.functor (rightEnvelopingMap (U := U) φ)).obj M ≅ rightIndObj φ M where
  hom := rightIndComparisonHom φ M
  inv := rightIndComparisonInv φ M
  hom_inv_id := rightIndComparison_hom_inv φ M
  inv_hom_id := rightIndComparison_inv_hom φ M

end Tachikawa.Enveloping



namespace Tachikawa
open CategoryTheory
variable {R : Type} [Ring R]

namespace ProjectiveResolution
variable {M N : ModuleCat.{0} R} (P : CategoryTheory.ProjectiveResolution M)
    (Q : CategoryTheory.ProjectiveResolution N)

def prod : CategoryTheory.ProjectiveResolution (ModuleCat.of R (M × N)) :=
  resolutionOfExact _ (fun n => ModuleCat.of R (P.complex.X n × Q.complex.X n))
    (fun n => ModuleCat.ofHom ((P.complex.d (n+1) n).hom.prodMap (Q.complex.d (n+1) n).hom))
    (ModuleCat.ofHom ((P.π.f 0).hom.prodMap (Q.π.f 0).hom))
    (fun n => exact_prodMap _ _ _ _ (function_exact_succ P n) (function_exact_succ Q n))
    (exact_prodMap _ _ _ _ (function_exact_zero P) (function_exact_zero Q))
    (by
      rintro ⟨m,n⟩
      obtain ⟨p,hp⟩ := (ModuleCat.epi_iff_surjective (P.π.f 0)).mp inferInstance m
      obtain ⟨q,hq⟩ := (ModuleCat.epi_iff_surjective (Q.π.f 0)).mp inferInstance n
      exact ⟨(p,q),Prod.ext hp hq⟩)
    (fun n => by infer_instance)

end ProjectiveResolution
end Tachikawa



namespace Tachikawa
open CategoryTheory CategoryTheory.Limits
open scoped ModuleCat.Algebra
variable {k R : Type} [Field k] [Ring R] [Algebra k R]

namespace ProjectiveResolution
variable (M : ModuleCat.{0} R) [Projective M]

def simpleSelf : CategoryTheory.ProjectiveResolution M :=
  resolutionOfExact M (simpleTerm M) (fun _ => 0) (simpleAug M)
    (by
      intro n x
      refine ⟨fun _ => ⟨PUnit.unit, ?_⟩, fun _ => rfl⟩
      change (0 : PUnit) = x
      exact Subsingleton.elim _ _)
    (by intro x; exact ⟨fun hx => ⟨PUnit.unit,hx.symm⟩,fun ⟨_,hx⟩ => hx.symm⟩)
    (Function.surjective_id)
    (by intro n; cases n <;> dsimp [simpleTerm] <;> infer_instance)

lemma simpleSelf_above (n : ℕ) (hn : 0 < n) : IsZero ((simpleSelf M).complex.X n) := by
  cases n with
  | zero => omega
  | succ n =>
    change IsZero (ModuleCat.of R PUnit)
    exact ModuleCat.isZero_of_subsingleton _

variable {M} {N : ModuleCat.{0} R} (P : CategoryTheory.ProjectiveResolution M)
    (Q : CategoryTheory.ProjectiveResolution N)

omit [Projective M] in
lemma prod_above (b n : ℕ) (hP : ∀ i, b < i → IsZero (P.complex.X i))
    (hQ : ∀ i, b < i → IsZero (Q.complex.X i)) (hn : b < n) :
    IsZero ((prod P Q).complex.X n) := by
  let := ModuleCat.subsingleton_of_isZero (hP n hn)
  let := ModuleCat.subsingleton_of_isZero (hQ n hn)
  change IsZero (ModuleCat.of R (P.complex.X n × Q.complex.X n))
  exact ModuleCat.isZero_of_subsingleton _

end ProjectiveResolution
end Tachikawa



namespace Tachikawa.Enveloping
open CategoryTheory
open scoped TensorProduct ModuleCat.Algebra
variable {k R S : Type} [Field k] [Ring R] [Ring S] [Algebra k R] [Algebra k S]

def leftResolutionOf {M : ModuleCat (Alg k R S)} (P : CategoryTheory.ProjectiveResolution M)
    (hP : ∀ n, Module.Finite (Alg k R S) (P.complex.X n)) :
    CategoryTheory.ProjectiveResolution (leftFunctor.obj M) where
  complex := (leftFunctor.mapHomologicalComplex _).obj P.complex
  projective n := by
    let := hP n
    let : Module.Projective R (Obj (P.complex.X n)) := projective_left _
    change Projective (ModuleCat.of R (Obj (P.complex.X n)))
    infer_instance
  π := (leftFunctor.mapHomologicalComplex _).map P.π ≫
    (HomologicalComplex.singleMapHomologicalComplex _ _ _).hom.app _
  quasiIso := inferInstance

end Tachikawa.Enveloping



namespace Tachikawa.Enveloping
open CategoryTheory HomologicalComplex
open scoped TensorProduct ModuleCat.Algebra
variable {k R S : Type} [Field k] [Ring R] [Ring S] [Algebra k R] [Algebra k S]
  [FiniteDimensional k R] [FiniteDimensional k S]

instance regular_right_projective : Module.Projective Rᵐᵒᵖ (Obj (regular (k := k) (R := R))) := by
  let : Module.Projective Rᵐᵒᵖ R := Module.Projective.of_equiv (MulOpposite.opLinearEquiv Rᵐᵒᵖ).symm
  exact Module.Projective.of_equiv (regularRightEquiv (k := k) (R := R)).symm

instance rightFunctor_reflectsIsomorphisms :
    (rightFunctor (k := k) (R := R) (S := S)).ReflectsIsomorphisms := by
  rw [rightFunctor_eq]
  infer_instance

end Tachikawa.Enveloping



end

end OAI
end

section
-- module Solutions.OAIQ116_Tach.Tachikawa_Coinduction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section

namespace Tachikawa.C
open CategoryTheory
variable {k : Type} [Field k] [CharP k 2] (q : k)

def rightDualResObj : ℕ → ModuleCat (C k q)ᵐᵒᵖ
  | 0 => ModuleCat.of _ (eC q × eC q)
  | 1 => ModuleCat.of _ (eC q)
  | 2 => ModuleCat.of _ (fC q)
  | _+3 => ModuleCat.of _ PUnit

end Tachikawa.C



namespace Tachikawa.Construction
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct ModuleCat.Algebra
variable {k : Type} [Field k] [CharP k 2] (q : k)

instance instFiniteCSubtypeMemSubmoduleCe : Module.Finite (C k q) (C.Ce q) :=
  Module.Finite.of_restrictScalars_finite k _ _
instance instFiniteCSubtypeMemSubmoduleCf : Module.Finite (C k q) (C.Cf q) :=
  Module.Finite.of_restrictScalars_finite k _ _

def TLeftObj : ModuleCat (C k q) := ModuleCat.of (C k q) (C k q × DualBimodule k (C k q))
def TRightObj : ModuleCat (C k q)ᵐᵒᵖ := ModuleCat.of (C k q)ᵐᵒᵖ (C k q × DualBimodule k (C k q))

end Tachikawa.Construction



namespace Tachikawa.Construction
open CategoryTheory
open scoped TensorProduct ModuleCat.Algebra
variable {k : Type} [Field k] (q : k)

abbrev inclusionC : C k q →ₐ[k] T q :=
  TrivSqZeroExt.inlAlgHom k (C k q) (DualBimodule k (C k q))
abbrev inclusionB : B q →ₐ[k] E q := Algebra.TensorProduct.map (inclusionC q) (inclusionC q)

def tLeftUnderlying : TLeftObj q ≃ₗ[k] T q where
  toFun := id
  invFun := id
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' c x := by
    change (algebraMap k (C k q) c) • (show C k q × DualBimodule k (C k q) from x) =
      c • (show C k q × DualBimodule k (C k q) from x)
    exact IsScalarTower.algebraMap_smul (C k q) c _

lemma tLeftUnderlying_smul (r : C k q) (x : TLeftObj q) :
    tLeftUnderlying q (r • x) = inclusionC q r * tLeftUnderlying q x := by
  apply TrivSqZeroExt.ext
  · rfl
  · change r • (show C k q × DualBimodule k (C k q) from x).2 =
      r • (show C k q × DualBimodule k (C k q) from x).2 +
        MulOpposite.op (show C k q × DualBimodule k (C k q) from x).1 • (0:DualBimodule k (C k q))
    rw [smul_zero, add_zero]

def eLeftTensorEquiv : OuterTensor.Obj k (C k q) (C k q) (TLeftObj q) (TLeftObj q) ≃ₗ[k] E q :=
  TensorProduct.congr (tLeftUnderlying q) (tLeftUnderlying q)

lemma eLeftTensorEquiv_action (r : B q) :
    (eLeftTensorEquiv q).toLinearMap.comp (OuterTensor.action k (C k q) (C k q) (TLeftObj q) (TLeftObj q) r) =
      (LinearMap.mulLeft k (inclusionB q r)).comp (eLeftTensorEquiv q).toLinearMap := by
  induction r using OAI.tensorInductionOn with
  | tmul a b =>
    apply TensorProduct.ext'
    intro x y
    change (tLeftUnderlying q (a • x)) ⊗ₜ[k] (tLeftUnderlying q (b • y)) =
      (inclusionC q a ⊗ₜ[k] inclusionC q b) *
        ((tLeftUnderlying q x) ⊗ₜ[k] (tLeftUnderlying q y))
    rw [tLeftUnderlying_smul, tLeftUnderlying_smul, Algebra.TensorProduct.tmul_mul_tmul]
  | add r s hr hs =>
    apply LinearMap.ext
    intro x
    change eLeftTensorEquiv q ((OuterTensor.action k (C k q) (C k q) (TLeftObj q) (TLeftObj q) (r+s)) x) =
      inclusionB q (r+s) * eLeftTensorEquiv q x
    rw [map_add, map_add]
    change eLeftTensorEquiv q ((OuterTensor.action k (C k q) (C k q) (TLeftObj q) (TLeftObj q) r) x +
      (OuterTensor.action k (C k q) (C k q) (TLeftObj q) (TLeftObj q) s) x) = _
    apply ((eLeftTensorEquiv q).map_add _ _).trans
    apply Eq.trans (congrArg₂ (fun a b : E q => a+b) (LinearMap.congr_fun hr x) (LinearMap.congr_fun hs x))
    exact (add_mul (inclusionB q r) (inclusionB q s) (eLeftTensorEquiv q x)).symm

lemma eLeftTensorEquiv_smul (r : B q) (x : OuterTensor.Obj k (C k q) (C k q) (TLeftObj q) (TLeftObj q)) :
    eLeftTensorEquiv q (r • x) = inclusionB q r * eLeftTensorEquiv q x :=
  LinearMap.congr_fun (eLeftTensorEquiv_action q r) x

end Tachikawa.Construction



namespace Tachikawa.Construction
open CategoryTheory
open scoped ModuleCat.Algebra

variable {k : Type} [Field k] (q H : k) (hH : H ≠ 0)

abbrev U := Enveloping.twistedRegular (sigma q H hH)

end Tachikawa.Construction



end

end OAI
end

section
-- module Solutions.OAIQ116_Tach.Tachikawa_Induction
attribute [-instance] _root_.OAI.Tachikawa.AlgebraInduction.resFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section



namespace Tachikawa.Enveloping
open CategoryTheory
open scoped TensorProduct ModuleCat.Algebra
variable {k R S : Type} [Field k] [Ring R] [Ring S] [Algebra k R] [Algebra k S]

abbrev leftRestrictedRegular (φ : R →ₐ[k] S) : ModuleCat (Alg k R S) :=
  ofBimodule (k := k) (R := R) (S := S) (LeftRestrictedRegular φ)

def regularRightUnitTarget (φ : R →ₐ[k] S) : regular (k := k) (R := R) ⟶
    (AlgebraInduction.res (rightEnvelopingMap (U := R) φ)).obj (leftRestrictedRegular φ) :=
  ModuleCat.ofHom (X := regular (k := k) (R := R))
    (Y := (AlgebraInduction.res (rightEnvelopingMap (U := R) φ)).obj (leftRestrictedRegular φ))
  { toFun := fun r => φ r
    map_add' := φ.map_add
    map_smul' a x := by
      change φ ((action (k := k) (R := R) (S := R) R a) x) =
        (action (k := k) (R := R) (S := S) (LeftRestrictedRegular φ) (rightEnvelopingMap φ a)) (φ x)
      induction a using OAI.tensorInductionOn with
      | tmul r s =>
        change φ (r * ((show R from x) * s.unop)) = φ r * (φ x * φ s.unop)
        rw [map_mul, map_mul]
      | add a b ha hb =>
        rw [map_add, map_add, map_add]
        change φ ((action (k := k) (R := R) (S := R) R a) x +
          (action (k := k) (R := R) (S := R) R b) x) = _
        exact (φ.map_add _ _).trans (congrArg₂ (fun x y : LeftRestrictedRegular φ => x+y) ha hb) }

def rightIndRegularHom (φ : R →ₐ[k] S) :
    rightIndObj φ (regular (k := k) (R := R)) ⟶ leftRestrictedRegular φ :=
  rightIndExtend φ (regularRightUnitTarget φ)

lemma rightIndRegularHom_mk (φ : R →ₐ[k] S) (s : AlgebraInduction.Bimod φ.op)
    (r : RightObj (regular (k := k) (R := R))) :
    (show S from rightIndRegularHom φ (BalancedTensor.mk s r)) = φ r * (show Sᵐᵒᵖ from s).unop := by
  change φ (1:R) * (φ r * (show Sᵐᵒᵖ from s).unop) = _
  rw [map_one, one_mul]

def rightIndRegularInvLinear (φ : R →ₐ[k] S) : S →ₗ[Sᵐᵒᵖ]
    RightIndType φ (regular (k := k) (R := R)) :=
  ((LinearMap.toSpanSingleton Sᵐᵒᵖ _)
    (show RightIndType φ (regular (k := k) (R := R)) from
      rightIndUnit φ (regular (k := k) (R := R)) (1:R))).comp
    (MulOpposite.opLinearEquiv Sᵐᵒᵖ).toLinearMap

lemma rightIndRegularInvLinear_apply (φ : R →ₐ[k] S) (s : S) :
    rightIndRegularInvLinear φ s = BalancedTensor.mk (k := k) (R := Rᵐᵒᵖ) (S := Sᵐᵒᵖ)
      (N := RightObj (regular (k := k) (R := R)))
      (show AlgebraInduction.Bimod φ.op from MulOpposite.op s) (1:R) := by
  exact (AlgebraInduction.mk_one_smul φ.op
    (ModuleCat.of Rᵐᵒᵖ (RightObj (regular (k := k) (R := R)))) (MulOpposite.op s) (1:R)).symm

lemma rightIndRegularInvLinear_left (φ : R →ₐ[k] S) (r : R) (s : S) :
    rightIndRegularInvLinear φ (φ r * s) = r • rightIndRegularInvLinear φ s := by
  rw [rightIndRegularInvLinear_apply, rightIndRegularInvLinear_apply]
  trans BalancedTensor.mk (k := k) (R := Rᵐᵒᵖ) (S := Sᵐᵒᵖ)
    (M := AlgebraInduction.Bimod φ.op) (N := RightObj (regular (k := k) (R := R)))
    (MulOpposite.op (MulOpposite.op r) • (show AlgebraInduction.Bimod φ.op from MulOpposite.op s)) (1:R)
  · rfl
  trans BalancedTensor.mk (k := k) (R := Rᵐᵒᵖ) (S := Sᵐᵒᵖ)
    (N := RightObj (regular (k := k) (R := R)))
    (show AlgebraInduction.Bimod φ.op from MulOpposite.op s)
    (MulOpposite.op r • (show RightObj (regular (k := k) (R := R)) from (1:R)))
  · exact BalancedTensor.balance _ _ _
  change BalancedTensor.mk (k := k) (R := Rᵐᵒᵖ) (S := Sᵐᵒᵖ)
    (N := RightObj (regular (k := k) (R := R)))
    (show AlgebraInduction.Bimod φ.op from MulOpposite.op s) (1 * (1 * r)) =
    BalancedTensor.mk (k := k) (R := Rᵐᵒᵖ) (S := Sᵐᵒᵖ)
    (N := RightObj (regular (k := k) (R := R)))
    (show AlgebraInduction.Bimod φ.op from MulOpposite.op s) (r * (1 * 1))
  exact congrArg (fun z : R => BalancedTensor.mk (k := k) (R := Rᵐᵒᵖ) (S := Sᵐᵒᵖ)
    (N := RightObj (regular (k := k) (R := R)))
    (show AlgebraInduction.Bimod φ.op from MulOpposite.op s)
    (show RightObj (regular (k := k) (R := R)) from z)) (show (1:R) * (1*r) = r * (1*1) by simp only [one_mul, mul_one])

def rightIndRegularInv (φ : R →ₐ[k] S) :
    leftRestrictedRegular φ ⟶ rightIndObj φ (regular (k := k) (R := R)) :=
  ofBimoduleHom
    (show LeftRestrictedRegular φ →ₗ[R] RightIndType φ (regular (k := k) (R := R)) from
      { toFun := rightIndRegularInvLinear φ
        map_add' := (rightIndRegularInvLinear φ).map_add
        map_smul' := rightIndRegularInvLinear_left φ })
    (fun s x => (rightIndRegularInvLinear φ).map_smul s x)

def rightIndRegularIso (φ : R →ₐ[k] S) :
    rightIndObj φ (regular (k := k) (R := R)) ≅ leftRestrictedRegular φ where
  hom := rightIndRegularHom φ
  inv := rightIndRegularInv φ
  hom_inv_id := by
    apply rightInd_hom_ext φ
    intro s r
    change rightIndRegularInvLinear φ (show S from rightIndRegularHom φ
      (show rightIndObj φ (regular (k := k) (R := R)) from BalancedTensor.mk s r)) =
      (show RightIndType φ (regular (k := k) (R := R)) from BalancedTensor.mk s r)
    trans rightIndRegularInvLinear φ (φ r * (show Sᵐᵒᵖ from s).unop)
    · exact congrArg (rightIndRegularInvLinear φ) (rightIndRegularHom_mk φ s r)
    rw [rightIndRegularInvLinear_apply]
    trans BalancedTensor.mk (k := k) (R := Rᵐᵒᵖ) (S := Sᵐᵒᵖ)
      (M := AlgebraInduction.Bimod φ.op) (N := RightObj (regular (k := k) (R := R)))
      (MulOpposite.op (MulOpposite.op (show R from r)) • s) (1:R)
    · rfl
    trans BalancedTensor.mk (k := k) (R := Rᵐᵒᵖ) (S := Sᵐᵒᵖ)
      (N := RightObj (regular (k := k) (R := R))) s
      (MulOpposite.op (show R from r) • (show RightObj (regular (k := k) (R := R)) from (1:R)))
    · exact BalancedTensor.balance _ _ _
    change BalancedTensor.mk s (show RightObj (regular (k := k) (R := R)) from (1 * (1 * (show R from r)) : R)) = BalancedTensor.mk s r
    exact congrArg (fun z : R => BalancedTensor.mk s
      (show RightObj (regular (k := k) (R := R)) from z)) (by exact (congrArg (fun z : R => (1:R)*z) (one_mul (show R from r))).trans (one_mul (show R from r)))
  inv_hom_id := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro s
    change (show S from rightIndRegularHom φ (rightIndRegularInvLinear φ (show S from s))) =
      (show S from s)
    trans (show S from rightIndRegularHom φ (BalancedTensor.mk
      (show AlgebraInduction.Bimod φ.op from MulOpposite.op (show S from s))
      (show RightObj (regular (k := k) (R := R)) from (1:R))))
    · exact congrArg (fun x : RightIndType φ (regular (k := k) (R := R)) =>
        (show S from rightIndRegularHom φ x)) (rightIndRegularInvLinear_apply φ s)
    exact (rightIndRegularHom_mk φ _ _).trans
      (show φ (1:R) * (show S from s) = (show S from s) by rw [map_one, one_mul])

def leftRestrictedRegularIso (φ : R →ₐ[k] S) :
    (leftFunctor (k := k) (R := R) (S := S)).obj (leftRestrictedRegular φ) ≅
      (AlgebraInduction.res φ).obj (ModuleCat.of S S) :=
by
  let X := (leftFunctor (k := k) (R := R) (S := S)).obj (leftRestrictedRegular φ)
  let Z := (AlgebraInduction.res φ).obj (ModuleCat.of S S)
  exact LinearEquiv.toModuleIso (X₁ := X) (X₂ := Z)
    (m₁ := X.isModule) (m₂ := Z.isModule)
    { toFun := fun x : X =>
        (show (AlgebraInduction.res φ).obj (ModuleCat.of S S) from x)
      invFun := fun x => x
      left_inv _ := rfl
      right_inv _ := rfl
      map_add' _ _ := rfl
      map_smul' r x := by
        change φ r * ((show S from x) * 1) = φ r * (show S from x)
        rw [mul_one] }

end Tachikawa.Enveloping



namespace Tachikawa.Enveloping
open CategoryTheory
open scoped TensorProduct ModuleCat.Algebra
variable {k R S U : Type} [Field k] [Ring R] [Ring S] [Ring U]
  [Algebra k R] [Algebra k S] [Algebra k U]




lemma leftInd_hom_ext (φ : R →ₐ[k] S) {M : ModuleCat (Alg k R U)} {N : ModuleCat (Alg k S U)}
    {f g : leftIndObj φ M ⟶ N}
    (h : ∀ (s : AlgebraInduction.Bimod φ) (m : Obj M),
      f (BalancedTensor.mk s m) = g (BalancedTensor.mk s m)) : f = g := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  induction x using BalancedTensor.induction_on (k := k) (R := R) (S := S)
    (M := AlgebraInduction.Bimod φ) (N := Obj M) with
  | h0 => exact f.hom.map_zero.trans g.hom.map_zero.symm
  | ht s m => exact h s m
  | ha x y hx hy =>
    exact (f.hom.map_add x y).trans
      ((congrArg₂ (fun x y => x+y) hx hy).trans (g.hom.map_add x y).symm)

def leftIndComparisonHom (φ : R →ₐ[k] S) (M : ModuleCat (Alg k R U)) :
    (AlgebraInduction.functor (leftEnvelopingMap (U := U) φ)).obj M ⟶ leftIndObj φ M :=
  AlgebraInduction.extend (k := k) (R := Alg k R U) (S := Alg k S U)
    (N := M) (P := leftIndObj φ M) (leftEnvelopingMap φ) (leftIndUnit φ M)

def leftIndComparisonInv (φ : R →ₐ[k] S) (M : ModuleCat (Alg k R U)) :
    leftIndObj φ M ⟶ (AlgebraInduction.functor (leftEnvelopingMap (U := U) φ)).obj M :=
  leftIndExtend (k := k) (R := R) (S := S) (U := U) φ (M := M)
    (N := (AlgebraInduction.functor (leftEnvelopingMap (U := U) φ)).obj M)
    (AlgebraInduction.unit (k := k) (R := Alg k R U) (S := Alg k S U)
      (leftEnvelopingMap (U := U) φ) M)

lemma leftIndComparison_inv_unit (φ : R →ₐ[k] S) (M : ModuleCat (Alg k R U)) (m : M) :
    leftIndComparisonInv φ M (leftIndUnit φ M m) =
      AlgebraInduction.unit (k := k) (R := Alg k R U) (S := Alg k S U) (leftEnvelopingMap φ) M m := by
  change (1:S) • (show Obj ((AlgebraInduction.functor (k := k) (leftEnvelopingMap (U := U) φ)).obj M) from
    AlgebraInduction.unit (k := k) (leftEnvelopingMap (U := U) φ) M m) = _
  exact one_smul _ _

lemma leftIndComparison_hom_unit (φ : R →ₐ[k] S) (M : ModuleCat (Alg k R U)) (m : M) :
    leftIndComparisonHom φ M (AlgebraInduction.unit (k := k) (R := Alg k R U)
      (S := Alg k S U) (leftEnvelopingMap φ) M m) = leftIndUnit φ M m := by
  change (1:Alg k S U) • (show leftIndObj φ M from leftIndUnit φ M m) = _
  exact one_smul _ _

lemma leftIndComparison_hom_inv (φ : R →ₐ[k] S) (M : ModuleCat (Alg k R U)) :
    leftIndComparisonHom φ M ≫ leftIndComparisonInv φ M = 𝟙 _ := by
  apply (AlgebraInduction.homEquiv (k := k) (R := Alg k R U) (S := Alg k S U)
    (leftEnvelopingMap φ) M _).injective
  ext m
  change leftIndComparisonInv φ M (leftIndComparisonHom φ M
    (AlgebraInduction.unit (k := k) (leftEnvelopingMap (U := U) φ) M m)) =
      AlgebraInduction.unit (k := k) (leftEnvelopingMap (U := U) φ) M m
  rw [leftIndComparison_hom_unit, leftIndComparison_inv_unit]

lemma leftIndComparison_inv_hom (φ : R →ₐ[k] S) (M : ModuleCat (Alg k R U)) :
    leftIndComparisonInv φ M ≫ leftIndComparisonHom φ M = 𝟙 _ := by
  apply leftInd_hom_ext φ
  intro s m
  have h := (leftMap (leftIndComparisonHom φ M)).map_smul (show S from s)
    (show Obj ((AlgebraInduction.functor (k := k) (leftEnvelopingMap (U := U) φ)).obj M) from
      AlgebraInduction.unit (k := k) (leftEnvelopingMap (U := U) φ) M m)
  change leftIndComparisonHom φ M ((show S from s) •
    (show Obj ((AlgebraInduction.functor (k := k) (leftEnvelopingMap (U := U) φ)).obj M) from
      AlgebraInduction.unit (k := k) (leftEnvelopingMap (U := U) φ) M m)) = _
  apply h.trans
  apply Eq.trans (congrArg (fun x : Obj (leftIndObj φ M) => (show S from s) • x)
    (leftIndComparison_hom_unit φ M m))
  change (show S from s) • ((1:Uᵐᵒᵖ) •
    (BalancedTensor.mk (k := k) (R := R) (S := S)
      (M := AlgebraInduction.Bimod φ) (N := Obj M) (show AlgebraInduction.Bimod φ from (1:S)) m)) = BalancedTensor.mk s m
  rw [one_smul]
  exact (AlgebraInduction.mk_one_smul φ (ModuleCat.of R (Obj M)) (show S from s) m).symm

def leftIndComparisonIso (φ : R →ₐ[k] S) (M : ModuleCat (Alg k R U)) :
    (AlgebraInduction.functor (leftEnvelopingMap (U := U) φ)).obj M ≅ leftIndObj φ M where
  hom := leftIndComparisonHom φ M
  inv := leftIndComparisonInv φ M
  hom_inv_id := leftIndComparison_hom_inv φ M
  inv_hom_id := leftIndComparison_inv_hom φ M

def leftIndComparison (φ : R →ₐ[k] S) :
    AlgebraInduction.functor (leftEnvelopingMap (U := U) φ) ≅ leftIndFunctor φ :=
  NatIso.ofComponents (leftIndComparisonIso φ) (by
    intro M N f
    apply ModuleCat.hom_ext
    apply BalancedTensor.hom_ext
    intro a m
    change (show Alg k S U from a) • (show leftIndObj φ N from leftIndUnit φ N (f m)) =
      leftIndMap φ f ((show Alg k S U from a) • (show leftIndObj φ M from leftIndUnit φ M m))
    exact ((leftIndMap φ f).hom.map_smul (show Alg k S U from a)
      (show leftIndObj φ M from leftIndUnit φ M m)).symm)

def leftIndUnderlyingComparison (φ : R →ₐ[k] S) :
    leftIndFunctor (U := U) φ ⋙ leftFunctor ≅ leftFunctor ⋙ AlgebraInduction.functor φ :=
  NatIso.ofComponents (leftIndUnderlyingIso φ) (by intro M N f; ext x; rfl)

end Tachikawa.Enveloping



namespace Tachikawa.Enveloping
open CategoryTheory
open scoped ModuleCat.Algebra
variable {k R S : Type} [Field k] [Ring R] [Ring S] [Algebra k R] [Algebra k S]

abbrev leftComplex (P : ChainComplex (ModuleCat (Alg k R S)) ℕ) :=
  ((leftFunctor (k := k) (R := R) (S := S)).mapHomologicalComplex (.down ℕ)).obj P

def leftCokerEquiv (P : ChainComplex (ModuleCat (Alg k R S)) ℕ) (n : ℕ) :
    Obj (ModuleCat.of (Alg k R S) (NatCoker.C P n)) ≃ₗ[R] NatCoker.C (leftComplex P) n where
  toFun := id
  invFun := id
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

lemma coker_left_projective_of_homotopy (P : ChainComplex (ModuleCat (Alg k R S)) ℕ)
    (Q : ChainComplex (ModuleCat R) ℕ) (n : ℕ) (e : HomotopyEquiv (leftComplex P) Q)
    [Subsingleton (Q.X (n+1))] [Module.Projective R (Obj (P.X n))] :
    Module.Projective R (Obj (ModuleCat.of (Alg k R S) (NatCoker.C P n))) := by
  let : Module.Projective R ((leftComplex P).X n) :=
    inferInstanceAs (Module.Projective R (Obj (P.X n)))
  let := NatCoker.projective_of_homotopy (leftComplex P) n e
  exact Module.Projective.of_equiv (leftCokerEquiv P n).symm

end Tachikawa.Enveloping



namespace Tachikawa.Enveloping
open CategoryTheory HomologicalComplex
open scoped TensorProduct ModuleCat.Algebra
variable {k R S : Type} [Field k] [Ring R] [Ring S] [Algebra k R] [Algebra k S]
  [FiniteDimensional k R] [FiniteDimensional k S]

def inducedFactorIso (φ : R →ₐ[k] S) :
    AlgebraInduction.functor (rightEnvelopingMap (U := R) φ) ⋙
      AlgebraInduction.functor (leftEnvelopingMap (U := S) φ) ≅
      AlgebraInduction.functor (envelopingMap φ) :=
  AlgebraInduction.compositionIso _ _ ≪≫ eqToIso (by
    congr 1
    ext a <;> rfl)

end Tachikawa.Enveloping



end

end OAI
end

section
-- module Solutions.OAIQ116_Tach.Tachikawa_DerivedInduction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
set_option backward.isDefEq.respectTransparency false


noncomputable section
namespace Tachikawa.Construction
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct ModuleCat.Algebra
variable {k : Type} [Field k] [CharP k 2] (q : k) (hq : q ≠ 0)

abbrev Y : FiniteModule k (Enveloping.Alg k (E q) (E q)) :=
  Enveloping.inducedY (inclusionB q) (formE q)

end Tachikawa.Construction



namespace Tachikawa.TrivialInduction
open CategoryTheory
open scoped ModuleCat.Algebra
variable {k R : Type} [Field k] [Ring R] [Algebra k R]

def tensorPure (M : ModuleCat.{0} R) :
    AlgebraInduction.Bimod (inclusion (k := k) (R := R)) →ₗ[TrivialExtension k R]
      M →ₗ[k] BalancedTensor.T (k := k) (R := R) (S := TrivialExtension k R)
        (M := AlgebraInduction.Bimod (inclusion (k := k) (R := R))) (N := M) :=
  BalancedTensor.mk

lemma tensorPure_inr_smul (M : ModuleCat.{0} R) (r : R) (φ : DualBimodule k R) (m : M) :
    tensorPure (k := k) M
      (show AlgebraInduction.Bimod (inclusion (k := k) (R := R)) from
        (TrivSqZeroExt.inr (r • φ) : TrivialExtension k R)) m =
    (TrivSqZeroExt.inl r : TrivialExtension k R) • tensorPure (k := k) M
      (show AlgebraInduction.Bimod (inclusion (k := k) (R := R)) from
        (TrivSqZeroExt.inr φ : TrivialExtension k R)) m := by
  have h := LinearMap.congr_fun ((tensorPure (k := k) M).map_smul
    (TrivSqZeroExt.inl r : TrivialExtension k R)
    (show AlgebraInduction.Bimod (inclusion (k := k) (R := R)) from (TrivSqZeroExt.inr φ : TrivialExtension k R))) m
  have hr : (TrivSqZeroExt.inl r : TrivialExtension k R) •
      (show AlgebraInduction.Bimod (inclusion (k := k) (R := R)) from
        (TrivSqZeroExt.inr φ : TrivialExtension k R)) =
      (show AlgebraInduction.Bimod (inclusion (k := k) (R := R)) from
        (TrivSqZeroExt.inr (r • φ) : TrivialExtension k R)) :=
    TrivSqZeroExt.inl_mul_inr r φ
  rw [hr] at h
  exact h

def lowerBilinear (M : ModuleCat.{0} R) : DualBimodule k R →ₗ[R] M →ₗ[k]
    (AlgebraInduction.res (inclusion (k := k) (R := R))).obj ((AlgebraInduction.functor (inclusion (k := k))).obj M) where
  toFun φ :=
    { toFun := fun m => tensorPure (k := k) M (show AlgebraInduction.Bimod (inclusion (k := k) (R := R)) from
        (TrivSqZeroExt.inr φ : TrivialExtension k R)) m
      map_add' := fun x y => (tensorPure (k := k) M _).map_add x y
      map_smul' := by
        intro c x
        change tensorPure (k := k) M _ (c • x) = (algebraMap k (TrivialExtension k R) c) • tensorPure (k := k) M _ x
        rw [IsScalarTower.algebraMap_smul]
        exact (tensorPure (k := k) M _).map_smul c x }
  map_add' φ ψ := by
    apply LinearMap.ext
    intro m
    change tensorPure (k := k) M (show AlgebraInduction.Bimod (inclusion (k := k) (R := R)) from
      (TrivSqZeroExt.inr (φ+ψ) : TrivialExtension k R)) m = _
    rw [TrivSqZeroExt.inr_add]
    exact LinearMap.congr_fun ((tensorPure (k := k) M).map_add _ _) m
  map_smul' r φ := by
    apply LinearMap.ext
    intro m
    exact tensorPure_inr_smul M r φ m

lemma lowerBilinear_balanced (M : ModuleCat.{0} R) (r : R) (φ : DualBimodule k R) (m : M) :
    lowerBilinear (k := k) M (MulOpposite.op r • φ) m = lowerBilinear (k := k) M φ (r • m) := by
  have h := BalancedTensor.balance (k := k) (R := R) (S := TrivialExtension k R)
    r (show AlgebraInduction.Bimod (inclusion (k := k) (R := R)) from (TrivSqZeroExt.inr φ : TrivialExtension k R)) m
  have hr : MulOpposite.op r •
      (show AlgebraInduction.Bimod (inclusion (k := k) (R := R)) from
        (TrivSqZeroExt.inr φ : TrivialExtension k R)) =
      (show AlgebraInduction.Bimod (inclusion (k := k) (R := R)) from
        (TrivSqZeroExt.inr (MulOpposite.op r • φ) : TrivialExtension k R)) :=
    TrivSqZeroExt.inr_mul_inl r φ
  rw [hr] at h
  exact h

def lowerTensor (M : ModuleCat.{0} R) :
    BalancedTensor.T (k := k) (R := R) (S := R) (M := DualBimodule k R) (N := M) →ₗ[R]
    (AlgebraInduction.res (inclusion (k := k) (R := R))).obj ((AlgebraInduction.functor (inclusion (k := k))).obj M) :=
  BalancedTensor.lift (lowerBilinear (k := k) M) (lowerBilinear_balanced M)

variable [FiniteDimensional k R] (M : ModuleCat.{0} R) [FiniteDimensional k M]

omit [FiniteDimensional k R] [FiniteDimensional k M] in
lemma tensorComparison_lower (z : BalancedTensor.T (k := k) (R := R) (S := R)
    (M := DualBimodule k R) (N := M)) :
    tensorComparison (k := k) M (lowerTensor (k := k) M z) = (0, Nakayama.evaluation z) := by
  induction z using BalancedTensor.induction_on with
  | h0 => rfl
  | ht φ m =>
    apply Prod.ext
    · change (0:R) • m = 0
      simp
    · change Nakayama.evaluationBilinear φ m + (0:R) • (0 : Nakayama k R M) = _
      rw [zero_smul, add_zero]
      rfl
  | ha x y hx hy =>
    erw [map_add, map_add, hx, hy, map_add]
    apply Prod.ext
    · exact zero_add _
    · rfl

end Tachikawa.TrivialInduction



namespace Tachikawa.TrivialInduction
open CategoryTheory
open scoped ModuleCat.Algebra
variable {k R : Type} [Field k] [Ring R] [Algebra k R]

lemma tensorComparison_natural {M N : ModuleCat.{0} R} (f : M ⟶ N) :
    (AlgebraInduction.functor (inclusion (k := k) (R := R))).map f ≫
      tensorComparison (k := k) N =
    tensorComparison (k := k) M ≫ (functor (k := k)).map f := by
  apply ModuleCat.hom_ext
  apply BalancedTensor.hom_ext
  intro a m
  change (show TrivialExtension k R from a) • unit (f m) =
    map (k := k) (R := R) f.hom ((show TrivialExtension k R from a) • unit m)
  rw [map_smul, map_unit]

end Tachikawa.TrivialInduction



namespace Tachikawa.C
open CategoryTheory
open scoped ModuleCat.Algebra
variable {k : Type} [Field k] [CharP k 2] (q : k)

omit [CharP k 2] in
lemma resObj_finite_k (n : ℕ) : Module.Finite k (resObj q n) := by
  have hf : Module.Finite (C k q) (resObj q n) := by
    cases n with
    | zero =>
      let : Module.Finite k (Cf q) := Module.Finite.of_injective
        ((Cf q).subtype.restrictScalars k) Subtype.val_injective
      exact Module.Finite.of_restrictScalars_finite k (C k q) (Cf q)
    | succ n =>
      let : Module.Finite k (Ce q) := Module.Finite.of_injective
        ((Ce q).subtype.restrictScalars k) Subtype.val_injective
      exact Module.Finite.of_restrictScalars_finite k (C k q) (Ce q)
  let := hf
  exact Module.Finite.trans (C k q) (resObj q n)

end Tachikawa.C



end

end OAI
end

section
-- module Solutions.OAIQ116_Tach.Tachikawa_StableLift
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section



namespace Tachikawa.Enveloping
open CategoryTheory
open scoped ModuleCat.Algebra
variable {k R S : Type} [Field k] [Ring R] [Ring S] [Algebra k R] [Algebra k S]
  (X : ModuleCat.{0} R) {M N : ModuleCat.{0} (Alg k S R)}

instance eval_finite [FiniteDimensional k M] [FiniteDimensional k X] :
    Module.Finite S (evalObj X M) :=
  Module.Finite.of_restrictScalars_finite k S (evalType X M)

end Tachikawa.Enveloping



end

end OAI
end

section
-- module Solutions.OAIQ116_Tach.Tachikawa_HomProfile
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section



namespace Tachikawa
open CategoryTheory CategoryTheory.Abelian
open scoped ModuleCat.Algebra
variable {k R : Type} [Field k] [Ring R] [Algebra k R]
variable (C : ChainComplex (ModuleCat R) ℤ) (hC : TotallyAcyclic C)
  (fin : ∀ j, Module.Finite R (C.X j)) (proj : ∀ j, Module.Projective R (C.X j))
  (N : ModuleCat R)

namespace CompleteStableExt
abbrev Q := completeResolutionTail C hC.1 proj

end CompleteStableExt
end Tachikawa



end

end OAI
end


