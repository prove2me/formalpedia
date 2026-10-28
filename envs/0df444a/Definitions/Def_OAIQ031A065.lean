-- Prove2me | Definitions.Def_OAIQ031A065
-- name    : OAIQ031A065
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T14:12:40.691953+00:00
-- url     : https://prove2.me/theorems/79434165-3d6f-49cc-b7d4-30a1d2e63c8e
-- title:
--   Definitions bundle OAIQ031A065 of the split of OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.ArExplicit.Statement.main`, carved from OpenAI's openai/math development (OpenAI, *An explicit counterexample to the Auslander-Reiten conjecture (result family 199)*, OpenAI Math Release, September 23, 2026, result family 199, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 59 declarations of OpenAI's Lean: 19 definitions, 3 instances and 37 theorems. The definitions and types are `OAI.ArExplicit.DualTensor.moduleEvaluationEquiv`, `OAI.ArExplicit.ExternalTensor.scalarVertical`, `OAI.ArExplicit.ModuleBar.augmentation`, `OAI.ArExplicit.ModuleBar.complex`, `OAI.ArExplicit.ModuleBar.differential`, `OAI.ArExplicit.ModuleBar.nativeResolution`, `OAI.ArExplicit.ModuleBar.resolution`, `OAI.ArExplicit.Resolution.TSelfExt`, `OAI.ArExplicit.Resolution.evaluateF`, `OAI.ArExplicit.Resolution.fromRightF`, `OAI.ArExplicit.Resolution.idealDualComplex`, `OAI.ArExplicit.Resolution.idealDualDifferential`, `OAI.ArExplicit.Resolution.idealDualObject`, `OAI.ArExplicit.Resolution.leftEll`, `OAI.ArExplicit.Resolution.leftU`, `OAI.ArExplicit.Resolution.tSimpleDerived`, `OAI.ArExplicit.Resolution.tSimpleEndScalarEquiv`, `OAI.ArExplicit.Resolution.tSimpleExtZeroEquiv`, `OAI.ArExplicit.Resolution.tSimpleScalarEnd`.
--
--   **Sources.** They come from these modules of lean/OAI/Algebra, in whole or in part: [`AuslanderReiten_Algebras_SimpleDual`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Algebras/SimpleDual.lean), [`AuslanderReiten_Algebras_TSimpleEnd`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Algebras/TSimpleEnd.lean), [`AuslanderReiten_Bar_ModuleBar`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Bar/ModuleBar.lean), [`AuslanderReiten_Bar_ModuleBarNative`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Bar/ModuleBarNative.lean), [`AuslanderReiten_Duality_DualResolution`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Duality/DualResolution.lean), [`AuslanderReiten_Duality_DualTensorEvaluation`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Duality/DualTensorEvaluation.lean), [`AuslanderReiten_Duality_DualTensorModule`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Duality/DualTensorModule.lean), [`AuslanderReiten_Duality_IdealDualComplex`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Duality/IdealDualComplex.lean), [`AuslanderReiten_Ext_TExtRecurrence`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Ext/TExtRecurrence.lean), [`AuslanderReiten_Modules_TInductionTriangle`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Modules/TInductionTriangle.lean), [`AuslanderReiten_Tensor_ExternalTensorForget`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Tensor/ExternalTensorForget.lean).
--
--   **Imports.** It imports the bundles `OAIQ031A044`, `OAIQ031A046`, `OAIQ031A047`, `OAIQ031A048` and `OAIQ031A049` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ031A078`, `OAIQ031A079`, `OAIQ031A080`, `OAIQ031A081`, `OAIQ031A082`, `OAIQ031A084`, `OAIQ031A085` and `OAIQ031A088`.
-- source:
--   OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 199; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/An-explicit-counterexample-to-the-Auslander-Reiten-conjecture-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algebra at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ031A044
import Definitions.Def_OAIQ031A046
import Definitions.Def_OAIQ031A047
import Definitions.Def_OAIQ031A048
import Definitions.Def_OAIQ031A049

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Algebras_SimpleDual
attribute [-instance] _root_.OAI.ArExplicit.A.instIsTwoSidedAugmentationIdeal _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ArExplicit.Resolution
open ArExplicit.Letter ArExplicit.BaseAlgebra
variable {k : Type*} [Field k] (q : k)

theorem simple_expand (hq : 1 + q ≠ 0) (s : Simple q) :
    s = simpleCoordinate q s • generator q := by
  apply simpleCoordinate_injective q hq
  simp

end ArExplicit.Resolution

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Duality_DualTensorEvaluation
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.EnvelopingBimodule.regular_projective _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.TrivialInduction.dualModule _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ArExplicit
namespace DualTensor

variable {k R V W : Type*} [CommRing k] [Ring R] [Algebra k R]
  [AddCommGroup V] [Module k V] [Module R V] [IsScalarTower k R V]
  [AddCommGroup W] [Module k W] [Module R W] [IsScalarTower k R W]

variable {n : ℕ}

theorem evaluation_inverseUsing (s : V →ₗ[R] (Fin n → R)) (p : (Fin n → R) →ₗ[R] V)
    (h : p.comp s = LinearMap.id) (φ : Module.Dual k (V →ₗ[R] R)) :
    evaluation (inverseUsing s p φ) = φ := by
  ext f
  change evaluation (∑ i, BalancedTensor.tmul
    (Coinduced.mk (φ.comp (coefficientRight s i))) (p (Pi.single i 1))) f = φ f
  simp only [map_sum, LinearMap.sum_apply, evaluation_tmul, LinearMap.comp_apply]
  rw [← map_sum, sum_coefficientRight s p h]

theorem inverseUsing_evaluation (s : V →ₗ[R] (Fin n → R)) (p : (Fin n → R) →ₗ[R] V)
    (h : p.comp s = LinearMap.id) (z : BalancedTensor k R (Coinduced k R) V) :
    inverseUsing s p (evaluation z) = z := by
  induction z using BalancedTensor.induction_on with
  | zero =>
    simp only [inverseUsing, map_zero, LinearMap.zero_comp]
    apply Finset.sum_eq_zero
    intro i hi
    exact BalancedTensor.zero_tmul _
  | add x y hx hy =>
    change (∑ i, BalancedTensor.tmul
      (Coinduced.mk ((evaluation (x + y)).comp (coefficientRight s i))) (p (Pi.single i 1))) = x + y
    have hadd (i : Fin n) : Coinduced.mk ((evaluation (x + y)).comp (coefficientRight s i)) =
        Coinduced.mk ((evaluation x).comp (coefficientRight s i)) +
        Coinduced.mk ((evaluation y).comp (coefficientRight s i)) := by
      ext r
      simp
    simp_rw [hadd, BalancedTensor.add_tmul, Finset.sum_add_distrib]
    exact congrArg₂ (· + ·) hx hy
  | tmul ℓ v =>
    change (∑ i, BalancedTensor.tmul
      (Coinduced.mk ((evaluation (BalancedTensor.tmul ℓ v)).comp (coefficientRight s i)))
        (p (Pi.single i 1))) = BalancedTensor.tmul ℓ v
    have hc (i : Fin n) :
        Coinduced.mk ((evaluation (BalancedTensor.tmul ℓ v)).comp (coefficientRight s i)) =
          MulOpposite.op (s v i) • ℓ := by
      ext r
      rfl
    simp_rw [hc, BalancedTensor.balance]
    change (∑ i, (BalancedTensor.mk (k := k) (R := R) ℓ) (s v i • p (Pi.single i 1))) =
      (BalancedTensor.mk (k := k) (R := R) ℓ) v
    rw [← map_sum, sum_coefficients s p h]

theorem evaluation_bijective [Module.Finite R V] [Module.Projective R V] :
    Function.Bijective (evaluation (k := k) (R := R) (V := V)) := by
  obtain ⟨n, p, hp⟩ := Module.Finite.exists_fin' R V
  obtain ⟨s, hs⟩ := Module.projective_lifting_property p (LinearMap.id : V →ₗ[R] V) hp
  exact ⟨Function.LeftInverse.injective (inverseUsing_evaluation s p hs),
    Function.RightInverse.surjective (evaluation_inverseUsing s p hs)⟩

theorem evaluation_natural (a : V →ₗ[R] W)
    (z : BalancedTensor k R (Coinduced k R) V) (f : W →ₗ[R] R) :
    evaluation (BalancedTensor.mapRight (S := k) a z) f = evaluation z (f.comp a) := by
  induction z using BalancedTensor.induction_on with
  | zero => simp
  | tmul ℓ v => rfl
  | add x y hx hy => simp only [map_add, LinearMap.add_apply, hx, hy]

end DualTensor
end ArExplicit

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Duality_DualTensorModule
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.EnvelopingBimodule.regular_projective _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.TrivialInduction.dualModule _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ArExplicit.DualTensor
variable {k R V W : Type*} [CommRing k] [Ring R] [Algebra k R]
variable [AddCommGroup V] [Module k V] [Module R V] [IsScalarTower k R V]
variable [AddCommGroup W] [Module k W] [Module R W] [IsScalarTower k R W]

def moduleEvaluationEquiv [Module.Finite R V] [Module.Projective R V] :
    BalancedTensor k R (Coinduced k R) V ≃ₗ[R] RightDual k R (V →ₗ[R] R) :=
  LinearEquiv.ofBijective moduleEvaluation
    ((RightDual.scalarEquiv (k := k) (R := R)).symm.bijective.comp evaluation_bijective)

end ArExplicit.DualTensor

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Duality_DualResolution
attribute [-instance] _root_.OAI.ArExplicit.A.instIsTwoSidedAugmentationIdeal _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.Resolution.instIsScalarTowerTSimple _root_.OAI.ArExplicit.Resolution.instModuleTSimple _root_.OAI.ArExplicit.Resolution.simpleRightAction _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ArExplicit.Resolution

open ArExplicit.Letter ArExplicit.BaseAlgebra

variable {k : Type*} [Field k] (q : k)

local notation "C" => BaseAlgebra k q

@[simp] theorem fromRightE_evaluateE (g : E q →ₗ[C] C) : fromRightE q (evaluateE q g) = g := by
  apply LinearMap.ext
  intro a
  change (a : C) • g (vertexE q) = g a
  rw [← g.map_smul, smul_vertexE]

theorem rightE_coeff_zero (a : rightE q) (i : Letter)
    (hi : i = t ∨ i = j ∨ i = f ∨ i = n) : (a : C).coeff i = 0 := by
  have h := congrArg (fun b : C => b.coeff i) a.property
  rcases hi with rfl | rfl | rfl | rfl <;> simpa [product] using h.symm

@[simp] theorem rightE_coeff_t (a : rightE q) : (a : C).coeff t = 0 :=
  rightE_coeff_zero q a t (by simp)
@[simp] theorem rightE_coeff_j (a : rightE q) : (a : C).coeff j = 0 :=
  rightE_coeff_zero q a j (by simp)
@[simp] theorem rightE_coeff_f (a : rightE q) : (a : C).coeff f = 0 :=
  rightE_coeff_zero q a f (by simp)
@[simp] theorem rightE_coeff_n (a : rightE q) : (a : C).coeff n = 0 :=
  rightE_coeff_zero q a n (by simp)

def leftEll (r : k) : rightE q →ₗ[Cᵐᵒᵖ] rightE q where
  toFun a := ⟨ell q r * a, by
    change basisVector q e * (ell q r * a) = ell q r * a
    rw [← mul_assoc]
    congr 1
    ext i
    cases i <;> simp [ell, product]⟩
  map_add' a b := Subtype.ext (mul_add (ell q r) a b)
  map_smul' c a := Subtype.ext (mul_assoc (ell q r) a (MulOpposite.unop c)).symm

@[simp] theorem coe_leftEll (r : k) (a : rightE q) :
    (leftEll q r a : C) = ell q r * a := rfl

theorem smul_vertexF (a : F q) : (a : C) • vertexF q = a := by
  apply Subtype.ext
  exact a.property

def evaluateF (g : F q →ₗ[C] C) : rightF q := ⟨g (vertexF q), by
  change basisVector q f • g (vertexF q) = g (vertexF q)
  rw [← g.map_smul]
  congr 1
  exact smul_vertexF q (vertexF q)⟩

def fromRightF (a : rightF q) : F q →ₗ[C] C where
  toFun b := (b : C) * a
  map_add' b c := add_mul (b : C) c a
  map_smul' c b := mul_assoc c (b : C) a

@[simp] theorem evaluateF_fromRightF (a : rightF q) : evaluateF q (fromRightF q a) = a := by
  apply Subtype.ext
  exact a.property

@[simp] theorem fromRightF_evaluateF (g : F q →ₗ[C] C) : fromRightF q (evaluateF q g) = g := by
  apply LinearMap.ext
  intro a
  change (a : C) • g (vertexF q) = g a
  rw [← g.map_smul, smul_vertexF]

theorem rightF_coeff_zero (a : rightF q) (i : Letter)
    (hi : i = e ∨ i = x ∨ i = y ∨ i = z ∨ i = u ∨ i = v) : (a : C).coeff i = 0 := by
  have h := congrArg (fun b : C => b.coeff i) a.property
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;> simpa [product] using h.symm

@[simp] theorem rightF_coeff_e (a : rightF q) : (a : C).coeff e = 0 :=
  rightF_coeff_zero q a e (by simp)
@[simp] theorem rightF_coeff_x (a : rightF q) : (a : C).coeff x = 0 :=
  rightF_coeff_zero q a x (by simp)
@[simp] theorem rightF_coeff_y (a : rightF q) : (a : C).coeff y = 0 :=
  rightF_coeff_zero q a y (by simp)
@[simp] theorem rightF_coeff_z (a : rightF q) : (a : C).coeff z = 0 :=
  rightF_coeff_zero q a z (by simp)
@[simp] theorem rightF_coeff_u (a : rightF q) : (a : C).coeff u = 0 :=
  rightF_coeff_zero q a u (by simp)
@[simp] theorem rightF_coeff_v (a : rightF q) : (a : C).coeff v = 0 :=
  rightF_coeff_zero q a v (by simp)

def leftU : rightF q →ₗ[Cᵐᵒᵖ] rightE q where
  toFun a := ⟨basisVector q u * a, by
    change basisVector q e * (basisVector q u * a) = basisVector q u * a
    rw [← mul_assoc, basis_mul]
    simp [multiplicationTable]⟩
  map_add' a b := Subtype.ext (mul_add (basisVector q u) a b)
  map_smul' c a := Subtype.ext (mul_assoc (basisVector q u) a (MulOpposite.unop c)).symm

@[simp] theorem coe_leftU (a : rightF q) : (leftU q a : C) = basisVector q u * a := rfl

end ArExplicit.Resolution

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Duality_IdealDualComplex
attribute [-instance] _root_.OAI.ArExplicit.A.instIsTwoSidedAugmentationIdeal _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory
namespace ArExplicit.Resolution
open ArExplicit.Letter ArExplicit.BaseAlgebra
universe u
variable {k : Type u} [Field k] [CharP k 2] (q : k)
local notation "C" => BaseAlgebra k q

def idealDualObject : ℕ → ModuleCat C
  | 0 => ModuleCat.of C (RightDual k C (rightF q))
  | _ + 1 => ModuleCat.of C (RightDual k C (rightE q))

def idealDualDifferential : (n : ℕ) → idealDualObject q (n + 1) ⟶ idealDualObject q n
  | 0 => ModuleCat.ofHom (RightDual.map (k := k) (leftU q))
  | m + 1 => ModuleCat.ofHom (RightDual.map (k := k) (leftEll q (q ^ m)))

theorem idealDualDifferential_comp (n : ℕ) :
    idealDualDifferential q (n + 1) ≫ idealDualDifferential q n = 0 := by
  apply ModuleCat.hom_ext
  cases n with
  | zero =>
    apply LinearMap.ext
    intro φ
    apply RightDual.ext
    apply LinearMap.ext
    intro a
    change φ.functional (leftEll q (q ^ 0) (leftU q a)) = 0
    have hz : leftEll q (q ^ 0) (leftU q a) = 0 := by
      apply Subtype.ext
      change ell q (q ^ 0) * (basisVector q u * (a : C)) = 0
      rw [pow_zero, ← mul_assoc, ell_one_mul_u, zero_mul]
    rw [hz, map_zero]
  | succ n =>
    apply LinearMap.ext
    intro φ
    apply RightDual.ext
    apply LinearMap.ext
    intro a
    change φ.functional (leftEll q (q ^ (n + 1)) (leftEll q (q ^ n) a)) = 0
    have hz : leftEll q (q ^ (n + 1)) (leftEll q (q ^ n) a) = 0 := by
      apply Subtype.ext
      change ell q (q ^ (n + 1)) * (ell q (q ^ n) * (a : C)) = 0
      rw [pow_succ', ← mul_assoc, ell_successor_mul, zero_mul]
    rw [hz, map_zero]

def idealDualComplex : ChainComplex (ModuleCat C) ℕ :=
  ChainComplex.of (idealDualObject q) (idealDualDifferential q) (idealDualDifferential_comp q)

end ArExplicit.Resolution

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Algebras_TSimpleEnd
attribute [-instance] _root_.OAI.ArExplicit.A.instIsTwoSidedAugmentationIdeal _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory
open scoped ModuleCat
namespace ArExplicit.Resolution
universe u
variable {k : Type u} [Field k] (q : k)
local notation "T" => ArExplicit.T k q
local notation "S" => ModuleCat.of T (Simple q)

def tSimpleScalarEnd : k →ₗ[k] (S ⟶ S) :=
  LinearMap.toSpanSingleton k (S ⟶ S) (𝟙 S)

theorem tSimpleEnd_eq_scalar (hq1 : 1 + q ≠ 0) (f : S ⟶ S) :
    f = tSimpleScalarEnd q (simpleCoordinate q (f (generator q))) := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change f.hom x = simpleCoordinate q (f.hom (generator q)) • x
  rw [simple_expand q hq1 x, LinearMap.map_smul_of_tower]
  rw [simple_expand q hq1 (f.hom (generator q)), smul_smul, smul_smul, mul_comm]
  simp

theorem tSimpleScalarEnd_bijective (hq1 : 1 + q ≠ 0) :
    Function.Bijective (tSimpleScalarEnd q) := by
  constructor
  · intro a b hab
    have hh := congrArg (fun f : S ⟶ S => simpleCoordinate q (f (generator q))) hab
    change simpleCoordinate q (a • generator q) = simpleCoordinate q (b • generator q) at hh
    simpa using hh
  · intro f
    exact ⟨simpleCoordinate q (f (generator q)), (tSimpleEnd_eq_scalar q hq1 f).symm⟩

def tSimpleEndScalarEquiv (hq1 : 1 + q ≠ 0) : k ≃ₗ[k] (S ⟶ S) :=
  LinearEquiv.ofBijective (tSimpleScalarEnd q) (tSimpleScalarEnd_bijective q hq1)

def tSimpleExtZeroEquiv (hq1 : 1 + q ≠ 0) : k ≃ₗ[k] Abelian.Ext S S 0 where
  toEquiv := (tSimpleEndScalarEquiv q hq1).toEquiv.trans Abelian.Ext.homEquiv₀.symm
  map_add' a b := by
    change Abelian.Ext.mk₀ (tSimpleScalarEnd q (a + b)) =
      Abelian.Ext.mk₀ (tSimpleScalarEnd q a) + Abelian.Ext.mk₀ (tSimpleScalarEnd q b)
    rw [map_add, Abelian.Ext.mk₀_add]
  map_smul' a b := by
    change Abelian.Ext.mk₀ (tSimpleScalarEnd q (a * b)) = a • Abelian.Ext.mk₀ (tSimpleScalarEnd q b)
    rw [← Abelian.Ext.mk₀_smul]
    congr 1
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change (a * b) • x = (algebraMap k T a) • (b • x)
    rw [IsScalarTower.algebraMap_smul]
    exact mul_smul a b x

@[simp] theorem tSimpleExtZeroEquiv_one (hq1 : 1 + q ≠ 0) :
    tSimpleExtZeroEquiv q hq1 1 = Abelian.Ext.mk₀ (𝟙 S) := by
  change Abelian.Ext.mk₀ (tSimpleScalarEnd q 1) = _
  congr 1
  exact one_smul k (𝟙 S)

end ArExplicit.Resolution

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Bar_ModuleBar
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
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

instance baseModule (n : ℕ) : Module k (moduleObject k R M n) := (object k R M n).isModule
instance moduleTower (n : ℕ) : IsScalarTower k R (moduleObject k R M n) :=
  IsScalarTower.of_algebraMap_smul (A := R) fun a x => by
    change left k R M n (algebraMap k R a) x = a • x
    rw [AlgHom.commutes]
    rfl

def differential (n : ℕ) : moduleObject k R M (n + 1) →ₗ[R] moduleObject k R M n where
  toAddHom := (boundary k R M n).toAddHom
  map_smul' a x := boundary_left k R M n a x

theorem free (n : ℕ) : Module.Free R (moduleObject k R M (n + 1)) := by
  change @Module.Free R (R ⊗[k] object k R M n) _ _ (leftModule k R M (n + 1))
  have hm : leftModule k R M (n + 1) =
      (inferInstance : Module R (R ⊗[k] object k R M n)) := by
    apply Module.ext'
    intro a x
    change left k R M (n + 1) a x = a • x
    induction x using OAI.tensorInductionOn with
    | add x y hx hy => simp only [map_add, smul_add, hx, hy]
    | tmul b x => rfl
  rw [hm]
  infer_instance

theorem finite [Module.Finite k R] [Module.Finite k M] (n : ℕ) :
    Module.Finite R (moduleObject k R M (n + 1)) := by
  let : Module.Finite k (moduleObject k R M (n + 1)) := finiteBase k R M (n + 1)
  exact Module.Finite.of_restrictScalars_finite k R _

variable [CharP k 2]

theorem boundary_squared (n : ℕ) (x : object k R M (n + 2)) :
    boundary k R M n (boundary k R M (n + 1) x) = 0 := by
  induction n with
  | zero =>
    induction x using OAI.tensorInductionOn with
    | add x y hx hy => simp only [map_add, hx, hy, add_zero]
    | tmul a x =>
      rw [boundary_succ_tmul, map_add, boundary_left, boundary_zero_tmul, left_zero]
      exact double_zero_p0 k _
  | succ n ih =>
    induction x using OAI.tensorInductionOn with
    | add x y hx hy => simp only [map_add, hx, hy, add_zero]
    | tmul a x =>
      rw [boundary_succ_tmul, map_add, boundary_left, boundary_succ_tmul, ih,
        TensorProduct.tmul_zero, add_zero]
      exact double_zero_p0 k _

theorem contraction_identity (n : ℕ) (x : object k R M (n + 1)) :
    boundary k R M (n + 1) (contraction k R M (n + 1) x) +
      contraction k R M n (boundary k R M n x) = x := by
  change boundary k R M (n + 1) ((1 : R) ⊗ₜ[k] x) +
    (1 : R) ⊗ₜ[k] boundary k R M n x = x
  rw [boundary_succ_tmul, left_one, add_assoc, double_zero_p0 k, add_zero]

omit [CharP k 2] in
theorem augmentation_contraction (x : M) : boundary k R M 0 (contraction k R M 0 x) = x :=
  one_smul R x

theorem differential_exact (n : ℕ) :
    LinearMap.range (differential k R M (n + 1)) = LinearMap.ker (differential k R M n) := by
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩
    exact boundary_squared k R M n x
  · intro x hx
    refine ⟨contraction k R M (n + 1) x, ?_⟩
    have h := contraction_identity k R M n x
    change boundary k R M n x = 0 at hx
    rw [hx, map_zero, add_zero] at h
    exact h

def complex : ChainComplex (ModuleCat.{u} R) ℕ :=
  ChainComplex.of (fun n => moduleObject k R M (n + 1))
    (fun n => ModuleCat.ofHom (X := moduleObject k R M (n + 2))
      (Y := moduleObject k R M (n + 1)) (differential k R M (n + 1)))
    (fun n => by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      exact boundary_squared k R M (n + 1))

@[simp] theorem complex_d (n : ℕ) : (complex k R M).d (n + 1) n =
    ModuleCat.ofHom (X := moduleObject k R M (n + 2))
      (Y := moduleObject k R M (n + 1)) (differential k R M (n + 1)) := by
  simp only [complex, ChainComplex.of.d]
  apply Category.id_comp

def augmentation : complex k R M ⟶
    (ChainComplex.single₀ (ModuleCat.{u} R)).obj (moduleObject k R M 0) :=
  (ChainComplex.toSingle₀Equiv _ _).symm
    ⟨ModuleCat.ofHom (X := moduleObject k R M 1) (Y := moduleObject k R M 0)
      (differential k R M 0), by
      rw [complex_d]
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      exact boundary_squared k R M 0⟩

@[simp] theorem augmentation_zero : (augmentation k R M).f 0 =
    ModuleCat.ofHom (X := moduleObject k R M 1) (Y := moduleObject k R M 0)
      (differential k R M 0) := ChainComplex.toSingle₀Equiv_symm_apply_f_zero _ _

theorem complex_exactAt (n : ℕ) : (complex k R M).ExactAt (n + 1) := by
  rw [HomologicalComplex.exactAt_iff' _ (n + 2) (n + 1) n (by simp) (by simp)]
  rw [ShortComplex.moduleCat_exact_iff_range_eq_ker]
  change LinearMap.range ((complex k R M).d (n + 1 + 1) (n + 1)).hom =
    LinearMap.ker ((complex k R M).d (n + 1) n).hom
  rw [complex_d, complex_d]
  exact differential_exact k R M (n + 1)

def resolution : ProjectiveResolution (moduleObject k R M 0) where
  complex := complex k R M
  projective n := by
    let := free k R M n
    let : Module.Projective R (moduleObject k R M (n + 1)) := Module.Projective.of_free
    exact (moduleObject k R M (n + 1)).projective_of_categoryTheory_projective
  π := augmentation k R M
  quasiIso := ⟨fun n => by
    cases n with
    | zero =>
      rw [ChainComplex.quasiIsoAt₀_iff, ShortComplex.quasiIso_iff_of_zeros']
      · constructor
        · rw [ShortComplex.moduleCat_exact_iff_range_eq_ker]
          change LinearMap.range ((complex k R M).d 1 0).hom =
            LinearMap.ker ((augmentation k R M).f 0).hom
          rw [complex_d, augmentation_zero]
          exact differential_exact k R M 0
        · rw [ModuleCat.epi_iff_surjective]
          intro x
          exact ⟨contraction k R M 0 x, augmentation_contraction k R M x⟩
      · exact (complex k R M).shape 0 0 (by simp)
      · rfl
      · rfl
    | succ n =>
      rw [quasiIsoAt_iff_exactAt']
      · exact complex_exactAt k R M n
      · exact ChainComplex.exactAt_succ_single_obj _ _⟩

end ArExplicit.ModuleBar

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Bar_ModuleBarNative
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Abelian
open CochainComplex CochainComplex.HomComplex
namespace ArExplicit.ModuleBar
universe u
variable (k R M : Type u) [Field k] [Ring R] [Algebra k R]
  [AddCommGroup M] [Module R M] [Module k M] [IsScalarTower k R M] [CharP k 2]

def nativeResolution : ProjectiveResolution (ModuleCat.of R M) := resolution k R M

instance nativeResolution_finite [Module.Finite k R] [Module.Finite k M] (n : ℕ) :
    Module.Finite R ((nativeResolution k R M).complex.X n) := finite k R M n

end ArExplicit.ModuleBar

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Modules_TInductionTriangle
attribute [-instance] _root_.OAI.ArExplicit.A.instIsTwoSidedAugmentationIdeal _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
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

variable [HasDerivedCategory (ModuleCat.{u} (ArExplicit.T k q))]

def tSimpleDerived : DerivedCategory (ModuleCat T) :=
  (DerivedCategory.singleFunctor (ModuleCat T) 0).obj (ModuleCat.of T (Simple q))

end ArExplicit.Resolution

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Ext_TExtRecurrence
attribute [-instance] _root_.OAI.ArExplicit.A.instIsTwoSidedAugmentationIdeal _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
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
variable [hD : HasDerivedCategory (ModuleCat.{u} (ArExplicit.T k q))]
include hD

abbrev TSelfExt (n : ℕ) := Abelian.Ext (ModuleCat.of T (Simple q)) (ModuleCat.of T (Simple q)) n

end ArExplicit.Resolution

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Tensor_ExternalTensorForget
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ExternalTensor.hasHomCochainTotal _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
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

abbrev scalarVertical (i j n : ℕ) :=
  mapBifunctor.d₂ (forgetComplex k A P) (forgetComplex k B Q)
    (MonoidalCategory.curriedTensor (ModuleCat.{u} k)) (ComplexShape.down ℕ) i j n

theorem scalarVertical_comp (i j n : ℕ) (h : i+j=n+1) :
    scalarVertical k A B P Q i j n ≫ (forgetTermIso k A B P Q n).inv =
      ModuleCat.ofHom ((vertical k A B P Q i j n).hom.restrictScalars k) := by
  cases j with
  | zero =>
    rw [show scalarVertical k A B P Q i 0 n = 0 from
      mapBifunctor.d₂_eq_zero _ _ _ _ i 0 n (by change ¬ ((ComplexShape.down ℕ).next 0 + 1 = 0); omega),
      zero_comp, vertical_zero]
    rfl
  | succ j =>
    have hij : i+j=n := by omega
    dsimp only [scalarVertical]
    rw [mapBifunctor.d₂_eq _ _ _ _ i (show (ComplexShape.down ℕ).Rel (j+1) j from rfl) n hij]
    change ((-1 : ℤˣ)^i • _) ≫ _ = _
    rw [Linear.units_smul_comp, Category.assoc, scalarInclusion_forgetTermIso_inv,
      vertical_succ k A B P Q i j n hij]
    apply ModuleCat.hom_ext
    apply TensorProduct.ext
    apply LinearMap.ext
    intro x
    apply LinearMap.ext
    intro y
    rfl

end ArExplicit.ExternalTensor

end

end OAI
end


