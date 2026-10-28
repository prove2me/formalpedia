-- Prove2me | Definitions.Def_OAIQ031A032
-- name    : OAIQ031A032
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T13:59:01.516458+00:00
-- url     : https://prove2.me/theorems/4fb08562-e00b-4caf-b4ff-d92f1ad0a3f9
-- title:
--   Definitions bundle OAIQ031A032 of the split of OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.ArExplicit.Statement.main`, carved from OpenAI's openai/math development (OpenAI, *An explicit counterexample to the Auslander-Reiten conjecture (result family 199)*, OpenAI Math Release, September 23, 2026, result family 199, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 42 declarations of OpenAI's Lean: 13 definitions, 13 instances and 16 theorems. The definitions and types are `OAI.ArExplicit.DualTensor.formula`, `OAI.ArExplicit.ExternalTensor.canonicalTensorObject`, `OAI.ArExplicit.InductionBimodule.coordinates`, `OAI.ArExplicit.Resolution.fixedLeft`, `OAI.ArExplicit.Resolution.fromRightE`, `OAI.ArExplicit.Resolution.generator`, `OAI.ArExplicit.Resolution.rightE`, `OAI.ArExplicit.Resolution.rightF`, `OAI.ArExplicit.ResolutionProducts.natCubicCocycle`, `OAI.ArExplicit.TrivialInduction.Middle`, `OAI.ArExplicit.TrivialInduction.Quotient`, `OAI.ArExplicit.TrivialInduction.inclusion`, `OAI.ArExplicit.TrivialInduction.projection`.
--
--   **Sources.** They come from these modules of lean/OAI/Algebra, in whole or in part: [`AuslanderReiten_Algebras_SimpleDual`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Algebras/SimpleDual.lean), [`AuslanderReiten_Duality_DualResolution`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Duality/DualResolution.lean), [`AuslanderReiten_Duality_DualTensorEvaluation`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Duality/DualTensorEvaluation.lean), [`AuslanderReiten_Homology_VectorTensorKunneth`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Homology/VectorTensorKunneth.lean), [`AuslanderReiten_Modules_Coinduced`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Modules/Coinduced.lean), [`AuslanderReiten_Modules_CoinducedBimodule`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Modules/CoinducedBimodule.lean), [`AuslanderReiten_Modules_InductionBimodule`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Modules/InductionBimodule.lean), [`AuslanderReiten_Modules_TrivialInduction`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Modules/TrivialInduction.lean), [`AuslanderReiten_Resolutions_NatResolutionCubic`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Resolutions/NatResolutionCubic.lean), [`AuslanderReiten_Resolutions_ResolutionProducts`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Resolutions/ResolutionProducts.lean), [`AuslanderReiten_Tensor_ExternalTensorScalar`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Tensor/ExternalTensorScalar.lean).
--
--   **Imports.** It imports the bundles `OAIQ031A001`, `OAIQ031A003`, `OAIQ031A005`, `OAIQ031A007`, `OAIQ031A008` and `OAIQ031A009` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ031A048`, `OAIQ031A049`, `OAIQ031A050`, `OAIQ031A051`, `OAIQ031A052`, `OAIQ031A056` and `OAIQ031A057`.
-- source:
--   OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 199; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/An-explicit-counterexample-to-the-Auslander-Reiten-conjecture-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algebra at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ031A001
import Definitions.Def_OAIQ031A003
import Definitions.Def_OAIQ031A005
import Definitions.Def_OAIQ031A007
import Definitions.Def_OAIQ031A008
import Definitions.Def_OAIQ031A009

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Modules_Coinduced
attribute [-instance] _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ArExplicit

namespace Coinduced

variable {k R : Type*} [CommRing k] [Ring R] [Algebra k R]

instance instSMulCommClass : SMulCommClass k R (Coinduced k R) where
  smul_comm c r x := by ext s; rfl

end Coinduced
end ArExplicit

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Modules_CoinducedBimodule
attribute [-instance] _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ArExplicit.Coinduced
variable {k R : Type*} [CommRing k] [Ring R] [Algebra k R]

instance instSMulMulOpposite : SMul Rᵐᵒᵖ (Coinduced k R) :=
  ⟨fun r x => ⟨{ toFun := fun s => x.functional (r.unop * s)
                 map_add' := fun s t => by simp [mul_add]
                 map_smul' := fun a s => by simp }⟩⟩

@[simp] theorem functional_right (r : Rᵐᵒᵖ) (x : Coinduced k R) (s : R) :
    (r • x).functional s = x.functional (r.unop * s) := rfl

instance instModuleMulOpposite : Module Rᵐᵒᵖ (Coinduced k R) where
  one_smul x := by ext s; simp
  mul_smul r t x := by ext s; simp [mul_assoc]
  smul_zero r := by ext s; simp
  smul_add r x y := by ext s; simp
  zero_smul x := by ext s; simp
  add_smul r t x := by ext s; simp [add_mul]

instance instSMulCommClassMulOpposite : SMulCommClass R Rᵐᵒᵖ (Coinduced k R) where
  smul_comm r t x := by ext s; simp [mul_assoc]
instance instSMulCommClassMulOpposite_1 : SMulCommClass k Rᵐᵒᵖ (Coinduced k R) where
  smul_comm a r x := by ext s; rfl

end ArExplicit.Coinduced

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Algebras_SimpleDual
attribute [-instance] _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective
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

instance simpleRightAction : SMul Cᵐᵒᵖ (Simple q) :=
  ⟨fun c s => c.unop.coeff f • s⟩

@[simp] theorem simple_right_smul (c : Cᵐᵒᵖ) (s : Simple q) :
    c • s = c.unop.coeff f • s := rfl

def generator : Simple q := (LinearMap.range (dU q)).mkQ (vertexF q)

@[simp] theorem generator_coordinate : simpleCoordinate q (generator q) = 1 := rfl

end ArExplicit.Resolution

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Duality_DualResolution
attribute [-instance] _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.Resolution.instIsScalarTowerTSimple _root_.OAI.ArExplicit.Resolution.instModuleTSimple _root_.OAI.ArExplicit.Resolution.simpleRightAction _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective
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

def fixedLeft (p : C) : Submodule Cᵐᵒᵖ C where
  carrier := {a | p * a = a}
  zero_mem' := mul_zero p
  add_mem' := by
    intro a b ha hb
    change p * a = a at ha
    change p * b = b at hb
    change p * (a + b) = a + b
    rw [mul_add, ha, hb]
  smul_mem' := by
    intro c a ha
    change p * a = a at ha
    change p * (a * MulOpposite.unop c) = a * MulOpposite.unop c
    rw [← mul_assoc, ha]

abbrev rightE : Submodule Cᵐᵒᵖ C := fixedLeft q (basisVector q e)
abbrev rightF : Submodule Cᵐᵒᵖ C := fixedLeft q (basisVector q f)

def fromRightE (a : rightE q) : E q →ₗ[C] C where
  toFun b := (b : C) * a
  map_add' b c := add_mul (b : C) c a
  map_smul' c b := mul_assoc c (b : C) a

@[simp] theorem fromRightE_apply (a : rightE q) (b : E q) :
    fromRightE q a b = (b : C) * a := rfl

end ArExplicit.Resolution

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Duality_DualTensorEvaluation
attribute [-instance] _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns
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

def formula : Coinduced k R →ₗ[k] V →ₗ[k] Module.Dual k (V →ₗ[R] R) where
  toFun ℓ :=
    { toFun v :=
        { toFun f := ℓ.functional (f v)
          map_add' f g := by simp
          map_smul' a f := by simp }
      map_add' v w := by ext f; simp
      map_smul' a v := by ext f; simp [LinearMap.map_smul_of_tower] }
  map_add' ℓ μ := by ext v f; rfl
  map_smul' a ℓ := by ext v f; rfl

end DualTensor
end ArExplicit

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Homology_VectorTensorKunneth
attribute [-instance] _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ArExplicit.VectorComplex

open CategoryTheory CategoryTheory.Limits HomologicalComplex

universe u

variable (k : Type u) [Field k]
variable (F : ModuleCat.{u} k ⥤ ModuleCat.{u} k ⥤ ModuleCat.{u} k)
  [F.Additive] [∀ X, (F.obj X).Additive]

theorem totalMap_quasiIso {P P' Q Q' : ChainComplex (ModuleCat.{u} k) ℕ}
    (f : P ⟶ P') (g : Q ⟶ Q') [QuasiIso f] [QuasiIso g] :
    QuasiIso (mapBifunctorMap f g F (ComplexShape.down ℕ)) := by
  obtain ⟨e, rfl⟩ := (ChainComplex.quasiIso_iff_of_projective f).mp inferInstance
  obtain ⟨e', rfl⟩ := (ChainComplex.quasiIso_iff_of_projective g).mp inferInstance
  exact homotopyEquivalences_le_quasiIso _ _ _ ⟨totalHomotopyEquiv F e e', rfl⟩

end ArExplicit.VectorComplex

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Modules_InductionBimodule
attribute [-instance] _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ArExplicit

namespace InductionBimodule
variable {k R S : Type*} [CommRing k] [Ring R] [Ring S] [Algebra k R] [Algebra k S]
  (ι : R →ₐ[k] S)

def coordinates : InductionBimodule ι ≃ S where
  toFun := value
  invFun := InductionBimodule.mk
  left_inv _ := rfl
  right_inv _ := rfl

instance instAddCommGroup : AddCommGroup (InductionBimodule ι) := (coordinates ι).addCommGroup
instance instModule : Module S (InductionBimodule ι) := (coordinates ι).addEquiv.module S
instance instModule_1 : Module k (InductionBimodule ι) := (coordinates ι).addEquiv.module k
instance instSMulMulOpposite : SMul Rᵐᵒᵖ (InductionBimodule ι) := ⟨fun r x => ⟨x.value * ι r.unop⟩⟩

@[simp] theorem value_zero : (0 : InductionBimodule ι).value = 0 := rfl
@[simp] theorem value_add (x y : InductionBimodule ι) : (x + y).value = x.value + y.value := rfl
@[simp] theorem value_smul (s : S) (x : InductionBimodule ι) : (s • x).value = s * x.value := rfl
@[simp] theorem value_scalar (a : k) (x : InductionBimodule ι) : (a • x).value = a • x.value := rfl
@[simp] theorem value_right (r : Rᵐᵒᵖ) (x : InductionBimodule ι) :
    (r • x).value = x.value * ι r.unop := rfl

instance instModuleMulOpposite : Module Rᵐᵒᵖ (InductionBimodule ι) where
  one_smul x := by ext; simp
  mul_smul r s x := by ext; simp [mul_assoc]
  smul_zero r := by ext; simp
  smul_add r x y := by ext; simp [add_mul]
  add_smul r s x := by ext; simp [mul_add]
  zero_smul x := by ext; simp

end InductionBimodule
end ArExplicit

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Modules_TrivialInduction
attribute [-instance] _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.Resolution.instIsScalarTowerTSimple _root_.OAI.ArExplicit.Resolution.instModuleTSimple _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ArExplicit.TrivialInduction

variable {k R : Type*} [CommRing k] [Ring R] [Algebra k R]

local notation "T" => TrivialExtension k R

abbrev Middle := InductionBimodule (TrivialExtension.inlHom : R →ₐ[k] T)
abbrev Quotient := InductionBimodule (AlgHom.id k R)

instance dualModule : Module T (Coinduced k R) :=
  Module.compHom (Coinduced k R) TrivialExtension.projection.toRingHom

@[simp] theorem dual_smul (t : T) (φ : Coinduced k R) : t • φ = t.base • φ := rfl

instance quotientModule : Module T (Quotient (k := k) (R := R)) :=
  Module.compHom _ TrivialExtension.projection.toRingHom

@[simp] theorem quotient_smul_value (t : T) (r : Quotient (k := k) (R := R)) :
    (t • r).value = t.base * r.value := rfl

def inclusion : Coinduced k R →ₗ[Rᵐᵒᵖ] Middle (k := k) (R := R) where
  toFun φ := ⟨TrivialExtension.inr φ.functional⟩
  map_add' φ ψ := by
    apply InductionBimodule.ext
    apply TrivialExtension.ext
    · exact (zero_add _).symm
    · rfl
  map_smul' r φ := by
    apply InductionBimodule.ext
    apply TrivialExtension.ext
    · exact (zero_mul _).symm
    · ext x
      change φ.functional (r.unop * x) = 0 + φ.functional (r.unop * x)
      exact (zero_add _).symm

def projection : Middle (k := k) (R := R) →ₗ[Rᵐᵒᵖ] Quotient (k := k) (R := R) where
  toFun t := ⟨t.value.base⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem inclusion_value (φ : Coinduced k R) :
    (inclusion φ).value = TrivialExtension.inr φ.functional := rfl
@[simp] theorem projection_value (t : Middle (k := k) (R := R)) :
    (projection t).value = t.value.base := rfl

end ArExplicit.TrivialInduction

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Resolutions_NatResolutionCubic
attribute [-instance] _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Limits
open CochainComplex CochainComplex.HomComplex
namespace ArExplicit.ResolutionProducts
universe u
variable {k R : Type u} [Field k] [Ring R] [Algebra k R]
attribute [local instance] moduleCatBaseModule moduleCatBaseTower
variable {X : ModuleCat.{u} R} (P : ProjectiveResolution X)
variable (f : ∀ n : ℕ, P.complex.X (n+3) ⟶ P.complex.X n)

variable [CharP k 2]
variable (hf : ∀ n, f (n+1) ≫ P.complex.d (n+1) n =
  P.complex.d (n+4) (n+3) ≫ f n)

include hf k

theorem natCubicCochain_closed : δ 3 4 (natCubicCochain P f) = 0 := by
  apply Cochain.ext
  intro p q hpq
  by_cases hq : q ≤ 0
  · obtain ⟨m,rfl⟩ := Int.exists_eq_neg_ofNat hq
    have hp : p = -((m+4 : ℕ) : ℤ) := by omega
    subst p
    rw [δ_v 3 4 rfl _ _ _ hpq (-((m+1 : ℕ) : ℤ)) (-((m+3 : ℕ) : ℤ)) (by omega) (by omega)]
    rw [natCubicCochain_v P f (m+1), natCubicCochain_v P f m]
    rw [P.cochainComplex_d _ _ (m+1) m rfl rfl,
      P.cochainComplex_d _ _ (m+4) (m+3) rfl rfl]
    have hfour : (4 : ℤ).negOnePow = 1 := by decide
    simp only [hfour, one_smul, Category.assoc, Iso.inv_hom_id_assoc,
      Cochain.zero_v]
    rw [← Category.assoc (f (m+1)), hf m]
    let z := (P.cochainComplexXIso (-((m+4 : ℕ) : ℤ)) (m+4) rfl).hom ≫
      P.complex.d (m+4) (m+3) ≫ f m ≫
        (P.cochainComplexXIso (-(m : ℤ)) m rfl).inv
    change z + z = 0
    rw [← two_smul k z, show (2 : k) = 0 from CharP.cast_eq_zero k 2, zero_smul]
  · exact (P.cochainComplex.isZero_of_isStrictlyLE 0 q (by omega)).eq_of_tgt _ _

def natCubicCocycle : Cocycle P.cochainComplex P.cochainComplex 3 :=
  Cocycle.mk (natCubicCochain P f) 4 rfl (natCubicCochain_closed (k := k) P f hf)

end ArExplicit.ResolutionProducts

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Resolutions_ResolutionProducts
attribute [-instance] _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective
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

@[simp] theorem endExt_hom {X : C} (P : ProjectiveResolution X) {n : ℕ}
    (x : Cocycle P.cochainComplex P.cochainComplex (n : ℤ)) :
    (endExt P x).hom = conjugate (resolutionIso P)
      (ShiftedHom.map (Cocycle.equivHomShift.symm x) DerivedCategory.Q) :=
  Equiv.apply_symm_apply _ _

end ArExplicit.ResolutionProducts

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Tensor_ExternalTensorScalar
attribute [-instance] _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective
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
variable (M N : Type u) [AddCommGroup M] [AddCommGroup N]
variable [Module A M] [Module B N] [mM : Module k M] [mN : Module k N]
variable [IsScalarTower k A M] [IsScalarTower k B N]

def canonicalTensorObject : ModuleCat.{u} (A ⊗[k] B) :=
  letI : Module k M := moduleCatBaseModule (k := k) (R := A) (ModuleCat.of A M)
  letI : Module k N := moduleCatBaseModule (k := k) (R := B) (ModuleCat.of B N)
  letI : IsScalarTower k A M := moduleCatBaseTower (k := k) (R := A) (ModuleCat.of A M)
  letI : IsScalarTower k B N := moduleCatBaseTower (k := k) (R := B) (ModuleCat.of B N)
  moduleObject k A B M N

end ArExplicit.ExternalTensor

end

end OAI
end


