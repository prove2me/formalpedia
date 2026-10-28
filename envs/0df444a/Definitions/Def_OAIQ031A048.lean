-- Prove2me | Definitions.Def_OAIQ031A048
-- name    : OAIQ031A048
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T14:04:09.323448+00:00
-- url     : https://prove2.me/theorems/820e92b5-7bd6-4bc0-8ccf-5fe5d7e36fc7
-- title:
--   Definitions bundle OAIQ031A048 of the split of OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.ArExplicit.Statement.main`, carved from OpenAI's openai/math development (OpenAI, *An explicit counterexample to the Auslander-Reiten conjecture (result family 199)*, OpenAI Math Release, September 23, 2026, result family 199, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 13 declarations of OpenAI's Lean: 4 definitions and 9 theorems. The definitions and types are `OAI.ArExplicit.CompleteComparison.cokernelSyzygyEquiv`, `OAI.ArExplicit.ExternalTensor.selfExtScalarEquiv`, `OAI.ArExplicit.ExternalTensor.termPiEquiv`, `OAI.ArExplicit.Resolution.evaluateE`.
--
--   **Sources.** They come from these modules of lean/OAI/Algebra, in whole or in part: [`AuslanderReiten_Bar_ModuleBar`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Bar/ModuleBar.lean), [`AuslanderReiten_Cones_CokernelSyzygy`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Cones/CokernelSyzygy.lean), [`AuslanderReiten_Duality_DualResolution`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Duality/DualResolution.lean), [`AuslanderReiten_Tensor_ExternalTensorComplex`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Tensor/ExternalTensorComplex.lean), [`AuslanderReiten_Tensor_ExternalTensorDifferential`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Tensor/ExternalTensorDifferential.lean), [`AuslanderReiten_Tensor_ExternalTensorProjective`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Tensor/ExternalTensorProjective.lean), [`AuslanderReiten_Tensor_ExternalTensorScalar`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Tensor/ExternalTensorScalar.lean), [`AuslanderReiten_Tensor_ExternalTensorScalarExt`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Tensor/ExternalTensorScalarExt.lean), [`AuslanderReiten_Tensor_ExternalTensorScalarProducts`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Tensor/ExternalTensorScalarProducts.lean), [`AuslanderReiten_Tensor_ExternalTensorSingle`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Tensor/ExternalTensorSingle.lean).
--
--   **Imports.** It imports the bundles `OAIQ031A027`, `OAIQ031A029`, `OAIQ031A030`, `OAIQ031A031` and `OAIQ031A032` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ031A064`, `OAIQ031A065`, `OAIQ031A067`, `OAIQ031A072` and `OAIQ031A073`; the proof of `OAI_ArExplicit_MainConclusions_scalarExtension`.
-- source:
--   OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 199; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/An-explicit-counterexample-to-the-Auslander-Reiten-conjecture-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algebra at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ031A027
import Definitions.Def_OAIQ031A029
import Definitions.Def_OAIQ031A030
import Definitions.Def_OAIQ031A031
import Definitions.Def_OAIQ031A032

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Bar_ModuleBar
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
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

theorem boundary_left (n : ℕ) (a : R) (x : object k R M (n + 1)) :
    boundary k R M n (left k R M (n + 1) a x) =
      left k R M n a (boundary k R M n x) := by
  induction x using OAI.tensorInductionOn with
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul b x =>
    cases n with
    | zero => exact mul_smul _ _ _
    | succ n =>
      rw [left_tmul, boundary_succ_tmul, boundary_succ_tmul, map_add, left_tmul, ← left_mul]

omit [Module R M] [IsScalarTower k R M] in
theorem finiteBase [Module.Finite k R] [Module.Finite k M] (n : ℕ) :
    Module.Finite k (object k R M n) := by
  induction n with
  | zero => infer_instance
  | succ n ih =>
    let := ih
    change Module.Finite k (R ⊗[k] object k R M n)
    infer_instance

end ArExplicit.ModuleBar

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Cones_CokernelSyzygy
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ArExplicit.CompleteComparison

universe u

variable {R : Type u} [Ring R]
variable {P : ChainComplex (ModuleCat.{u} R) ℤ}

noncomputable def cokernelSyzygyEquiv (hP : ExactProjectiveComplex P) (n : ℤ) :
    Cokernel P (n + 1) ≃ₗ[R] LinearMap.ker (P.d n (n - 1)).hom := by
  have hex : LinearMap.range (P.d ((n + 1) + 1) (n + 1)).hom =
      LinearMap.ker (P.d (n + 1) n).hom :=
    hP.exactAt_of_indices rfl (by omega)
  exact (Submodule.quotEquivOfEq _ _ hex).trans
    ((P.d (n + 1) n).hom.quotKerEquivRange.trans
      (LinearEquiv.ofEq _ _ (hP.exactAt n)))

end ArExplicit.CompleteComparison

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Duality_DualResolution
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.Resolution.instIsScalarTowerTSimple _root_.OAI.ArExplicit.Resolution.instModuleTSimple _root_.OAI.ArExplicit.Resolution.simpleRightAction _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
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

def evaluateE (g : E q →ₗ[C] C) : rightE q := ⟨g (vertexE q), by
  change basisVector q e * g (vertexE q) = g (vertexE q)
  calc
    _ = g (basisVector q e • vertexE q) := (g.map_smul _ _).symm
    _ = _ := congrArg g (e_smul_vertexE q)⟩

@[simp] theorem evaluateE_fromRightE (a : rightE q) : evaluateE q (fromRightE q a) = a := by
  apply Subtype.ext
  exact a.property

end ArExplicit.Resolution

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Tensor_ExternalTensorProjective
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct

namespace ArExplicit.ExternalTensor

universe u
variable (k A B : Type u) [Field k] [Ring A] [Ring B] [Algebra k A] [Algebra k B]

variable {M N : Type u} [AddCommGroup M] [AddCommGroup N]
variable [Module k M] [Module k N] [Module A M] [Module B N]
variable [IsScalarTower k A M] [IsScalarTower k B N]

theorem projective [Module.Finite A M] [Module.Projective A M]
    [Module.Finite B N] [Module.Projective B N] :
    Module.Projective (A ⊗[k] B) (moduleObject k A B M N) := by
  obtain ⟨n, p, hp⟩ := Module.Finite.exists_fin' A M
  obtain ⟨m, q, hq⟩ := Module.Finite.exists_fin' B N
  obtain ⟨s, hs⟩ := Module.projective_lifting_property p (LinearMap.id : M →ₗ[A] M) hp
  obtain ⟨t, ht⟩ := Module.projective_lifting_property q (LinearMap.id : N →ₗ[B] N) hq
  apply Module.Projective.of_split (map k A B s t) (map k A B p q)
  apply LinearMap.ext
  intro z
  let w : M ⊗[k] N := z
  change TensorProduct.map (p.restrictScalars k) (q.restrictScalars k)
    (TensorProduct.map (s.restrictScalars k) (t.restrictScalars k) w) = w
  induction w using OAI.tensorInductionOn with
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul x y =>
    simp only [TensorProduct.map_tmul, LinearMap.restrictScalars_apply,
      show p (s x) = x from DFunLike.congr_fun hs x,
      show q (t y) = y from DFunLike.congr_fun ht y]

end ArExplicit.ExternalTensor

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Tensor_ExternalTensorComplex
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ExternalTensor.diagonalZeroUnique _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ArExplicit.ExternalTensor

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

universe u

variable (k A B : Type u) [Field k] [Ring A] [Ring B] [Algebra k A] [Algebra k B]

attribute [local instance] moduleCatBaseModule moduleCatBaseTower

variable (P : ChainComplex (ModuleCat.{u} A) ℕ) (Q : ChainComplex (ModuleCat.{u} B) ℕ)

def termPiEquiv (n : ℕ) :
    (complex k A B P Q).X n ≃ₗ[A ⊗[k] B] (∀ p : Diagonal n, summands k A B P Q n p) :=
  (termDirectSumEquiv k A B P Q n).trans DFinsupp.linearEquivFunOnFintype

variable [Module.Finite k A] [Module.Finite k B]
variable [∀ n, Module.Finite A (P.X n)] [∀ n, Module.Finite B (Q.X n)]

variable [∀ n, Module.Projective A (P.X n)] [∀ n, Module.Projective B (Q.X n)]

omit [Module.Finite k A] [Module.Finite k B] in
theorem term_projective (n : ℕ) : Module.Projective (A ⊗[k] B) ((complex k A B P Q).X n) := by
  let (index : Diagonal n) : Module.Projective (A ⊗[k] B) (summands k A B P Q n index) :=
    projective k A B
  exact Module.Projective.of_equiv (termDirectSumEquiv k A B P Q n).symm

end ArExplicit.ExternalTensor

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Tensor_ExternalTensorDifferential
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ArExplicit.ExternalTensor

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped TensorProduct

universe u

variable (k A B : Type u) [Field k] [Ring A] [Ring B] [Algebra k A] [Algebra k B]

attribute [local instance] moduleCatBaseModule moduleCatBaseTower

variable (P : ChainComplex (ModuleCat.{u} A) ℕ) (Q : ChainComplex (ModuleCat.{u} B) ℕ)

theorem hom_ext {N : ModuleCat.{u} (A ⊗[k] B)} {n : ℕ}
    {f g : (complex k A B P Q).X n ⟶ N}
    (h : ∀ (i j : ℕ) (hij : i+j=n),
      inclusion k A B P Q i j n hij ≫ f = inclusion k A B P Q i j n hij ≫ g) : f=g :=
  mapBifunctor.hom_ext h

end ArExplicit.ExternalTensor

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Tensor_ExternalTensorScalar
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ExternalTensor.freeFree _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
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

theorem canonicalTensorObject_eq :
    canonicalTensorObject k A B M N = moduleObject k A B M N := by
  cases canonicalScalar_eq k A M (mM := mM)
  cases canonicalScalar_eq k B N (mM := mN)
  rfl

end ArExplicit.ExternalTensor

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Tensor_ExternalTensorScalarExt
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ExternalTensor.freeFree _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
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
variable [Module A M] [Module B N] [Module k M] [Module k N]
variable [IsScalarTower k A M] [IsScalarTower k B N]

def selfExtScalarEquiv (n : ℕ) :
    Ext (moduleObject k A B M N) (moduleObject k A B M N) n ≃ₗ[k]
      Ext (canonicalTensorObject k A B M N) (canonicalTensorObject k A B M N) n := by
  rw [canonicalTensorObject_eq]

end ArExplicit.ExternalTensor

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Tensor_ExternalTensorScalarProducts
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ExternalTensor.freeFree _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
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

@[simp] theorem selfExtScalarEquiv_identity :
    selfExtScalarEquiv k A B M N 0 (Ext.mk₀ (𝟙 (moduleObject k A B M N))) =
      Ext.mk₀ (𝟙 (canonicalTensorObject k A B M N)) := by
  cases canonicalScalar_eq k A M (mM := mM)
  cases canonicalScalar_eq k B N (mM := mN)
  rfl

end ArExplicit.ExternalTensor

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Tensor_ExternalTensorSingle
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ArExplicit.ExternalTensor
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped TensorProduct
universe u
variable (k A B : Type u) [Field k] [Ring A] [Ring B] [Algebra k A] [Algebra k B]
attribute [local instance] moduleCatBaseModule moduleCatBaseTower

variable (M : ModuleCat.{u} A) (N : ModuleCat.{u} B)

theorem singleTotal_summand_isZero (n : ℕ) (hn : n ≠ 0) (p : Diagonal n) :
    IsZero (summands k A B ((ChainComplex.single₀ (ModuleCat A)).obj M)
      ((ChainComplex.single₀ (ModuleCat B)).obj N) n p) := by
  by_cases hi : p.val.1 = 0
  · have hj : p.val.2 ≠ 0 := by have h := p.property; omega
    exact (rightFunctor k A B (((ChainComplex.single₀ (ModuleCat A)).obj M).X p.val.1)).map_isZero
      (isZero_single_obj_X _ _ _ _ hj)
  · exact ((bifunctor k A B).flip.obj (((ChainComplex.single₀ (ModuleCat B)).obj N).X p.val.2)).map_isZero
      (isZero_single_obj_X _ _ _ _ hi)

end ArExplicit.ExternalTensor

end

end OAI
end


