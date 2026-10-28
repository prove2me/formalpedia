-- Prove2me | Definitions.Def_OAIQ031A060
-- name    : OAIQ031A060
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T14:09:22.710759+00:00
-- url     : https://prove2.me/theorems/f741f69b-79de-425e-a458-aca7ddaca05e
-- title:
--   Definitions bundle OAIQ031A060 of the split of OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.ArExplicit.Statement.main`, carved from OpenAI's openai/math development (OpenAI, *An explicit counterexample to the Auslander-Reiten conjecture (result family 199)*, OpenAI Math Release, September 23, 2026, result family 199, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 12 declarations of OpenAI's Lean: 7 definitions and 5 theorems. The definitions and types are `OAI.ArExplicit.TriangleGradedSequence.zeroDiagonalProjection`, `OAI.ArExplicit.scalarExtensionCokernelEquiv`, `OAI.ArExplicit.scalarExtensionComplex`, `OAI.ArExplicit.scalarExtensionEquiv`, `OAI.ArExplicit.scalarExtensionHomCoordinates`, `OAI.ArExplicit.scalarExtensionPi`, `OAI.ArExplicit.verifiedCandidate`.
--
--   **Sources.** They come from these modules of lean/OAI/Algebra, in whole or in part: [`AuslanderReiten_BaseChange_ScalarExtensionCokernel`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/BaseChange/ScalarExtensionCokernel.lean), [`AuslanderReiten_BaseChange_ScalarExtensionComplete`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/BaseChange/ScalarExtensionComplete.lean), [`AuslanderReiten_BaseChange_ScalarExtensionHom`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/BaseChange/ScalarExtensionHom.lean), [`AuslanderReiten_BaseChange_ScalarExtensionProjective`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/BaseChange/ScalarExtensionProjective.lean), [`AuslanderReiten_Coordinates_ConcreteParameters`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Coordinates/ConcreteParameters.lean), [`AuslanderReiten_Fibers_FiberProjectionZero`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Fibers/FiberProjectionZero.lean), [`AuslanderReiten_HomComplex_FullHomShiftedIdentity`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/HomComplex/FullHomShiftedIdentity.lean), [`AuslanderReiten_Homology_TriangleConnectingProduct`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Homology/TriangleConnectingProduct.lean), [`AuslanderReiten_Main`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Main.lean), [`AuslanderReiten_Parameters`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Parameters.lean).
--
--   **Imports.** It imports the bundles `OAIQ031A035`, `OAIQ031A038`, `OAIQ031A040` and `OAIQ031A043` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ031A076`; the proofs of `OAI.ArExplicit.GorensteinProjective.scalarExtension`, `OAI.ArExplicit.PositiveExtVanish.scalarExtension` and `OAI.ArExplicit.nonprojective_scalarExtension`.
-- source:
--   OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 199; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/An-explicit-counterexample-to-the-Auslander-Reiten-conjecture-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algebra at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ031A035
import Definitions.Def_OAIQ031A038
import Definitions.Def_OAIQ031A040
import Definitions.Def_OAIQ031A043

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_BaseChange_ScalarExtensionCokernel
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct
namespace ArExplicit
universe u v w
variable (k : Type u) [Field k] (E : Type v) [Field E] [Algebra k E]
  (R : Type w) [Ring R] [Algebra k R]
  {L M : Type w}
  [AddCommGroup L] [Module R L] [Module k L] [IsScalarTower k R L]
  [AddCommGroup M] [Module R M] [Module k M] [IsScalarTower k R M]

attribute [local instance] scalarExtensionModule

def scalarExtensionCokernelEquiv (d : L →ₗ[R] M) :
    ((E ⊗[k] M) ⧸ LinearMap.range (scalarExtensionMap k E R d)) ≃ₗ[E ⊗[k] R]
      (E ⊗[k] (M ⧸ LinearMap.range d)) :=
  (scalarExtensionMap_exact k E R d (LinearMap.range d).mkQ
    (LinearMap.exact_map_mkQ_range d)).linearEquivOfSurjective
      (scalarExtensionMap_surjective k E R _ (Submodule.mkQ_surjective _))

def scalarExtensionEquiv (e : L ≃ₗ[R] M) :
    (E ⊗[k] L) ≃ₗ[E ⊗[k] R] (E ⊗[k] M) :=
  LinearEquiv.ofLinearMap (scalarExtensionMap k E R e.toLinearMap)
    (scalarExtensionMap k E R e.symm.toLinearMap)
    (by rw [← scalarExtensionMap_comp]; simp)
    (by rw [← scalarExtensionMap_comp]; simp)

end ArExplicit

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_BaseChange_ScalarExtensionProjective
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct
namespace ArExplicit
universe u v w

variable (k : Type u) [Field k] (E : Type v) [Field E] [Algebra k E]
  (R : Type w) [Ring R] [Algebra k R]

attribute [local instance] scalarExtensionModule

def scalarExtensionPi (n : ℕ) :
    (E ⊗[k] (Fin n → R)) ≃ₗ[E ⊗[k] R] (Fin n → E ⊗[k] R) where
  __ := (TensorProduct.piRight k E E (fun _ : Fin n => R)).toAddEquiv
  map_smul' a x := by
    change TensorProduct.piRight k E E (fun _ : Fin n => R) (a • x) =
      a • TensorProduct.piRight k E E (fun _ : Fin n => R) x
    induction a using OAI.tensorInductionOn with
    | add a b ha hb => simp only [add_smul, map_add, ha, hb]
    | tmul e r =>
      induction x using OAI.tensorInductionOn with
      | add x y hx hy => simp only [smul_add, map_add, hx, hy]
      | tmul e' f =>
        ext i
        simp only [scalarExtension_smul_tmul, TensorProduct.piRight_apply,
          TensorProduct.piRightHom_tmul, Pi.smul_apply, smul_eq_mul,
          Algebra.TensorProduct.tmul_mul_tmul]

end ArExplicit

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_BaseChange_ScalarExtensionHom
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct
namespace ArExplicit
universe u v w
variable (k : Type u) [Field k] (E : Type v) [Field E] [Algebra k E]
  (R : Type w) [Ring R] [Algebra k R]
  {M N L : Type w}
  [AddCommGroup M] [Module R M] [Module k M] [IsScalarTower k R M]
  [AddCommGroup N] [Module R N] [Module k N] [IsScalarTower k R N]
  [AddCommGroup L] [Module R L] [Module k L] [IsScalarTower k R L]

attribute [local instance] scalarExtensionModule

def scalarExtensionHomCoordinates (n : ℕ) :
    ((E ⊗[k] (Fin n → R)) →ₗ[E ⊗[k] R] (E ⊗[k] N)) ≃ₗ[E]
      (Fin n → E ⊗[k] N) :=
  (LinearEquiv.congrLeft (E ⊗[k] N) E (scalarExtensionPi k E R n)).trans
    (LinearEquiv.piRing (E ⊗[k] R) (E ⊗[k] N) (Fin n) E)

end ArExplicit

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Parameters
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ArExplicit

theorem twist_eigenvalues_ne (n : ℕ) (hn : 0 < n) :
    (H₁ ^ n)⁻¹ ≠ (H₂ ^ n)⁻¹ := by
  intro h
  have := congrArg (fun x : BaseField => x⁻¹) h
  simp only [inv_inv] at this
  exact parameter_pow_ne 1 2 (by decide) n hn this

end ArExplicit

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_BaseChange_ScalarExtensionComplete
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory
open scoped TensorProduct
namespace ArExplicit
universe u v w
variable (k : Type u) [Field k] (E : Type v) [Field E] [Algebra k E]
  (R : Type w) [Ring R] [Algebra k R]

attribute [local instance] moduleCatBaseModule

attribute [local instance] moduleCatBaseTower scalarExtensionModule

def scalarExtensionComplex (P : ChainComplex (ModuleCat.{w} R) ℤ) :
    ChainComplex (ModuleCat.{max v w} (E ⊗[k] R)) ℤ where
  X n := ModuleCat.of (E ⊗[k] R) (E ⊗[k] P.X n)
  d i j := ModuleCat.ofHom (scalarExtensionMap k E R (P.d i j).hom)
  shape i j hij := by
    rw [P.shape i j hij]
    apply ModuleCat.hom_ext
    exact map_zero (scalarExtensionHomLinear k E R)
  d_comp_d' i j l _ _ := by
    apply ModuleCat.hom_ext
    change (scalarExtensionMap k E R (P.d j l).hom).comp
      (scalarExtensionMap k E R (P.d i j).hom) = 0
    rw [← scalarExtensionMap_comp]
    rw [show (P.d j l).hom.comp (P.d i j).hom = 0 from
      congrArg ModuleCat.Hom.hom (P.d_comp_d i j l)]
    exact map_zero (scalarExtensionHomLinear k E R)

end ArExplicit

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Coordinates_ConcreteParameters
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ArExplicit

theorem parameterUnit_twist_ne (n : ℕ) (hn : 0 < n) :
    (((parameterUnit 1)⁻¹ : BaseFieldˣ) : BaseField)^n ≠
      (((parameterUnit 2)⁻¹ : BaseFieldˣ) : BaseField)^n := by
  simpa only [Units.val_inv_eq_inv_val, parameterUnit_val, inv_pow] using twist_eigenvalues_ne n hn

end ArExplicit

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Fibers_FiberProjectionZero
attribute [-instance] _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ArExplicit.TriangleGradedSequence
open CategoryTheory CategoryTheory.Pretriangulated
universe u v w
variable (k : Type u) [Field k] [CharP k 2]
variable {C : Type w} [Category.{v} C] [Preadditive C] [Linear k C]
variable [Limits.HasZeroObject C] [HasShift C ℤ]
variable [∀ n : ℤ, (CategoryTheory.shiftFunctor C n).Additive] [Pretriangulated C]
variable (T : Triangle C) (hT : T ∈ distTriang C) (X : C)
variable (em : Middle T X 0 ≃ₗ[k] k × k) (et : Top T X 0 ≃ₗ[k] k)
variable (c : k) (hc : c ≠ 0)
variable (hrow : ∀ m, et (second k T X 0 m) = c * ((em m).1 + (em m).2))

include hT hc hrow in

theorem first_zero_diagonal (x : Bottom T X 0) :
    (em (first k T X 0 x)).1 = (em (first k T X 0 x)).2 := by
  have hz : second k T X 0 (first k T X 0 x) = 0 := by
    have hmem := LinearMap.mem_range_self (first k T X 0) x
    rw [exact_middle k T X hT 0] at hmem
    exact hmem
  have h := hrow (first k T X 0 x)
  rw [hz, map_zero] at h
  exact CharTwo.add_eq_zero.mp ((mul_eq_zero.mp h.symm).resolve_left hc)

def zeroDiagonalProjection : Bottom T X 0 →ₗ[k] diagonalSubmodule (k := k) (V := k) :=
  (em.toLinearMap.comp (first k T X 0)).codRestrict _
    (first_zero_diagonal k T hT X em et c hc hrow)

end ArExplicit.TriangleGradedSequence

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_HomComplex_FullHomShiftedIdentity
attribute [-instance] _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ArExplicit
open CategoryTheory
open CochainComplex CochainComplex.HomComplex CompleteComparison
universe u v w
variable (k : Type u) [CommRing k]
variable {C : Type w} [Category.{v} C] [Preadditive C] [Linear k C]

theorem fullHomShiftedHomotopyEquiv_identity (K : CochainComplex C ℤ) :
    fullHomShiftedHomotopyEquiv k K K 0 (fullHomIdentity K) =
      (shiftFunctorZero (HomotopyCategory C (ComplexShape.up ℤ)) ℤ).inv.app
        ((HomotopyCategory.quotient C _).obj K) := by
  have h : Cocycle.equivHomShift.symm (Cocycle.ofHom (𝟙 K)) =
      ShiftedHom.mk₀ (0 : ℤ) rfl (𝟙 K) := by
    apply HomologicalComplex.Hom.ext
    funext i
    simp only [cocycleHom_component, Cocycle.ofHom_coe]
    simp only [ShiftedHom.mk₀, CategoryTheory.shiftFunctorZero',
      eqToIso_refl, Iso.trans_inv, Iso.refl_inv,
      Category.id_comp, CochainComplex.shiftFunctorZero_inv_app_f, Category.comp_id]
    change (Cochain.ofHom (𝟙 K)).v i (i+0) rfl =
      (K.XIsoOfEq (show i=i+0 by omega)).hom
    simpa only [Cochain.ofHom_v, HomologicalComplex.id_f, Category.id_comp] using
      (Cochain.v_comp_XIsoOfEq_hom (Cochain.ofHom (𝟙 K)) i i (i+0) (add_zero i) (by omega)).symm
  rw [fullHomIdentity, fullHomShiftedHomotopyEquiv_mk, h]
  change (ShiftedHom.mk₀ (0 : ℤ) rfl (𝟙 K)).map (HomotopyCategory.quotient C _) = _
  rw [ShiftedHom.map_mk₀, CategoryTheory.Functor.map_id]
  simp [ShiftedHom.mk₀, CategoryTheory.shiftFunctorZero']

end ArExplicit

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Homology_TriangleConnectingProduct
attribute [-instance] _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Pretriangulated
namespace ArExplicit.TriangleGradedSequence
universe u v w
variable (k : Type u) [CommRing k] [CharP k 2]
variable {C : Type w} [Category.{v} C] [Preadditive C] [Linear k C]
variable [HasShift C ℤ]
variable [∀ n : ℤ, (CategoryTheory.shiftFunctor C n).Additive]
variable (T : Triangle C) (X : C)

theorem first_eq_shift (n : ℤ) (v : Bottom T X n) :
    first k T X n v = v ≫ T.mor₁⟦n⟧' := by
  change v ≫ (n.negOnePow • T.mor₁⟦n⟧') = _
  rw [integerUnit_smul k]

end ArExplicit.TriangleGradedSequence

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Main
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory
open scoped ModuleCat.Algebra
namespace ArExplicit
universe v

attribute [local instance] moduleCatBaseModule moduleCatBaseTower

def verifiedCandidate {R M : Type} [Ring R] [Algebra BaseField R]
    [AddCommGroup M] [Module R M] [Module BaseField M] [IsScalarTower BaseField R M]
    (h : MainConclusions BaseField R M) :
    {c : Candidate // MainConclusions BaseField c.R c.M} :=
  ⟨{ R := R, M := M }, h⟩

end ArExplicit

end

end OAI
end


