-- Prove2me | Definitions.Def_OAIQ031A056
-- name    : OAIQ031A056
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T14:07:55.873218+00:00
-- url     : https://prove2.me/theorems/8f2d8397-1661-4790-920a-a287e2638214
-- title:
--   Definitions bundle OAIQ031A056 of the split of OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.ArExplicit.Statement.main`, carved from OpenAI's openai/math development (OpenAI, *An explicit counterexample to the Auslander-Reiten conjecture (result family 199)*, OpenAI Math Release, September 23, 2026, result family 199, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 20 declarations of OpenAI's Lean: 5 definitions, 1 instance and 14 theorems. The definitions and types are `OAI.ArExplicit.ConvertedAlgebra.radicalT`, `OAI.ArExplicit.ConvertedAlgebra.radicalU`, `OAI.ArExplicit.ExternalTensor.transportSummand`, `OAI.ArExplicit.ExternalTensor.transportTerm`, `OAI.ArExplicit.coneLiftKernel`.
--
--   **Sources.** They come from these modules of lean/OAI/Algebra, in whole or in part: [`AuslanderReiten_Cocycles_CocycleCorners`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Cocycles/CocycleCorners.lean), [`AuslanderReiten_Complete_CompleteNullhomotopy`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Complete/CompleteNullhomotopy.lean), [`AuslanderReiten_Cones_ConeCokernel`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Cones/ConeCokernel.lean), [`AuslanderReiten_Cones_ConeConnectingCoordinates`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Cones/ConeConnectingCoordinates.lean), [`AuslanderReiten_HomComplex_FullHomProductCoordinate`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/HomComplex/FullHomProductCoordinate.lean), [`AuslanderReiten_HomComplex_FullHomProductReindex`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/HomComplex/FullHomProductReindex.lean), [`AuslanderReiten_Modules_InductionBimodule`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Modules/InductionBimodule.lean), [`AuslanderReiten_Resolutions_BinaryKoszulDual`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Resolutions/BinaryKoszulDual.lean), [`AuslanderReiten_Tensor_ExternalTensorTransport`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Tensor/ExternalTensorTransport.lean), [`AuslanderReiten_Triangular_ConvertedStructure`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Triangular/ConvertedStructure.lean), [`AuslanderReiten_Triangular_TriangularRadical`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Triangular/TriangularRadical.lean).
--
--   **Imports.** It imports the bundles `OAIQ031A027`, `OAIQ031A028`, `OAIQ031A029`, `OAIQ031A032`, `OAIQ031A033`, `OAIQ031A035`, `OAIQ031A036`, `OAIQ031A038` and `OAIQ031A039` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ031A071`, `OAIQ031A072`, `OAIQ031A073`, `OAIQ031A074` and `OAIQ031A076`.
-- source:
--   OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 199; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/An-explicit-counterexample-to-the-Auslander-Reiten-conjecture-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algebra at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ031A027
import Definitions.Def_OAIQ031A028
import Definitions.Def_OAIQ031A029
import Definitions.Def_OAIQ031A032
import Definitions.Def_OAIQ031A033
import Definitions.Def_OAIQ031A035
import Definitions.Def_OAIQ031A036
import Definitions.Def_OAIQ031A038
import Definitions.Def_OAIQ031A039

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Cocycles_CocycleCorners
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ArExplicit

namespace CocycleData

theorem cochain_data_properties : cochain.all (fun p => decide (
    (∀ b : Bool, p.first ≠ TIndex.vertex b ∧ p.second ≠ TIndex.vertex b ∧ p.third ≠ TIndex.vertex b) ∧
    p.first.target = p.second.source ∧ p.second.target = p.third.source ∧
    p.first.source = p.output.source ∧ p.third.target = p.output.target ∧
    p.first.weight + p.second.weight + p.third.weight = p.output.weight + 1)) = true := by
  decide +kernel

theorem cochain_term_properties (t : TripleMonomial) (ht : t ∈ cochain) :
    (∀ b : Bool, t.first ≠ TIndex.vertex b ∧ t.second ≠ TIndex.vertex b ∧ t.third ≠ TIndex.vertex b) ∧
    t.first.target = t.second.source ∧ t.second.target = t.third.source ∧
    t.first.source = t.output.source ∧ t.third.target = t.output.target ∧
    t.first.weight + t.second.weight + t.third.weight = t.output.weight + 1 := by
  exact of_decide_eq_true ((List.all_eq_true.mp cochain_data_properties) t ht)

end CocycleData
end ArExplicit

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Complete_CompleteNullhomotopy
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open CategoryTheory

namespace ArExplicit.CompleteComparison

universe u

variable {R : Type u} [Ring R]
variable {P Q : ChainComplex (ModuleCat.{u} R) ℤ}

theorem nullhomotopy_of_cokernel_zero (hP : TotallyAcyclicComplex P)
    (hQ : ExactProjectiveComplex Q) (F : P ⟶ Q) (hf : cokernelMap F 0 = 0) :
    ∃ H : Homotopy F 0, H.hom (-1) 0 = 0 := by
  let := hP.projective 0
  have hz : (LinearMap.range (Q.d 1 0).hom).mkQ.comp (F.f 0).hom = 0 := by
    calc
      _ = (cokernelMap F 0).comp (LinearMap.range (P.d 1 0).hom).mkQ :=
        (cokernelMap_mkQ F 0).symm
      _ = 0 := by rw [hf, LinearMap.zero_comp]
  obtain ⟨h₀, hh₀⟩ := lift_through_exact (Q.d 1 0).hom
    (LinearMap.range (Q.d 1 0).hom).mkQ (Submodule.ker_mkQ _).symm (F.f 0).hom hz
  obtain ⟨H, hH⟩ := nullhomotopy_of_initial_with_component hP hQ F h₀ 0 (by
    rw [LinearMap.zero_comp, add_zero, hh₀])
  exact ⟨H, hH⟩

end ArExplicit.CompleteComparison

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Cones_ConeCokernel
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ArExplicit

variable {R M N E : Type*} [Ring R]
variable [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
variable [AddCommGroup E] [Module R E]

namespace ConeCokernel

variable {Q₀ Q₁ P₀ P₁ P₂ : Type*}
variable [AddCommGroup Q₀] [Module R Q₀] [AddCommGroup Q₁] [Module R Q₁]
variable [AddCommGroup P₀] [Module R P₀] [AddCommGroup P₁] [Module R P₁]
variable [AddCommGroup P₂] [Module R P₂]
variable (dQ : Q₁ →ₗ[R] Q₀) (dP : P₁ →ₗ[R] P₀) (f : P₁ →ₗ[R] Q₀)

theorem projective [Module.Projective R (Left dQ)] [Module.Projective R (Right dP)]
    (eP : P₂ →ₗ[R] P₁) (f₁ : P₂ →ₗ[R] Q₁)
    (hex : Function.Exact eP dP) (hc : dQ.comp f₁ = f.comp eP) :
    Module.Projective R (Middle dQ dP f) :=
  projective_of_exact (inclusion dQ dP f) (projection dQ dP f)
    (inclusion_injective dQ dP f eP f₁ hex hc) (projection_surjective dQ dP f)
    (exact dQ dP f)

end ConeCokernel
end ArExplicit

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Cones_ConeConnectingCoordinates
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ArExplicit
open CategoryTheory HomologicalComplex
open CochainComplex CochainComplex.HomComplex CompleteComparison
universe u
variable {R : Type u} [Ring R]
variable (H : CochainComplex (ModuleCat.{u} R) ℤ)

variable {H} {F G : CochainComplex (ModuleCat.{u} R) ℤ}
variable (φ : F ⟶ G) (κ : H ⟶ mappingCone φ)

theorem coneLiftKernelComponent_square :
    (cochainCokernelMap φ).comp (coneLiftKernelComponent φ κ) =
      (coneLiftMiddle φ κ).comp (H.d (-1) 0).hom := by
  ext z
  have hκ := congrArg (fun f : H.X (-1) ⟶ (mappingCone φ).X 0 => f.hom z) (κ.comm (-1) 0)
  change ((mappingCone φ).d (-1) 0).hom ((κ.f (-1)).hom z) =
    (κ.f 0).hom ((H.d (-1) 0).hom z) at hκ
  have hc := DFunLike.congr_fun (coneTermEquiv_differential φ (-1)) ((κ.f (-1)).hom z)
  change coneTermEquiv φ 0 (((mappingCone φ).d (-1) 0).hom ((κ.f (-1)).hom z)) = _ at hc
  rw [hκ] at hc
  have hh := congrArg (fun v : G.X 0 × F.X 1 =>
    (LinearMap.range (G.d (-1) 0).hom).mkQ v.1) hc
  change (coneLiftMiddle φ κ) ((H.d (-1) 0).hom z) =
    (LinearMap.range (G.d (-1) 0).hom).mkQ
      ((G.d (-1) 0).hom (conePreviousTermEquiv φ ((κ.f (-1)).hom z)).1 +
        (φ.f 0).hom (conePreviousTermEquiv φ ((κ.f (-1)).hom z)).2) at hh
  have hz : (LinearMap.range (G.d (-1) 0).hom).mkQ
      ((G.d (-1) 0).hom (conePreviousTermEquiv φ ((κ.f (-1)).hom z)).1) = 0 :=
    (Submodule.Quotient.mk_eq_zero _).mpr ⟨_, rfl⟩
  rw [map_add, hz, zero_add] at hh
  exact hh.symm

variable (hi : Function.Injective (cochainCokernelMap φ))

include hi in

theorem coneLiftKernelComponent_closed :
    (coneLiftKernelComponent φ κ).comp (H.d (-2) (-1)).hom = 0 := by
  ext z
  apply hi
  change ((cochainCokernelMap φ).comp (coneLiftKernelComponent φ κ))
    ((H.d (-2) (-1)).hom z) = cochainCokernelMap φ 0
  rw [map_zero]
  rw [coneLiftKernelComponent_square]
  change (coneLiftMiddle φ κ)
    (((H.d (-1) 0).hom.comp (H.d (-2) (-1)).hom) z) = 0
  rw [show (H.d (-1) 0).hom.comp (H.d (-2) (-1)).hom = 0 from
    congrArg ModuleCat.Hom.hom (H.d_comp_d (-2) (-1) 0)]
  exact map_zero _

def coneLiftKernel : RawSyzygy H →ₗ[R] CochainCokernel F :=
  (LinearMap.range (H.d (-2) (-1)).hom).liftQ (coneLiftKernelComponent φ κ)
    (LinearMap.range_le_ker_iff.mpr (coneLiftKernelComponent_closed φ κ hi))

end ArExplicit

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Resolutions_BinaryKoszulDual
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ArExplicit.BinaryKoszul

universe u

variable (k : Type u) [Field k]

theorem dualRow_dualColumn (n : ℕ) : (dualRow k n).comp (dualColumn k (n + 1)) = 0 := by
  apply LinearMap.ext
  intro f
  apply LinearMap.ext
  intro x
  change f (mulY k (n + 1) (mulX k n x)) + -f (mulX k (n + 1) (mulY k n x)) = 0
  have h := DFunLike.congr_fun (mul_commute k n) x
  change mulX k (n + 1) (mulY k n x) = mulY k (n + 1) (mulX k n x) at h
  rw [h, add_neg_cancel]

theorem dualColumn_injective (n : ℕ) : Function.Injective (dualColumn k n) := by
  intro f g h
  apply LinearMap.ext
  intro x
  obtain ⟨⟨a, b⟩, rfl⟩ := row_surjective k n x
  have hy := congrArg Prod.fst h
  have hx := congrArg Prod.snd h
  have hya := DFunLike.congr_fun hy b
  have hxa := neg_injective (DFunLike.congr_fun hx a)
  change f (mulY k n b) = g (mulY k n b) at hya
  change f (mulX k n a) = g (mulX k n a) at hxa
  simp only [row_apply, map_add, hxa, hya]

end ArExplicit.BinaryKoszul

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_HomComplex_FullHomProductReindex
attribute [-instance] _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ArExplicit.CompleteComparison
open CategoryTheory
open CochainComplex CochainComplex.HomComplex
universe u w
variable {k : Type u} [Field k]
variable {C : Type w} [Category.{u} C] [Preadditive C] [Linear k C]
variable {K L M : CochainComplex C ℤ} {a b c d : ℤ}

theorem fullHomProduct_reindex_left (h : a=b) (h₁ : b+c=d) (h₂ : a+c=d)
    (x : CohomologyClass K L a) (y : CohomologyClass L M c) :
    TateKoszul.degreeEquiv (k := k) (CohomologyClass K M) h₁
      (fullHomProduct (TateKoszul.degreeEquiv (k := k) (CohomologyClass K L) h x) y) =
    TateKoszul.degreeEquiv (k := k) (CohomologyClass K M) h₂ (fullHomProduct x y) := by
  subst b
  rfl

end ArExplicit.CompleteComparison

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_HomComplex_FullHomProductCoordinate
attribute [-instance] _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ArExplicit.CompleteComparison
open CategoryTheory CochainComplex CochainComplex.HomComplex
universe u w
variable {k : Type u} [Field k]
variable {C : Type w} [Category.{u} C] [Preadditive C] [Linear k C]
variable {K L M : CochainComplex C ℤ} {a b c d : ℤ}

theorem fullHomProduct_coordinate
    (h : a=b) (h₁ : b+c=d) (h₂ : a+c=d)
    {x : CohomologyClass K L a} {y : CohomologyClass K L b}
    {p : CohomologyClass L M c} {z : CohomologyClass K M d}
    (hy : y = TateKoszul.degreeEquiv (k := k) (CohomologyClass K L) h x)
    (hz : z = TateKoszul.degreeEquiv (k := k) (CohomologyClass K M) h₁ (fullHomProduct y p)) :
    z = TateKoszul.degreeEquiv (k := k) (CohomologyClass K M) h₂ (fullHomProduct x p) := by
  rw [hz, hy, fullHomProduct_reindex_left]

end ArExplicit.CompleteComparison

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Modules_InductionBimodule
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.TrivialInduction.quotientModule _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
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

instance instIsScalarTower : IsScalarTower k S (InductionBimodule ι) where
  smul_assoc a s x := by ext; exact smul_mul_assoc a s x.value

end InductionBimodule
end ArExplicit

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Tensor_ExternalTensorTransport
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
namespace ArExplicit.ExternalTensor
universe u
variable (k A B : Type u) [Field k] [Ring A] [Ring B] [Algebra k A] [Algebra k B]
attribute [local instance] moduleCatBaseModule moduleCatBaseTower
variable (h : A ≃ₐ[k] A) (j : B ≃ₐ[k] B)

local notation "F" => tensorRestriction k A B h j

variable (P : ChainComplex (ModuleCat.{u} A) ℕ) (Q : ChainComplex (ModuleCat.{u} B) ℕ)
variable (e : ∀ n, P.X n →ₗ[k] P.X n) (f : ∀ n, Q.X n →ₗ[k] Q.X n)
variable (he : ∀ n a x, e n (a • x) = h a • e n x)
variable (hf : ∀ n b x, f n (b • x) = j b • f n x)
def transportSummand (i j' : ℕ) : moduleObject k A B (P.X i) (Q.X j') ⟶
    (F).obj (moduleObject k A B (P.X i) (Q.X j')) :=
  ModuleCat.ofHom (X := moduleObject k A B (P.X i) (Q.X j'))
    (Y := (F).obj (moduleObject k A B (P.X i) (Q.X j')))
    (tensorSemilinear k A B h j (e i) (f j') (he i) (hf j'))

def transportTerm (n : ℕ) : (complex k A B P Q).X n ⟶
    (F).obj ((complex k A B P Q).X n) :=
  desc k A B P Q (fun i j' hij =>
    transportSummand k A B h j P Q e f he hf i j' ≫
      (F).map (inclusion k A B P Q i j' n hij))

@[reassoc] theorem inclusion_transportTerm (i j' n : ℕ) (hij : i+j'=n) :
    inclusion k A B P Q i j' n hij ≫ transportTerm k A B h j P Q e f he hf n =
      transportSummand k A B h j P Q e f he hf i j' ≫
        (F).map (inclusion k A B P Q i j' n hij) :=
  inclusion_desc k A B P Q _ i j' hij

end ArExplicit.ExternalTensor

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Triangular_TriangularRadical
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ArExplicit.Triangular

variable {R F : Type*} [Ring R] [AddCommGroup F]
variable [Module R F] [Module Rᵐᵒᵖ F] [SMulCommClass R Rᵐᵒᵖ F]

theorem radical_eq_comap :
    Ring.jacobson (Triangular R F) = Ideal.comap diagonal (Ring.jacobson (R × R)) := by
  apply jacobson_eq_comap_of_nil_kernel _ diagonal_surjective
  intro a ha
  refine ⟨2, ?_⟩
  have h := Ideal.pow_mem_pow ha 2
  simpa only [diagonal_kernel_square, Ideal.mem_bot] using h

theorem mem_jacobson_iff (a : Triangular R F) :
    a ∈ Ring.jacobson (Triangular R F) ↔
      a.top ∈ Ring.jacobson R ∧ a.bottom ∈ Ring.jacobson R := by
  rw [radical_eq_comap]
  exact mem_jacobson_prod_iff (a.top, a.bottom)

section Scalars

variable (k : Type*) [CommRing k] [Algebra k R] [Module k F]
variable [IsScalarTower k R F] [IsScalarTower k Rᵐᵒᵖ F]
variable [SMulCommClass k R F] [SMulCommClass k Rᵐᵒᵖ F]

variable {S : Type*} [Ring S] [Algebra k S]

theorem radical_eq_ker_quotientMap (f : R →ₐ[k] S)
    (hf : Ring.jacobson R = RingHom.ker f) :
    Ring.jacobson (Triangular R F) = RingHom.ker (quotientMap k f) := by
  ext a
  rw [mem_jacobson_iff, hf]
  change (f a.top = 0 ∧ f a.bottom = 0) ↔ (f a.top, f a.bottom) = (0, 0)
  simp only [Prod.mk.injEq]

end Scalars
end ArExplicit.Triangular

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Triangular_ConvertedStructure
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.Resolution.augmentation_epi _root_.OAI.ArExplicit.Resolution.complex_scalar _root_.OAI.ArExplicit.Resolution.instIsScalarTowerTSimple _root_.OAI.ArExplicit.Resolution.instModuleTSimple _root_.OAI.ArExplicit.Resolution.simpleRightAction _root_.OAI.ArExplicit.TrivialInduction.dualModule _root_.OAI.ArExplicit.TrivialInduction.quotientModule _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ArExplicit

namespace ConvertedAlgebra

variable {k : Type*} [Field k] (q : k) (F : Type*) [AddCommGroup F]
variable [Module (A k q) F] [Module (A k q)ᵐᵒᵖ F]
variable [SMulCommClass (A k q) (A k q)ᵐᵒᵖ F]

def radicalU : ConvertedAlgebra k q F := ⟨A.radicalU q, 0, 0⟩

def radicalT : ConvertedAlgebra k q F := ⟨A.radicalT q, 0, 0⟩

end ConvertedAlgebra
end ArExplicit

end OAI
end


