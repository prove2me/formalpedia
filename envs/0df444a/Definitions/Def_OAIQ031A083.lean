-- Prove2me | Definitions.Def_OAIQ031A083
-- name    : OAIQ031A083
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T14:23:28.969267+00:00
-- url     : https://prove2.me/theorems/2c853745-da59-43b9-b88b-84eac840a185
-- title:
--   Definitions bundle OAIQ031A083 of the split of OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.ArExplicit.Statement.main`, carved from OpenAI's openai/math development (OpenAI, *An explicit counterexample to the Auslander-Reiten conjecture (result family 199)*, OpenAI Math Release, September 23, 2026, result family 199, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 16 declarations of OpenAI's Lean: 4 definitions and 12 theorems. The definitions and types are `OAI.ArExplicit.BalancedTensor.cokernelEquiv`, `OAI.ArExplicit.FrobeniusTrace.presentationHomDualEquiv`, `OAI.ArExplicit.FrobeniusTrace.projectiveHomDualEquiv`, `OAI.ArExplicit.FrobeniusTrace.projectiveHomHomologyDuality`.
--
--   **Sources.** They come from these modules of lean/OAI/Algebra, in whole or in part: [`AuslanderReiten_Bar_BarProjective`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Bar/BarProjective.lean), [`AuslanderReiten_Bar_BarResolution`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Bar/BarResolution.lean), [`AuslanderReiten_Bar_TCasimirEvaluation`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Bar/TCasimirEvaluation.lean), [`AuslanderReiten_Bar_TCasimirSquare`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Bar/TCasimirSquare.lean), [`AuslanderReiten_Duality_ProjectiveStableDuality`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Duality/ProjectiveStableDuality.lean), [`AuslanderReiten_Duality_ProjectiveStablePairing`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Duality/ProjectiveStablePairing.lean), [`AuslanderReiten_Duality_ProjectiveTraceDuality`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Duality/ProjectiveTraceDuality.lean), [`AuslanderReiten_Duality_SymmetricHomology`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Duality/SymmetricHomology.lean), [`AuslanderReiten_Evaluation_TensorBetaEvaluation`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Evaluation/TensorBetaEvaluation.lean), [`AuslanderReiten_Tensor_BalancedTensorCokernel`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Tensor/BalancedTensorCokernel.lean), [`AuslanderReiten_Tensor_ExternalTensorScalarProducts`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Tensor/ExternalTensorScalarProducts.lean).
--
--   **Imports.** It imports the bundles `OAIQ031A062`, `OAIQ031A063`, `OAIQ031A064`, `OAIQ031A067`, `OAIQ031A068` and `OAIQ031A069` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ031A096` and `OAIQ031A102`.
-- source:
--   OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 199; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/An-explicit-counterexample-to-the-Auslander-Reiten-conjecture-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algebra at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ031A062
import Definitions.Def_OAIQ031A063
import Definitions.Def_OAIQ031A064
import Definitions.Def_OAIQ031A067
import Definitions.Def_OAIQ031A068
import Definitions.Def_OAIQ031A069

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Bar_BarProjective
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct
namespace ArExplicit.AbsoluteBar
universe u
variable (k R : Type u) [Field k] [Ring R] [Algebra k R]

theorem finite [Module.Finite k R] (n : ℕ) :
    Module.Finite (Enveloping k R) (moduleObject k R (n + 1)) := by
  let : Module.Finite k (moduleObject k R (n + 1)) := finiteBase k R (n + 1)
  exact Module.Finite.of_restrictScalars_finite k (Enveloping k R) _

end ArExplicit.AbsoluteBar

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Bar_BarResolution
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory
namespace ArExplicit.AbsoluteBar
universe u
variable (k R : Type u) [Field k] [Ring R] [Algebra k R] [CharP k 2]

theorem complex_exactAt (n : ℕ) : (complex k R).ExactAt (n + 1) := by
  rw [HomologicalComplex.exactAt_iff' _ (n + 2) (n + 1) n (by simp) (by simp)]
  rw [ShortComplex.moduleCat_exact_iff_range_eq_ker]
  change LinearMap.range ((complex k R).d (n + 1 + 1) (n + 1)).hom =
    LinearMap.ker ((complex k R).d (n + 1) n).hom
  rw [complex_d, complex_d]
  exact differential_exact k R (n + 1)

end ArExplicit.AbsoluteBar

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Bar_TCasimirEvaluation
attribute [-instance] _root_.OAI.ArExplicit.A.instIsTwoSidedAugmentationIdeal _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.Resolution.instIsScalarTowerMulOppositeBaseAlgebraSimple _root_.OAI.ArExplicit.Resolution.simpleRightAction _root_.OAI.ArExplicit.Resolution.simpleRightModule _root_.OAI.ArExplicit.TrivialInduction.dualModule _root_.OAI.ArExplicit.TrivialInduction.instAdditiveModuleCatTrivialExtensionInflate _root_.OAI.ArExplicit.TrivialInduction.instIsScalarTowerTrivialExtensionCoinduced _root_.OAI.ArExplicit.TrivialInduction.instPreservesHomologyModuleCatTrivialExtensionInflate _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionCoinduced _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionMulOppositeCoinduced _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionMulOppositeQuotient _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionQuotient _root_.OAI.ArExplicit.TrivialInduction.quotientModule _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct

namespace ArExplicit.T

variable {k : Type*} [Field k] (q : k)
local notation "R" => T k q
local notation "S" => Resolution.Simple q

theorem twistedCasimir_evaluation (H : kˣ) (hq1 : 1 + q ≠ 0) (s : S) :
    evaluateAtSimple q s (twistedCasimir q H) = ((H : k) • upper q .f) ⊗ₜ[k] s := by
  simp only [evaluateAtSimple, twistedCasimir, map_sum, TensorProduct.map_tmul,
    LinearMap.id_apply, simpleActionAt_apply, CocycleData.vector_smul_simple q hq1]
  rw [Finset.sum_eq_single (true, .f)]
  · have ht := CocycleData.twist_vector q H (true, .f)
    simp only [TIndex.weight, reduceIte, pow_one, vector] at ht
    simpa [TIndex.star, vector] using! congrArg (fun a : R => a ⊗ₜ[k] s) ht
  · intro i _ hi
    have hn : TIndex.star i ≠ (false, Letter.f) := by
      intro he
      have hh := congrArg TIndex.star he
      simp only [star_star] at hh
      exact hi hh
    simp [hn]
  · simp

end ArExplicit.T

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Bar_TCasimirSquare
attribute [-instance] _root_.OAI.ArExplicit.A.instIsTwoSidedAugmentationIdeal _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.Resolution.instIsScalarTowerMulOppositeBaseAlgebraSimple _root_.OAI.ArExplicit.Resolution.simpleRightAction _root_.OAI.ArExplicit.Resolution.simpleRightModule _root_.OAI.ArExplicit.TrivialInduction.dualModule _root_.OAI.ArExplicit.TrivialInduction.instAdditiveModuleCatTrivialExtensionInflate _root_.OAI.ArExplicit.TrivialInduction.instIsScalarTowerTrivialExtensionCoinduced _root_.OAI.ArExplicit.TrivialInduction.instPreservesHomologyModuleCatTrivialExtensionInflate _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionCoinduced _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionMulOppositeCoinduced _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionMulOppositeQuotient _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionQuotient _root_.OAI.ArExplicit.TrivialInduction.quotientModule _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct

namespace ArExplicit.T

variable {k : Type*} [Field k] (q : k)
local notation "S" => Resolution.Simple q

theorem twistedCasimir_square_evaluation (H : kˣ) (hq1 : 1 + q ≠ 0) (s t : S) :
    squareEvaluation q s t (twistedCasimir q H ⊗ₜ[k] twistedCasimir q H) =
      ((H : k)^2 • (upper q .f ⊗ₜ[k] upper q .f)) ⊗ₜ[k] (s ⊗ₜ[k] t) := by
  simp only [squareEvaluation, LinearMap.comp_apply, TensorProduct.map_tmul,
    twistedCasimir_evaluation q H hq1, LinearEquiv.coe_coe,
    TensorProduct.tensorTensorTensorComm_tmul]
  simp only [TensorProduct.smul_tmul', TensorProduct.tmul_smul, smul_smul, pow_two]

end ArExplicit.T

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Duality_SymmetricHomology
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ArExplicit.FrobeniusTrace

universe u

variable {k R : Type u} [Field k] [Ring R] [Algebra k R] [Module.Finite k R]
variable (τ : FrobeniusTrace k R)
variable {N : Type u} [AddCommGroup N] [Module R N] [Module k N]
variable [IsScalarTower k R N] [SMulCommClass R k N]
variable (hs : ∀ a b : R, τ.trace (a * b) = τ.trace (b * a))

include hs in

theorem freeHomDual_precomp {r s : ℕ} (a : (Fin r → R) →ₗ[R] (Fin s → R))
    (φ : Module.Dual k ((Fin r → R) →ₗ[R] N)) :
    τ.freeHomDualEquiv s ((StableHomology.precomp (k := k) a).dualMap φ) =
      a.comp (τ.freeHomDualEquiv r φ) := by
  apply (τ.freeHomDualEquiv s).symm.injective
  rw [LinearEquiv.symm_apply_apply]
  ext f
  change φ (f.comp a) = (τ.freeHomDualEquiv s).symm (a.comp (τ.freeHomDualEquiv r φ)) f
  rw [← τ.freeHomDual_naturality_source hs]
  rw [LinearEquiv.symm_apply_apply]

end ArExplicit.FrobeniusTrace

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Duality_ProjectiveTraceDuality
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ArExplicit

universe u

variable (R P : Type u) [Ring R] [AddCommGroup P] [Module R P]

namespace FrobeniusTrace

variable {k R : Type u} [Field k] [Ring R] [Algebra k R] [Module.Finite k R]
variable (τ : FrobeniusTrace k R)
variable (hs : ∀ a b : R, τ.trace (a * b) = τ.trace (b * a))
variable {P Q N : Type u}
variable [AddCommGroup P] [Module R P] [Module k P] [IsScalarTower k R P]
variable [AddCommGroup Q] [Module R Q] [Module k Q] [IsScalarTower k R Q]
variable [AddCommGroup N] [Module R N] [Module k N] [IsScalarTower k R N]
variable [SMulCommClass R k N]

noncomputable def presentationHomDualEquiv (F : FiniteProjectivePresentation R P) :
    Module.Dual k (P →ₗ[R] N) ≃ₗ[k] (N →ₗ[R] P) :=
  linearRetractEquiv
    (StableHomology.precomp (k := k) F.inclusion).dualMap
    (StableHomology.precomp (k := k) F.projection).dualMap (by
      ext φ f
      change φ ((f.comp F.projection).comp F.inclusion) = φ f
      congr 1
      ext x
      exact congrArg f (F.split_apply x))
    (StableTargetHomology.postcomp (k := k) F.inclusion)
    (StableTargetHomology.postcomp (k := k) F.projection) (by
      ext g x
      exact F.split_apply (g x))
    (τ.freeHomDualEquiv F.rank) (by
      intro φ
      exact τ.freeHomDual_precomp hs (F.inclusion.comp F.projection) φ)

theorem presentationHomDualEquiv_symm_apply (F : FiniteProjectivePresentation R P)
    (g : N →ₗ[R] P) (f : P →ₗ[R] N) :
    (τ.presentationHomDualEquiv hs F).symm g f =
      (τ.freeHomDualEquiv F.rank).symm (F.inclusion.comp g) (f.comp F.projection) := rfl

theorem presentationHomDual_naturality_source
    (F : FiniteProjectivePresentation R P) (G : FiniteProjectivePresentation R Q)
    (a : P →ₗ[R] Q) (f : Q →ₗ[R] N) (g : N →ₗ[R] P) :
    (τ.presentationHomDualEquiv hs F).symm g (f.comp a) =
      (τ.presentationHomDualEquiv hs G).symm (a.comp g) f := by
  rw [presentationHomDualEquiv_symm_apply, presentationHomDualEquiv_symm_apply]
  let A := G.inclusion.comp (a.comp F.projection)
  have H := τ.freeHomDual_naturality_source hs A (f.comp G.projection) (F.inclusion.comp g)
  have hleft : (f.comp G.projection).comp A = (f.comp a).comp F.projection := by
    apply LinearMap.ext
    intro x
    exact congrArg f (G.split_apply (a (F.projection x)))
  have hright : A.comp (F.inclusion.comp g) = G.inclusion.comp (a.comp g) := by
    apply LinearMap.ext
    intro x
    exact congrArg (fun p => G.inclusion (a p)) (F.split_apply (g x))
  rw [hleft, hright] at H
  exact H

noncomputable def projectiveHomDualEquiv [Module.Finite R P] [Module.Projective R P] :
    Module.Dual k (P →ₗ[R] N) ≃ₗ[k] (N →ₗ[R] P) :=
  τ.presentationHomDualEquiv hs (FiniteProjectivePresentation.choose R P)

theorem projectiveHomDual_precomp [Module.Finite R P] [Module.Projective R P]
    [Module.Finite R Q] [Module.Projective R Q] (a : P →ₗ[R] Q)
    (φ : Module.Dual k (P →ₗ[R] N)) :
    τ.projectiveHomDualEquiv hs ((StableHomology.precomp (k := k) a).dualMap φ) =
      a.comp (τ.projectiveHomDualEquiv hs φ) := by
  apply (τ.projectiveHomDualEquiv hs (P := Q) (N := N)).symm.injective
  rw [LinearEquiv.symm_apply_apply]
  ext f
  change φ (f.comp a) =
    (τ.presentationHomDualEquiv hs (FiniteProjectivePresentation.choose R Q)).symm
      (a.comp (τ.projectiveHomDualEquiv hs φ)) f
  rw [← τ.presentationHomDual_naturality_source hs
    (FiniteProjectivePresentation.choose R P)]
  exact (congrArg (fun ψ : Module.Dual k (P →ₗ[R] N) => ψ (f.comp a))
    ((τ.projectiveHomDualEquiv hs).symm_apply_apply φ)).symm

end FrobeniusTrace
end ArExplicit

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Duality_ProjectiveStableDuality
attribute [-instance] _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ArExplicit.FrobeniusTrace

universe u

variable {k R : Type u} [Field k] [Ring R] [Algebra k R] [Module.Finite k R]
variable (τ : FrobeniusTrace k R)
variable (hs : ∀ a b : R, τ.trace (a * b) = τ.trace (b * a))
variable {P₁ P₀ Pminus N : Type u}
variable [AddCommGroup P₁] [Module R P₁] [Module k P₁] [IsScalarTower k R P₁]
variable [AddCommGroup P₀] [Module R P₀] [Module k P₀] [IsScalarTower k R P₀]
variable [AddCommGroup Pminus] [Module R Pminus] [Module k Pminus] [IsScalarTower k R Pminus]
variable [AddCommGroup N] [Module R N] [Module k N] [IsScalarTower k R N]
variable [SMulCommClass R k N]
variable [Module.Finite R P₁] [Module.Projective R P₁]
variable [Module.Finite R P₀] [Module.Projective R P₀]
variable [Module.Finite R Pminus] [Module.Projective R Pminus]

noncomputable def projectiveHomHomologyDuality
    (e : P₁ →ₗ[R] P₀) (d : P₀ →ₗ[R] Pminus) (h : d.comp e = 0) :
    Module.Dual k (LinearHomology.Homology
      (StableHomology.precomp (k := k) (N := N) d)
      (StableHomology.precomp e) (StableHomology.precomp_comp e d h)) ≃ₗ[k]
    LinearHomology.Homology
      (StableTargetHomology.postcomp (k := k) (N := N) e)
      (StableTargetHomology.postcomp d) (StableTargetHomology.postcomp_comp e d h) :=
  (LinearHomology.dualHomologyEquiv _ _ _).trans
    (LinearHomology.congr _ _ _ _ _ _
      (τ.projectiveHomDualEquiv hs) (τ.projectiveHomDualEquiv hs) (τ.projectiveHomDualEquiv hs)
      (τ.projectiveHomDual_precomp hs e) (τ.projectiveHomDual_precomp hs d))

open scoped ModuleCat.Algebra
open CompleteComparison

end ArExplicit.FrobeniusTrace

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Duality_ProjectiveStablePairing
attribute [-instance] _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ArExplicit.FrobeniusTrace

universe u

variable {k R : Type u} [Field k] [Ring R] [Algebra k R] [Module.Finite k R]
variable (τ : FrobeniusTrace k R)
variable {N : Type u} [AddCommGroup N] [Module R N] [Module k N]
variable [IsScalarTower k R N] [SMulCommClass R k N]
variable (hs : ∀ a b : R, τ.trace (a * b) = τ.trace (b * a))
variable {P₁ P₀ Pminus : Type u}
variable [AddCommGroup P₁] [Module R P₁] [Module k P₁] [IsScalarTower k R P₁]
variable [AddCommGroup P₀] [Module R P₀] [Module k P₀] [IsScalarTower k R P₀]
variable [AddCommGroup Pminus] [Module R Pminus] [Module k Pminus] [IsScalarTower k R Pminus]
variable [Module.Finite R P₁] [Module.Projective R P₁]
variable [Module.Finite R P₀] [Module.Projective R P₀]
variable [Module.Finite R Pminus] [Module.Projective R Pminus]
variable (e : P₁ →ₗ[R] P₀) (d : P₀ →ₗ[R] Pminus) (h : d.comp e = 0)

theorem projectiveHomHomologyDuality_symm_apply
    (z : LinearMap.ker (StableTargetHomology.postcomp (k := k) (N := N) d))
    (x : LinearMap.ker (StableHomology.precomp (k := k) (N := N) e)) :
    ((τ.projectiveHomHomologyDuality hs e d h).symm
      (Submodule.Quotient.mk z)) (Submodule.Quotient.mk x) =
    (τ.projectiveHomDualEquiv hs).symm z.val x.val := by
  simp only [projectiveHomHomologyDuality, LinearEquiv.trans_symm, LinearEquiv.trans_apply]
  rfl

end ArExplicit.FrobeniusTrace

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Evaluation_TensorBetaEvaluation
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.Resolution.instIsScalarTowerMulOppositeBaseAlgebraSimple _root_.OAI.ArExplicit.Resolution.simpleRightAction _root_.OAI.ArExplicit.Resolution.simpleRightModule _root_.OAI.ArExplicit.TrivialInduction.dualModule _root_.OAI.ArExplicit.TrivialInduction.instAdditiveModuleCatTrivialExtensionInflate _root_.OAI.ArExplicit.TrivialInduction.instIsScalarTowerTrivialExtensionCoinduced _root_.OAI.ArExplicit.TrivialInduction.instPreservesHomologyModuleCatTrivialExtensionInflate _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionCoinduced _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionMulOppositeCoinduced _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionMulOppositeQuotient _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionQuotient _root_.OAI.ArExplicit.TrivialInduction.quotientModule _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct

namespace ArExplicit.A

variable {k : Type*} [Field k] (q : k)

theorem squareEvaluation_eq_beta (H : kˣ) (hq1 : 1 + q ≠ 0)
    (s t : Resolution.Simple q) :
    barZeroCoordinate q
      (T.squareEvaluation q s t (T.twistedCasimir q H ⊗ₜ[k] T.twistedCasimir q H)) =
      (H : k)^2 • socleMap q (s ⊗ₜ[k] t) := by
  rw [T.twistedCasimir_square_evaluation q H hq1]
  simp [barZeroCoordinate, simpleCoordinate, socleMap_tmul, T.socleMap, TensorProduct.smul_tmul', TensorProduct.tmul_smul,
    smul_smul, mul_comm]

end ArExplicit.A

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Tensor_BalancedTensorCokernel
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.EnvelopingBimodule.regular_projective _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ArExplicit.BalancedTensor
open CategoryTheory CompleteComparison
universe u
variable {k R S F : Type u} [Field k] [Ring R] [Ring S] [Algebra k R]
variable [AddCommGroup F] [Module k F] [Module Rᵐᵒᵖ F] [Module S F]
variable [IsScalarTower k Rᵐᵒᵖ F]
variable [SMulCommClass k S F] [SMulCommClass S Rᵐᵒᵖ F]
variable [Module.Finite Rᵐᵒᵖ F] [Module.Projective Rᵐᵒᵖ F]
variable {L M : Type u} [AddCommGroup L] [AddCommGroup M]
variable [Module k L] [Module k M] [Module R L] [Module R M]
variable [IsScalarTower k R L] [IsScalarTower k R M]
variable [SMulCommClass k R M]

def cokernelEquiv (d : L →ₗ[R] M) :
    (BalancedTensor k R F M ⧸ LinearMap.range (mapRight (k := k) (F := F) (S := S) d)) ≃ₗ[S]
      BalancedTensor k R F (M ⧸ LinearMap.range d) :=
  (mapRight_exact (k := k) (F := F) (S := S) d (LinearMap.range d).mkQ
    (LinearMap.exact_map_mkQ_range d)).linearEquivOfSurjective
      (mapRight_surjective (k := k) (F := F) (S := S) _ (Submodule.mkQ_surjective _))

theorem cokernelEquiv_mk (d : L →ₗ[R] M) (x : BalancedTensor k R F M) :
    cokernelEquiv (k := k) (F := F) (S := S) d (Submodule.Quotient.mk x) =
      mapRight (k := k) (F := F) (S := S) (LinearMap.range d).mkQ x := by
  apply (cokernelEquiv (k := k) (F := F) (S := S) d).symm.injective
  rw [LinearEquiv.symm_apply_apply]
  exact (Function.Exact.linearEquivOfSurjective_symm_apply _ _ x).symm

attribute [local instance] moduleCatBaseModule moduleCatBaseTower

end ArExplicit.BalancedTensor

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Tensor_ExternalTensorScalarProducts
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ExternalTensor.freeFree _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
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

theorem selfExtScalarEquiv_symm_comp {i j n : ℕ}
    (x : Ext (canonicalTensorObject k A B M N) (canonicalTensorObject k A B M N) i)
    (y : Ext (canonicalTensorObject k A B M N) (canonicalTensorObject k A B M N) j) (h : i+j=n) :
    (selfExtScalarEquiv k A B M N n).symm (x.comp y h) =
      ((selfExtScalarEquiv k A B M N i).symm x).comp ((selfExtScalarEquiv k A B M N j).symm y) h := by
  apply (selfExtScalarEquiv k A B M N n).injective
  rw [selfExtScalarEquiv_comp]
  simp

end ArExplicit.ExternalTensor

end

end OAI
end


