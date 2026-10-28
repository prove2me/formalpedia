-- Prove2me | Definitions.Def_OAIQ031A096
-- name    : OAIQ031A096
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T14:33:53.170211+00:00
-- url     : https://prove2.me/theorems/67c4292d-83cb-4ff0-b23e-687684dcb8d3
-- title:
--   Definitions bundle OAIQ031A096 of the split of OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.ArExplicit.Statement.main`, carved from OpenAI's openai/math development (OpenAI, *An explicit counterexample to the Auslander-Reiten conjecture (result family 199)*, OpenAI Math Release, September 23, 2026, result family 199, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 16 declarations of OpenAI's Lean: 4 definitions and 12 theorems. The definitions and types are `OAI.ArExplicit.AbsoluteBar.resolution`, `OAI.ArExplicit.BalancedTensor.cochainCokernelEquiv`, `OAI.ArExplicit.FrobeniusTrace.projectiveStableDuality`, `OAI.ArExplicit.TwoCone.skeletonTerm`.
--
--   **Sources.** They come from these modules of lean/OAI/Algebra, in whole or in part: [`AuslanderReiten_Bar_BarResolution`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Bar/BarResolution.lean), [`AuslanderReiten_Bar_TwistedBar`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Bar/TwistedBar.lean), [`AuslanderReiten_Complete_CompleteShiftDual`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Complete/CompleteShiftDual.lean), [`AuslanderReiten_Cones_CochainCokernelIso`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Cones/CochainCokernelIso.lean), [`AuslanderReiten_Cones_TwoConeSkeleton`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Cones/TwoConeSkeleton.lean), [`AuslanderReiten_Duality_ProjectiveStableDuality`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Duality/ProjectiveStableDuality.lean), [`AuslanderReiten_Duality_ProjectiveStablePairing`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Duality/ProjectiveStablePairing.lean), [`AuslanderReiten_Homology_ShortExactNaturality`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Homology/ShortExactNaturality.lean), [`AuslanderReiten_Tensor_BalancedTensorCokernel`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Tensor/BalancedTensorCokernel.lean), [`AuslanderReiten_Tensor_BalancedTensorComplete`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Tensor/BalancedTensorComplete.lean), [`AuslanderReiten_Tensor_BalancedTensorProjective`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Tensor/BalancedTensorProjective.lean).
--
--   **Imports.** It imports the bundles `OAIQ031A077`, `OAIQ031A078`, `OAIQ031A079`, `OAIQ031A080`, `OAIQ031A082` and `OAIQ031A083` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ031A107`, `OAIQ031A109`, `OAIQ031A110`, `OAIQ031A111`, `OAIQ031A113`, `OAIQ031A115`, `OAIQ031A117` and `OAIQ031A118`.
-- source:
--   OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 199; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/An-explicit-counterexample-to-the-Auslander-Reiten-conjecture-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algebra at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ031A077
import Definitions.Def_OAIQ031A078
import Definitions.Def_OAIQ031A079
import Definitions.Def_OAIQ031A080
import Definitions.Def_OAIQ031A082
import Definitions.Def_OAIQ031A083

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Bar_BarResolution
attribute [-instance] _root_.OAI.ArExplicit.AbsoluteBar.twistInvPair _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
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

def resolution : ProjectiveResolution (moduleObject k R 0) where
  complex := complex k R
  projective n := by
    let := projective k R n
    exact (moduleObject k R (n + 1)).projective_of_categoryTheory_projective
  π := augmentation k R
  quasiIso := ⟨fun n => by
    cases n with
    | zero =>
      rw [ChainComplex.quasiIsoAt₀_iff, ShortComplex.quasiIso_iff_of_zeros']
      · constructor
        · rw [ShortComplex.moduleCat_exact_iff_range_eq_ker]
          change LinearMap.range ((complex k R).d 1 0).hom =
            LinearMap.ker ((augmentation k R).f 0).hom
          rw [complex_d, augmentation_zero]
          exact differential_exact k R 0
        · rw [ModuleCat.epi_iff_surjective]
          intro x
          exact ⟨contraction k R 0 x, augmentation_contraction k R x⟩
      · change (complex k R).d 0 0 = 0
        exact (complex k R).shape _ _ (by simp)
      · rfl
      · rfl
    | succ n =>
      rw [quasiIsoAt_iff_exactAt']
      · exact complex_exactAt k R n
      · exact ChainComplex.exactAt_succ_single_obj _ _⟩

end ArExplicit.AbsoluteBar

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Bar_TwistedBar
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory
open scoped TensorProduct
namespace ArExplicit.AbsoluteBar
universe u
variable (k R : Type u) [Field k] [Ring R] [Algebra k R]

variable [CharP k 2]

theorem twistedDifferential_exact (h : R ≃ₐ[k] R) (n : ℕ) :
    LinearMap.range (twistedDifferential k R h (n + 1)) =
      LinearMap.ker (twistedDifferential k R h n) := by
  ext x
  change (∃ y, boundary k R (n + 1) y = x) ↔ boundary k R n x = 0
  exact SetLike.ext_iff.mp (boundary_exact k R n) x

theorem twistedComplex_exactAt (h : R ≃ₐ[k] R) (n : ℕ) :
    (twistedComplex k R h).ExactAt (n + 1) := by
  rw [HomologicalComplex.exactAt_iff' _ (n + 2) (n + 1) n (by simp) (by simp)]
  rw [ShortComplex.moduleCat_exact_iff_range_eq_ker]
  change LinearMap.range ((twistedComplex k R h).d (n + 1 + 1) (n + 1)).hom =
    LinearMap.ker ((twistedComplex k R h).d (n + 1) n).hom
  rw [twistedComplex_d, twistedComplex_d]
  exact twistedDifferential_exact k R h (n + 1)

end ArExplicit.AbsoluteBar

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Complete_CompleteShiftDual
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open CategoryTheory

namespace ArExplicit

universe u

variable {R : Type u} [Ring R]

namespace TotallyAcyclicCochain

open CompleteComparison

theorem of_chain {K : CochainComplex (ModuleCat.{u} R) ℤ}
    (hK : TotallyAcyclicComplex (chainOfCochain K)) : TotallyAcyclicCochain K where
  toExactProjectiveCochain := ExactProjectiveCochain.of_chain hK.toExactProjectiveComplex
  dualExact := DualExactCochain.of_chain hK

end TotallyAcyclicCochain

end ArExplicit

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Homology_ShortExactNaturality
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory HomologicalComplex
open CochainComplex CochainComplex.HomComplex

namespace ArExplicit
open CompleteComparison

universe u
variable {R : Type u} [Ring R]

namespace CompleteComparison
variable {K L M : CochainComplex (ModuleCat.{u} R) ℤ}

theorem cochainHomotopyRawEquiv_comp
    (hK : TotallyAcyclicCochain K) (hL : TotallyAcyclicCochain L)
    (hM : ExactProjectiveCochain M)
    (f : (HomotopyCategory.quotient _ _).obj K ⟶ (HomotopyCategory.quotient _ _).obj L)
    (g : (HomotopyCategory.quotient _ _).obj L ⟶ (HomotopyCategory.quotient _ _).obj M) :
    cochainHomotopyRawEquiv hK.to_chain hM.to_chain (f ≫ g) =
      StableHom.comp (cochainHomotopyRawEquiv hL.to_chain hM.to_chain g)
        (cochainHomotopyRawEquiv hK.to_chain hL.to_chain.toExactProjectiveComplex f) := by
  obtain ⟨f, rfl⟩ := (HomotopyCategory.quotient (ModuleCat.{u} R) (ComplexShape.up ℤ)).map_surjective f
  obtain ⟨g, rfl⟩ := (HomotopyCategory.quotient (ModuleCat.{u} R) (ComplexShape.up ℤ)).map_surjective g
  rw [← Functor.map_comp, cochainHomotopyRawEquiv_map, cochainHomotopyRawEquiv_map,
    cochainHomotopyRawEquiv_map, cochainCokernelMap_comp, StableHom.comp_classOf]

end CompleteComparison

end ArExplicit

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Cones_CochainCokernelIso
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ArExplicit.CompleteComparison
open CategoryTheory
universe u
variable {R : Type u} [Ring R]
variable {K L : CochainComplex (ModuleCat.{u} R) ℤ}

theorem rawEquiv_identity (hK : TotallyAcyclicCochain K) :
    cochainHomotopyRawEquiv hK.to_chain hK.to_chain.toExactProjectiveComplex (𝟙 _) =
      StableHom.identity := by
  rw [← (HomotopyCategory.quotient _ _).map_id, cochainHomotopyRawEquiv_map]
  congr 1
  apply LinearMap.ext
  intro z
  obtain ⟨z,rfl⟩ := Submodule.mkQ_surjective (LinearMap.range (K.d (-1) 0).hom) z
  rfl

end ArExplicit.CompleteComparison

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Cones_TwoConeSkeleton
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
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

abbrev skeletonTerm (n : ℕ) : ModuleCat.{u} R := ModuleCat.of R (D.term n × middleTerm D n)

end ArExplicit.TwoCone

end

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

noncomputable def projectiveStableDuality
    (e : P₁ →ₗ[R] P₀) (d : P₀ →ₗ[R] Pminus) (h : d.comp e = 0)
    (hex : LinearMap.range e = LinearMap.ker d) :
    Module.Dual k (StableHom R (StableHomology.Cokernel e) N) ≃ₗ[k]
      StableHom R N (LinearMap.ker d) := by
  letI : Module.Injective R R := τ.regular_injective
  let hd : HomExactAt e d := homExactAt_of_injective e d hex
  exact (StableHomology.homologyStableEquiv e d h hd).dualMap |>.trans
    ((τ.projectiveHomHomologyDuality hs e d h).trans
      (StableTargetHomology.homologyStableEquiv e d h hex))

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

theorem projectiveStableDuality_symm_cycles (hex : LinearMap.range e = LinearMap.ker d)
    (z : LinearMap.ker (StableTargetHomology.postcomp (k := k) (N := N) d))
    (x : LinearMap.ker (StableHomology.precomp (k := k) (N := N) e)) :
    ((τ.projectiveStableDuality (N := N) hs e d h hex).symm (StableTargetHomology.cyclesToStable d z))
      (StableHomology.cyclesToStable e x) =
    (τ.projectiveHomDualEquiv hs).symm z.val x.val := by
  let : Module.Injective R R := τ.regular_injective
  let hd : HomExactAt e d := homExactAt_of_injective e d hex
  let qx : LinearHomology.Homology (StableHomology.precomp d)
    (StableHomology.precomp e) (StableHomology.precomp_comp e d h) := Submodule.Quotient.mk x
  let qz : LinearHomology.Homology (StableTargetHomology.postcomp e)
    (StableTargetHomology.postcomp d) (StableTargetHomology.postcomp_comp e d h) := Submodule.Quotient.mk z
  have hx : StableHomology.homologyStableEquiv e d h hd qx =
      StableHomology.cyclesToStable e x := StableHomology.homologyStableEquiv_mk e d h hd x
  have hz : StableTargetHomology.homologyStableEquiv e d h hex qz =
      StableTargetHomology.cyclesToStable d z :=
    StableTargetHomology.homologyStableEquiv_mk e d h hex z
  rw [← hx, ← hz]
  unfold projectiveStableDuality
  simp only [LinearEquiv.trans_symm, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply]
  change ((τ.projectiveHomHomologyDuality hs e d h).symm qz)
    ((StableHomology.homologyStableEquiv e d h hd).symm
      ((StableHomology.homologyStableEquiv e d h hd) qx)) = _
  rw [LinearEquiv.symm_apply_apply]
  exact τ.projectiveHomHomologyDuality_symm_apply hs e d h z x

theorem projectiveStableDuality_symm_apply (hex : LinearMap.range e = LinearMap.ker d)
    (f : StableHomology.Cokernel e →ₗ[R] N) (g : N →ₗ[R] LinearMap.ker d) :
    ((τ.projectiveStableDuality (N := N) hs e d h hex).symm (StableHom.classOf R _ _ g))
      (StableHom.classOf R _ _ f) =
    (τ.projectiveHomDualEquiv hs).symm ((LinearMap.ker d).subtype.comp g)
      (f.comp (LinearMap.range e).mkQ) := by
  have H := τ.projectiveStableDuality_symm_cycles hs e d h hex
    (StableTargetHomology.mapToCycle d g) (StableHomology.mapToCycle e f)
  rw [StableTargetHomology.cyclesToStable_mapToCycle,
    StableHomology.cyclesToStable_mapToCycle] at H
  simpa only [StableTargetHomology.mapToCycle, StableHomology.mapToCycle] using H

end ArExplicit.FrobeniusTrace

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Tensor_BalancedTensorProjective
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.EnvelopingBimodule.regular_projective _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ArExplicit.BalancedTensor

variable {k R S F M : Type*} [CommRing k] [Ring R] [Ring S] [Algebra k R]
variable [AddCommGroup F] [Module k F] [Module Rᵐᵒᵖ F] [Module S F]
variable [SMulCommClass k S F] [SMulCommClass S Rᵐᵒᵖ F]
variable [IsScalarTower k Rᵐᵒᵖ F]
variable [AddCommGroup M] [Module k M] [Module R M] [IsScalarTower k R M]

theorem finite [Module.Finite S F] [Module.Finite R M] :
    Module.Finite S (BalancedTensor k R F M) := by
  obtain ⟨n, p, hp⟩ := Module.Finite.exists_fin' R M
  let : Module.Finite S (BalancedTensor k R F R) :=
    Module.Finite.equiv (runitLeft (k := k) (R := R) (S := S) (F := F)).symm
  let : Module.Finite S (BalancedTensor k R F (Fin n → R)) :=
    Module.Finite.equiv (piRight (k := k) (R := R) (S := S) (F := F) (M := R)).symm
  exact Module.Finite.of_surjective (mapRight (k := k) (S := S) p) (mapRight_surjective p hp)

end ArExplicit.BalancedTensor

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Tensor_BalancedTensorCokernel
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.EnvelopingBimodule.regular_projective _root_.OAI.ArExplicit.ExternalTensor.hasHomCochainTotal _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
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

@[simp] theorem cokernelEquiv_mk_tmul (d : L →ₗ[R] M) (f : F) (m : M) :
    cokernelEquiv (k := k) (F := F) (S := S) d (Submodule.Quotient.mk (tmul f m)) =
      tmul f (Submodule.Quotient.mk m) := by
  rw [cokernelEquiv_mk, mapRight_tmul]
  rfl

attribute [local instance] moduleCatBaseModule moduleCatBaseTower

def cochainCokernelEquiv (P : CochainComplex (ModuleCat.{u} R) ℤ) :
    CochainCokernel (((functor (k := k) (R := R) (S := S) (F := F)).mapHomologicalComplex _).obj P) ≃ₗ[S]
      BalancedTensor k R F (CochainCokernel P) :=
  cokernelEquiv (k := k) (F := F) (S := S) (P.d (-1) 0).hom

@[simp] theorem cochainCokernelEquiv_mk_tmul
    (P : CochainComplex (ModuleCat.{u} R) ℤ) (f : F) (x : P.X 0) :
    cochainCokernelEquiv (k := k) (F := F) (S := S) P
      (Submodule.Quotient.mk (tmul f x)) = tmul f (Submodule.Quotient.mk x) :=
  cokernelEquiv_mk_tmul (k := k) (F := F) (S := S) (P.d (-1) 0).hom f x

end ArExplicit.BalancedTensor

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Tensor_BalancedTensorComplete
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.EnvelopingBimodule.regular_projective _root_.OAI.ArExplicit.ExternalTensor.hasHomCochainTotal _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ArExplicit.BalancedTensor
open CategoryTheory
universe u
variable {k R S F : Type u} [Field k] [Ring R] [Ring S] [Algebra k R]
variable [AddCommGroup F] [Module k F] [Module Rᵐᵒᵖ F] [Module S F]
variable [IsScalarTower k Rᵐᵒᵖ F]
variable [SMulCommClass k S F] [SMulCommClass S Rᵐᵒᵖ F]
variable [Module.Finite Rᵐᵒᵖ F] [Module.Projective Rᵐᵒᵖ F]
variable [Module.Finite S F] [Module.Projective S F]
attribute [local instance] moduleCatBaseModule moduleCatBaseTower

theorem complex_exactProjective (P : CochainComplex (ModuleCat.{u} R) ℤ)
    (hP : ExactProjectiveCochain P) :
    ExactProjectiveCochain
      (((functor (k := k) (R := R) (S := S) (F := F)).mapHomologicalComplex _).obj P) where
  finite n := by
    let := hP.finite n
    exact finite
  projective n := by
    let := hP.finite n
    let := hP.projective n
    exact projective
  exactAt n := by
    rw [HomologicalComplex.exactAt_iff' _ (n-1) n (n+1) (by simp) (by simp),
      ShortComplex.moduleCat_exact_iff_range_eq_ker]
    have he := hP.exactAt n
    rw [HomologicalComplex.exactAt_iff' _ (n-1) n (n+1) (by simp) (by simp),
      ShortComplex.moduleCat_exact_iff_range_eq_ker] at he
    exact (LinearMap.exact_iff.mp
      (mapRight_exact (k := k) (F := F) (S := S) _ _
        (LinearMap.exact_iff.mpr he.symm))).symm

theorem complex_totallyAcyclic [Module.Injective S S]
    (P : CochainComplex (ModuleCat.{u} R) ℤ) (hP : ExactProjectiveCochain P) :
    TotallyAcyclicCochain
      (((functor (k := k) (R := R) (S := S) (F := F)).mapHomologicalComplex _).obj P) :=
  TotallyAcyclicCochain.of_chain
    (complex_exactProjective (k := k) (F := F) (S := S) P hP).to_chain.totallyAcyclic

end ArExplicit.BalancedTensor

end

end OAI
end


