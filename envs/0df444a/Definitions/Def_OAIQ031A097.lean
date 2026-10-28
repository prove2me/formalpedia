-- Prove2me | Definitions.Def_OAIQ031A097
-- name    : OAIQ031A097
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T14:35:10.565608+00:00
-- url     : https://prove2.me/theorems/98a06bce-adac-4d14-bddc-3f6e3ac3ec71
-- title:
--   Definitions bundle OAIQ031A097 of the split of OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.ArExplicit.Statement.main`, carved from OpenAI's openai/math development (OpenAI, *An explicit counterexample to the Auslander-Reiten conjecture (result family 199)*, OpenAI Math Release, September 23, 2026, result family 199, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 25 declarations of OpenAI's Lean: 13 definitions and 12 theorems. The definitions and types are `OAI.ArExplicit.BarBalanced.canonicalEquiv`, `OAI.ArExplicit.BarBalanced.canonicalEvaluated`, `OAI.ArExplicit.BarBalanced.canonicalObject`, `OAI.ArExplicit.BarBalanced.canonicalTransport`, `OAI.ArExplicit.BarBalanced.equiv`, `OAI.ArExplicit.BarBalanced.nativeElement`, `OAI.ArExplicit.BarBalanced.nativeObject`, `OAI.ArExplicit.BarBalanced.scalarEvaluatedElement`, `OAI.ArExplicit.BarBalanced.scalarEvaluatedObject`, `OAI.ArExplicit.ConeModule`, `OAI.ArExplicit.ExternalBalanced.evaluatedSecondComparison`, `OAI.ArExplicit.TwistedBimodule.untwistInverse`, `OAI.ArExplicit.completeConeQuotient`.
--
--   **Sources.** They come from these modules of lean/OAI/Algebra, in whole or in part: [`AuslanderReiten_Bar_BarBalancedCanonical`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Bar/BarBalancedCanonical.lean), [`AuslanderReiten_Bar_BarBalancedEquiv`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Bar/BarBalancedEquiv.lean), [`AuslanderReiten_Cones_ConeCriterion`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Cones/ConeCriterion.lean), [`AuslanderReiten_Cones_MappingConeCokernel`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Cones/MappingConeCokernel.lean), [`AuslanderReiten_Ext_ExternalEvaluationCubic`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Ext/ExternalEvaluationCubic.lean), [`AuslanderReiten_Stable_StableExtNaturality`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Stable/StableExtNaturality.lean), [`AuslanderReiten_Stable_StableExtPrecomp`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Stable/StableExtPrecomp.lean), [`AuslanderReiten_Tensor_TwistedTensor`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Tensor/TwistedTensor.lean).
--
--   **Imports.** It imports the bundles `OAIQ031A077`, `OAIQ031A082`, `OAIQ031A084`, `OAIQ031A085` and `OAIQ031A086` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ031A109`, `OAIQ031A110`, `OAIQ031A112`, `OAIQ031A113`, `OAIQ031A114` and `OAIQ031A117`.
-- source:
--   OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 199; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/An-explicit-counterexample-to-the-Auslander-Reiten-conjecture-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algebra at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ031A077
import Definitions.Def_OAIQ031A082
import Definitions.Def_OAIQ031A084
import Definitions.Def_OAIQ031A085
import Definitions.Def_OAIQ031A086

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Bar_BarBalancedEquiv
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.EnvelopingBimodule.regular_projective _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct
namespace ArExplicit.BarBalanced
universe u
variable (k R M : Type u) [Field k] [Ring R] [Algebra k R]
  [AddCommGroup M] [Module R M] [Module k M] [IsScalarTower k R M]
attribute [local instance 2000] AbsoluteBar.baseModule AbsoluteBar.bimoduleTower

theorem evaluation_prepend (n : ℕ) (a : R) (z : evaluated k R M n) :
    evaluation k R M (n+1) (prependBalanced k R M n a z) =
      a ⊗ₜ[k] evaluation k R M n z := by
  induction z using BalancedTensor.induction_on with
  | zero => simp; rfl
  | add x y hx hy => simp only [map_add, TensorProduct.tmul_add, hx, hy]; rfl
  | tmul x m =>
    rw [prependBalanced_tmul, evaluation_tmul, coordinates_prepend,
      rawEval_succ, evaluation_tmul]
    rfl

theorem evaluation_embedding (n : ℕ) (x : ModuleBar.object k R M n) :
    evaluation k R M n (embedding k R M n x) = x := by
  induction n with
  | zero =>
    change rawEval k R M 0 (((coordinates k R 0) ((coordinates k R 0).symm 1)) ⊗ₜ[k] x) = x
    rw [LinearEquiv.apply_symm_apply, rawEval_zero, one_smul]
  | succ n ih =>
    induction x using OAI.tensorInductionOn with
    | add x y hx hy => simp only [map_add, hx, hy]; rfl
    | tmul a x => rw [embedding_succ, evaluation_prepend, ih]; rfl

theorem embedding_rawEval (n : ℕ) (x : AbsoluteBar.object k R n) (m : M) :
    embedding k R M n (rawEval k R M n (x ⊗ₜ[k] m)) =
      BalancedTensor.tmul ((coordinates k R n).symm x) m := by
  induction n with
  | zero =>
    change BalancedTensor.tmul ((coordinates k R 0).symm 1) (x • m) = _
    rw [← BalancedTensor.balance]
    congr 1
    apply (coordinates k R 0).injective
    rw [coordinates_right, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
    exact one_mul x
  | succ n ih =>
    induction x using OAI.tensorInductionOn with
    | add x y hx hy =>
      simp only [TensorProduct.add_tmul, map_add, hx, hy, BalancedTensor.add_tmul]
    | tmul a x =>
      rw [rawEval_succ, embedding_succ, ih, prependBalanced_tmul]
      congr 1

theorem embedding_evaluation (n : ℕ) (z : evaluated k R M n) :
    embedding k R M n (evaluation k R M n z) = z := by
  induction z using BalancedTensor.induction_on with
  | zero =>
    rw [(evaluation k R M n).map_zero]
    exact (embedding k R M n).map_zero
  | add x y hx hy =>
    rw [(evaluation k R M n).map_add]
    exact ((embedding k R M n).map_add _ _).trans (congrArg₂ (· + ·) hx hy)
  | tmul x m =>
    rw [evaluation_tmul, embedding_rawEval, LinearEquiv.symm_apply_apply]

def equiv (n : ℕ) : evaluated k R M n ≃ₗ[R] ModuleBar.moduleObject k R M n :=
  LinearEquiv.ofBijective (evaluation k R M n) ⟨
    fun _ _ h => (embedding_evaluation k R M n _).symm.trans
      ((congrArg (embedding k R M n) h).trans (embedding_evaluation k R M n _)),
    fun x => ⟨embedding k R M n x, evaluation_embedding k R M n x⟩⟩

@[simp] theorem equiv_tmul (n : ℕ) (x : bar k R n) (m : M) :
    equiv k R M n (BalancedTensor.tmul x m) =
      rawEval k R M n ((coordinates k R n x) ⊗ₜ[k] m) := rfl

end ArExplicit.BarBalanced

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Bar_BarBalancedCanonical
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.EnvelopingBimodule.regular_projective _root_.OAI.ArExplicit.ExternalTensor.hasHomCochainTotal _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ArExplicit.BarBalanced
open CategoryTheory
open scoped TensorProduct
universe u
variable (k R : Type u) [Field k] [Ring R] [Algebra k R]
attribute [local instance 2000] moduleCatBaseModule moduleCatBaseTower
variable (X : ModuleCat.{u} R)

abbrev canonicalEvaluated (n : ℕ) :=
  BalancedTensor k R (EnvelopingBimodule k R (AbsoluteBar.moduleObject k R n)) X

def canonicalObject (n : ℕ) : ModuleCat.{u} R :=
  ModuleCat.of R (canonicalEvaluated k R X n)

def nativeObject (n : ℕ) : ModuleCat.{u} R :=
  ModuleCat.of R (evaluated k R X n)

def scalarEvaluatedObject (n : ℕ)
    (μ : Module k (AbsoluteBar.moduleObject k R n))
    (τ : letI := μ; IsScalarTower k (AbsoluteBar.Enveloping k R)
      (AbsoluteBar.moduleObject k R n)) : ModuleCat.{u} R := by
  letI := μ
  letI := τ
  exact ModuleCat.of R
    (BalancedTensor k R (EnvelopingBimodule k R (AbsoluteBar.moduleObject k R n)) X)

def scalarEvaluatedElement (n : ℕ)
    (μ : Module k (AbsoluteBar.moduleObject k R n))
    (τ : letI := μ; IsScalarTower k (AbsoluteBar.Enveloping k R)
      (AbsoluteBar.moduleObject k R n))
    (z : AbsoluteBar.moduleObject k R n) (x : X) : scalarEvaluatedObject k R X n μ τ := by
  letI := μ
  letI := τ
  exact BalancedTensor.tmul (EnvelopingBimodule.mk z) x

theorem scalarEvaluatedObject_eq (n : ℕ)
    (μ ν : Module k (AbsoluteBar.moduleObject k R n))
    (τ : letI := μ; IsScalarTower k (AbsoluteBar.Enveloping k R)
      (AbsoluteBar.moduleObject k R n))
    (υ : letI := ν; IsScalarTower k (AbsoluteBar.Enveloping k R)
      (AbsoluteBar.moduleObject k R n)) (h : μ=ν) :
    scalarEvaluatedObject k R X n μ τ = scalarEvaluatedObject k R X n ν υ := by
  subst ν
  rfl

theorem scalarEvaluatedElement_transport (n : ℕ)
    (μ ν : Module k (AbsoluteBar.moduleObject k R n))
    (τ : letI := μ; IsScalarTower k (AbsoluteBar.Enveloping k R)
      (AbsoluteBar.moduleObject k R n))
    (υ : letI := ν; IsScalarTower k (AbsoluteBar.Enveloping k R)
      (AbsoluteBar.moduleObject k R n)) (h : μ=ν)
    (z : AbsoluteBar.moduleObject k R n) (x : X) :
    (eqToIso (scalarEvaluatedObject_eq k R X n μ ν τ υ h)).hom
      (scalarEvaluatedElement k R X n μ τ z x) =
    scalarEvaluatedElement k R X n ν υ z x := by
  subst ν
  rfl

theorem canonicalScalar_eq (n : ℕ) :
    moduleCatBaseModule (k := k) (R := AbsoluteBar.Enveloping k R)
      (AbsoluteBar.moduleObject k R n) = AbsoluteBar.baseModule k R n := by
  let := AbsoluteBar.baseModule k R n
  let := AbsoluteBar.bimoduleTower k R n
  exact ExternalTensor.canonicalScalar_eq k (AbsoluteBar.Enveloping k R)
    (AbsoluteBar.moduleObject k R n)

theorem canonicalObject_eq (n : ℕ) : canonicalObject k R X n = nativeObject k R X n :=
  scalarEvaluatedObject_eq k R X n _ _
    (moduleCatBaseTower (k := k) (R := AbsoluteBar.Enveloping k R)
      (AbsoluteBar.moduleObject k R n))
    (AbsoluteBar.bimoduleTower k R n) (canonicalScalar_eq k R n)

def canonicalTransport (n : ℕ) : canonicalEvaluated k R X n ≃ₗ[R] evaluated k R X n :=
  (eqToIso (canonicalObject_eq k R X n)).toLinearEquiv

def nativeElement (n : ℕ) (z : AbsoluteBar.moduleObject k R n) (x : X) :
    evaluated k R X n := by
  letI := AbsoluteBar.baseModule k R n
  letI := AbsoluteBar.bimoduleTower k R n
  exact BalancedTensor.tmul (EnvelopingBimodule.mk z) x

@[simp] theorem canonicalTransport_tmul (n : ℕ)
    (z : EnvelopingBimodule k R (AbsoluteBar.moduleObject k R n)) (x : X) :
    canonicalTransport k R X n (BalancedTensor.tmul z x) = nativeElement k R X n z.value x :=
  scalarEvaluatedElement_transport k R X n _ _
    (moduleCatBaseTower (k := k) (R := AbsoluteBar.Enveloping k R)
      (AbsoluteBar.moduleObject k R n))
    (AbsoluteBar.bimoduleTower k R n) (canonicalScalar_eq k R n) z.value x

def canonicalEquiv (n : ℕ) : canonicalEvaluated k R X n ≃ₗ[R] ModuleBar.moduleObject k R X n :=
  (canonicalTransport k R X n).trans (equiv k R X n)

end ArExplicit.BarBalanced

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Cones_ConeCriterion
attribute [-instance] _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ArExplicit

open CategoryTheory CompleteComparison
open CochainComplex CochainComplex.HomComplex

universe u

variable {k R : Type u} [CommRing k] [Ring R] [Algebra k R]
variable {F G : CochainComplex (ModuleCat.{u} R) ℤ} (φ : F ⟶ G)

abbrev ConeModule := Cokernel (chainOfCochain (mappingCone φ)) 0

end ArExplicit

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Cones_MappingConeCokernel
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
variable {F G : CochainComplex (ModuleCat.{u} R) ℤ} (φ : F ⟶ G)

variable {L : Type u} [AddCommGroup L] [Module R L]
variable (p : CochainCokernel G →ₗ[R] L)
variable (hex : Function.Exact (cochainCokernelMap φ) p)

def completeConeQuotient : Cokernel (chainOfCochain (mappingCone φ)) 0 →ₗ[R] L :=
  (rawConeQuotient φ p hex).comp (cochainCokernelLinearEquiv (mappingCone φ)).toLinearMap

end ArExplicit

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Ext_ExternalEvaluationCubic
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ExternalTensor.hasHomCochainTotal _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ArExplicit.ExternalBalanced
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

universe u
variable (k A B : Type u) [Field k] [Ring A] [Ring B] [Algebra k A] [Algebra k B]
attribute [local instance 2000] moduleCatBaseModule moduleCatBaseTower
variable (X : ModuleCat.{u} A) (Y : ModuleCat.{u} B)
variable (P : ChainComplex (ModuleCat.{u} (A ⊗[k] Aᵐᵒᵖ)) ℕ)
  (Q : ChainComplex (ModuleCat.{u} (B ⊗[k] Bᵐᵒᵖ)) ℕ)
variable (p : ∀ n, P.X (n+3) ⟶ P.X n) (r : ∀ n, Q.X (n+3) ⟶ Q.X n)
local notation "QE" => factorEvaluation k Y Q

def evaluatedSecondComparison (n : ℕ) : (QE).X (n+3) ⟶ (QE).X n :=
  (EnvelopingBimodule.evaluationFunctor k B Y).map (r n)

end ArExplicit.ExternalBalanced

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Stable_StableExtNaturality
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ArExplicit
open CategoryTheory CategoryTheory.Abelian CompleteComparison
open scoped ModuleCat.Algebra
universe u
variable {k R : Type u} [Field k] [Ring R] [Algebra k R]
variable {P : ChainComplex (ModuleCat.{u} R) ℤ} (hP : TotallyAcyclicComplex P)
variable {N N' : ModuleCat.{u} R}

theorem positiveExtStableEquiv_postcomp (n : ℕ) (g : N ⟶ N')
    (x : Ext (ModuleCat.of R (Cokernel P 0)) N (n+1)) :
    positiveExtStableEquiv (k := k) hP N' n
      (x.comp (Ext.mk₀ g) (add_zero _)) =
        StableHom.postcomp g.hom (positiveExtStableEquiv (k := k) hP N n x) := by
  obtain ⟨f, hf, rfl⟩ := (completeExtResolution hP).extMk_surjective x (n+2) rfl
  rw [ProjectiveResolution.extMk_comp_mk₀, positiveExtStableEquiv_extMk,
    positiveExtStableEquiv_extMk]
  change StableHom.classOf R _ _ _ = StableHom.postcomp g.hom (StableHom.classOf R _ _ _)
  rw [StableHom.postcomp_classOf]
  apply congrArg (StableHom.classOf R _ _)
  apply LinearMap.ext
  intro z
  obtain ⟨z, rfl⟩ := Submodule.mkQ_surjective
    (LinearMap.range (P.d (((n+1 : ℕ) : ℤ)+1) ((n+1 : ℕ) : ℤ)).hom) z
  rfl

end ArExplicit

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Stable_StableExtPrecomp
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Abelian
open scoped ModuleCat.Algebra
namespace ArExplicit
open CompleteComparison
universe u
variable {k R : Type u} [Field k] [Ring R] [Algebra k R]
variable {P Q : ChainComplex (ModuleCat.{u} R) ℤ}
variable (hP : TotallyAcyclicComplex P) (hQ : TotallyAcyclicComplex Q)
variable (f : P ⟶ Q) (N : ModuleCat.{u} R)

theorem positiveExtStableEquiv_precomp (n : ℕ)
    (x : Ext (ModuleCat.of R (Cokernel Q 0)) N (n+1)) :
    positiveExtStableEquiv (k := k) hP N n
      ((Ext.mk₀ (ModuleCat.ofHom (cokernelMap f 0))).comp x (zero_add _)) =
    StableHom.precomp (cokernelMap f ((n+1 : ℕ) : ℤ))
      (positiveExtStableEquiv (k := k) hQ N n x) := by
  obtain ⟨g, hg, rfl⟩ := (completeExtResolution hQ).extMk_surjective x (n+2) rfl
  rw [ProjectiveResolution.mk₀_comp_extMk g (n+2) rfl hg (completeTailHom f hP hQ),
    positiveExtStableEquiv_extMk, positiveExtStableEquiv_extMk]
  change StableHom.classOf R _ _ _ = StableHom.precomp _ (StableHom.classOf R _ _ _)
  rw [StableHom.precomp_classOf]
  apply congrArg (StableHom.classOf R _ _)
  apply LinearMap.ext
  intro z
  obtain ⟨z, rfl⟩ := Submodule.mkQ_surjective
    (LinearMap.range (P.d (((n+1 : ℕ) : ℤ)+1) ((n+1 : ℕ) : ℤ)).hom) z
  rfl

end ArExplicit

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Tensor_TwistedTensor
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.EnvelopingBimodule.regular_projective _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ArExplicit

namespace TwistedBimodule

variable {k R M : Type*} [CommRing k] [Ring R] [Algebra k R]
variable [AddCommGroup M] [Module k M] [Module R M]
variable [IsScalarTower k R M] [SMulCommClass k R M]
variable (σ : R ≃ₐ[k] R)

def untwistInverse : TwistedLeftModule k R σ M →ₗ[k]
    BalancedTensor k R (TwistedBimodule k R σ) M :=
  (BalancedTensor.mk (⟨1⟩ : TwistedBimodule k R σ)).comp (TwistedLeftModule.scalarEquiv σ).toLinearMap

end TwistedBimodule
end ArExplicit

end OAI
end


