-- Prove2me | Definitions.Def_OAIQ031A120
-- name    : OAIQ031A120
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T14:54:02.909576+00:00
-- url     : https://prove2.me/theorems/a0112ab6-fc31-45f2-887c-d7e8b66d93e7
-- title:
--   Definitions bundle OAIQ031A120 of the split of OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.ArExplicit.Statement.main`, carved from OpenAI's openai/math development (OpenAI, *An explicit counterexample to the Auslander-Reiten conjecture (result family 199)*, OpenAI Math Release, September 23, 2026, result family 199, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 13 declarations of OpenAI's Lean: 3 definitions and 10 theorems. The definitions and types are `OAI.ArExplicit.CompleteComparison.tailFunctorHom`, `OAI.ArExplicit.CompleteComparison.tailFunctorIso`, `OAI.ArExplicit.FrobeniusTrace.completeStableDualityAt`.
--
--   **Sources.** They come from these modules of lean/OAI/Algebra, in whole or in part: [`AuslanderReiten_Bar_BarBalancedCanonical`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Bar/BarBalancedCanonical.lean), [`AuslanderReiten_Bar_ModuleBarCubic`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Bar/ModuleBarCubic.lean), [`AuslanderReiten_Bar_ModuleBarSuffix`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Bar/ModuleBarSuffix.lean), [`AuslanderReiten_Complete_CompleteStableDualityAt`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Complete/CompleteStableDualityAt.lean), [`AuslanderReiten_Complete_CompleteTailEndpoint`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Complete/CompleteTailEndpoint.lean), [`AuslanderReiten_Complete_CompleteTailFunctor`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Complete/CompleteTailFunctor.lean), [`AuslanderReiten_HomComplex_HomCochainNaturality`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/HomComplex/HomCochainNaturality.lean), [`AuslanderReiten_HomComplex_PositiveFullHomExt`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/HomComplex/PositiveFullHomExt.lean), [`AuslanderReiten_HomComplex_PositiveFullHomProducts`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/HomComplex/PositiveFullHomProducts.lean).
--
--   **Imports.** It imports the bundles `OAIQ031A105`, `OAIQ031A106`, `OAIQ031A107`, `OAIQ031A109` and `OAIQ031A110` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ031A130`, `OAIQ031A131`, `OAIQ031A132` and `OAIQ031A133`.
-- source:
--   OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 199; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/An-explicit-counterexample-to-the-Auslander-Reiten-conjecture-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algebra at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ031A105
import Definitions.Def_OAIQ031A106
import Definitions.Def_OAIQ031A107
import Definitions.Def_OAIQ031A109
import Definitions.Def_OAIQ031A110

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Bar_ModuleBarSuffix
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
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

variable [CharP k 2]

omit [CharP k 2] in

theorem suffixComparison_augmentation (p : AbsoluteBar.Cochain3 k R) :
    (differential k R M 0).comp (suffixComparisonMap k R M p 0) = cochain3 k R M p := by
  apply LinearMap.ext
  intro x
  change boundary k R M 0 (suffixComparison k R M p 1 x) = cochain3Linear k R M p x
  induction x using OAI.tensorInductionOn with
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul a x => rfl

end ArExplicit.ModuleBar

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Bar_BarBalancedCanonical
attribute [-instance] _root_.OAI.ArExplicit.AbsoluteBar.twistInvPair _root_.OAI.ArExplicit.AbsoluteBar.twistInvPairSymm _root_.OAI.ArExplicit.AbsoluteBar.twistedBaseModule _root_.OAI.ArExplicit.AbsoluteBar.twistedModuleTower _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ExternalTensor.hasHomCochainTotal _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
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

theorem rawEval_cubic_compatibility (p : AbsoluteBar.Cochain3 k R) (n : ℕ)
    (a : AbsoluteBar.moduleObject k R (n+4)) (x : X) :
    rawEval k R X (n+1) (cubicHom k R p n a ⊗ₜ[k] x) =
      ModuleBar.suffixComparisonMap k R X p n (rawEval k R X (n+4) (a ⊗ₜ[k] x)) :=
  rawEval_suffix k R X p (n+1) a x

end ArExplicit.BarBalanced

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Bar_ModuleBarCubic
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory
open CochainComplex CochainComplex.HomComplex
namespace ArExplicit.ModuleBar
universe u
variable (k R M : Type u) [Field k] [Ring R] [Algebra k R]
  [AddCommGroup M] [Module R M] [Module k M] [IsScalarTower k R M] [CharP k 2]
variable (p : AbsoluteBar.Cochain3 k R) (hp : AbsoluteBar.IsCocycle3 k R p)

theorem cubicMap_augmentation :
    cubicMap k R M p 0 ≫ (resolution k R M).π.f 0 =
      ModuleCat.ofHom (X := moduleObject k R M 4) (Y := moduleObject k R M 0)
        (cochain3 k R M p) := by
  change cubicMap k R M p 0 ≫ (augmentation k R M).f 0 = _
  rw [augmentation_zero]
  apply ModuleCat.hom_ext
  exact suffixComparison_augmentation k R M p

end ArExplicit.ModuleBar

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Complete_CompleteStableDualityAt
attribute [-instance] _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory
open scoped ModuleCat.Algebra
namespace ArExplicit.FrobeniusTrace
universe u
variable {k R : Type u} [Field k] [Ring R] [Algebra k R] [Module.Finite k R]
variable (τ : FrobeniusTrace k R) (hs : ∀ a b : R, τ.trace (a*b) = τ.trace (b*a))
variable {N : Type u} [AddCommGroup N] [Module R N] [Module k N]
  [IsScalarTower k R N] [SMulCommClass R k N]
open CompleteComparison

def completeStableDualityAt (P : ChainComplex (ModuleCat.{u} R) ℤ)
    (hP : ExactProjectiveComplex P) (a : ℤ) :
    Module.Dual k (StableHom R (Cokernel P a) N) ≃ₗ[k]
      StableHom R N (Cokernel P (a+1)) := by
  letI := hP.finite (a+1)
  letI := hP.projective (a+1)
  letI := hP.finite a
  letI := hP.projective a
  letI := hP.finite (a-1)
  letI := hP.projective (a-1)
  exact (τ.projectiveStableDuality hs (P.d (a+1) a).hom (P.d a (a-1)).hom
    (differential_comp P (a+1) a (a-1)) (hP.exactAt a)).trans
      (StableHom.targetEquiv (k := k) (cokernelSyzygyEquiv hP a).symm)

theorem completeStableDualityAt_symm_apply
    (P : ChainComplex (ModuleCat.{u} R) ℤ) (hP : ExactProjectiveComplex P) (a : ℤ)
    (f : Cokernel P a →ₗ[R] N) (g : N →ₗ[R] Cokernel P (a+1)) :
    ((τ.completeStableDualityAt hs P hP a).symm (StableHom.classOf R _ _ g))
      (StableHom.classOf R _ _ f) =
    letI := hP.finite a
    letI := hP.projective a
    (τ.projectiveHomDualEquiv hs).symm ((syzygyInclusion hP a).comp g)
      (f.comp (LinearMap.range (P.d (a+1) a).hom).mkQ) := by
  let := hP.finite (a+1)
  let := hP.projective (a+1)
  let := hP.finite a
  let := hP.projective a
  let := hP.finite (a-1)
  let := hP.projective (a-1)
  change ((τ.projectiveStableDuality hs (P.d (a+1) a).hom (P.d a (a-1)).hom
    (differential_comp P (a+1) a (a-1)) (hP.exactAt a)).symm
      (StableHom.targetEquiv (k := k) (cokernelSyzygyEquiv hP a)
        (StableHom.classOf R _ _ g))) (StableHom.classOf R _ _ f) = _
  rw [StableHom.targetEquiv_classOf]
  exact τ.projectiveStableDuality_symm_apply hs (P.d (a+1) a).hom (P.d a (a-1)).hom
    (differential_comp P (a+1) a (a-1)) (hP.exactAt a) f
    ((cokernelSyzygyEquiv hP a).toLinearMap.comp g)

theorem completeStableDualityAt_source
    {P Q : ChainComplex (ModuleCat.{u} R) ℤ}
    (hP : ExactProjectiveComplex P) (hQ : ExactProjectiveComplex Q) (a b : ℤ)
    (t : P.X a →ₗ[R] Q.X b)
    (α : Cokernel P a →ₗ[R] Cokernel Q b)
    (β : Cokernel P (a+1) →ₗ[R] Cokernel Q (b+1))
    (hα : α.comp (LinearMap.range (P.d (a+1) a).hom).mkQ =
      (LinearMap.range (Q.d (b+1) b).hom).mkQ.comp t)
    (hβ : (syzygyInclusion hQ b).comp β = t.comp (syzygyInclusion hP a))
    (f : StableHom R (Cokernel Q b) N) (g : StableHom R N (Cokernel P (a+1))) :
    ((τ.completeStableDualityAt hs P hP a).symm g) (StableHom.precomp α f) =
      ((τ.completeStableDualityAt hs Q hQ b).symm (StableHom.postcomp β g)) f := by
  obtain ⟨f,rfl⟩ := StableHom.classOf_surjective f
  obtain ⟨g,rfl⟩ := StableHom.classOf_surjective g
  rw [StableHom.precomp_classOf, StableHom.postcomp_classOf,
    completeStableDualityAt_symm_apply, completeStableDualityAt_symm_apply]
  let := hP.finite a
  let := hP.projective a
  let := hQ.finite b
  let := hQ.projective b
  have hf : (f.comp α).comp (LinearMap.range (P.d (a+1) a).hom).mkQ =
      (f.comp (LinearMap.range (Q.d (b+1) b).hom).mkQ).comp t := by
    rw [LinearMap.comp_assoc, hα, ← LinearMap.comp_assoc]
  have hg : (syzygyInclusion hQ b).comp (β.comp g) =
      t.comp ((syzygyInclusion hP a).comp g) := by
    rw [← LinearMap.comp_assoc, hβ, LinearMap.comp_assoc]
  rw [hf, hg]
  exact τ.presentationHomDual_naturality_source hs
    (FiniteProjectivePresentation.choose R (P.X a))
    (FiniteProjectivePresentation.choose R (Q.X b)) t
    (f.comp (LinearMap.range (Q.d (b+1) b).hom).mkQ) ((syzygyInclusion hP a).comp g)

end ArExplicit.FrobeniusTrace

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_HomComplex_PositiveFullHomExt
attribute [-instance] _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory
open CochainComplex CochainComplex.HomComplex
open scoped ModuleCat.Algebra
namespace ArExplicit.CompleteComparison
universe u
variable {k R : Type u} [Field k] [Ring R] [Algebra k R]
variable (K L : CochainComplex (ModuleCat.{u} R) ℤ)
variable (hK : TotallyAcyclicComplex (chainOfCochain K))
variable (hL : ExactProjectiveComplex (chainOfCochain L))

theorem fullPositiveExtEquiv_stable (n : ℕ)
    (x : CohomologyClass K L ((n+1 : ℕ) : ℤ)) :
    positiveExtStableEquiv (k := k) hK
      (ModuleCat.of R (Cokernel (chainOfCochain L) 0)) n
      (fullPositiveExtEquiv (k := k) K L hK hL n x) =
    fullHomSourceStableLinearEquiv (k := k) K L ((n+1 : ℕ) : ℤ) hK hL x :=
  LinearEquiv.apply_symm_apply _ _

end ArExplicit.CompleteComparison

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Complete_CompleteTailFunctor
attribute [-instance] _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Limits
open CochainComplex CochainComplex.HomComplex
namespace ArExplicit.CompleteComparison
universe u
variable {R S : Type u} [Ring R] [Ring S]
variable (F : ModuleCat.{u} R ⥤ ModuleCat.{u} S) [F.Additive]

variable (K : CochainComplex (ModuleCat.{u} R) ℤ)
local notation "FK" => functorComplex F K

def tailFunctorHom :
    nonnegativeTail (chainOfCochain FK) ⟶
      (F.mapHomologicalComplex (.down ℕ)).obj (nonnegativeTail (chainOfCochain K)) where
  f n := (tailTermIso FK n).hom ≫ F.map (tailTermIso K n).inv
  comm' n m hnm := by
    have hnm' : m+1=n := hnm
    subst n
    change ((tailTermIso FK (m+1)).hom ≫ F.map (tailTermIso K (m+1)).inv) ≫
        F.map ((nonnegativeTail (chainOfCochain K)).d (m+1) m) =
      (nonnegativeTail (chainOfCochain FK)).d (m+1) m ≫
        (tailTermIso FK m).hom ≫ F.map (tailTermIso K m).inv
    rw [tailTerm_d K _ _ rfl, tailTerm_d FK _ _ rfl]
    exact functor_iso_square F (tailTermIso K (m+1)) (tailTermIso K m)
      (tailTermIso FK (m+1)) (tailTermIso FK m) (K.d (-((m+1 : ℕ) : ℤ)) (-(m : ℤ)))

end ArExplicit.CompleteComparison

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Complete_CompleteTailEndpoint
attribute [-instance] _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace ArExplicit.CompleteComparison
universe u
variable {R S : Type u} [Ring R] [Ring S]
variable (F : ModuleCat.{u} R ⥤ ModuleCat.{u} S) [F.Additive]
variable (K : CochainComplex (ModuleCat.{u} R) ℤ)

def tailFunctorIso : nonnegativeTail (chainOfCochain (functorComplex F K)) ≅
    (F.mapHomologicalComplex (.down ℕ)).obj (nonnegativeTail (chainOfCochain K)) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n => tailTermIso (functorComplex F K) n ≪≫ (F.mapIso (tailTermIso K n)).symm)
    (fun i j _ => (tailFunctorHom F K).comm i j)

@[simp] theorem tailFunctorIso_hom : (tailFunctorIso F K).hom = tailFunctorHom F K := rfl

end ArExplicit.CompleteComparison

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_HomComplex_HomCochainNaturality
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Abelian HomologicalComplex
open scoped ModuleCat.Algebra
namespace ArExplicit.ExternalTensor
universe u
variable (k R : Type u) [Field k] [Ring R] [Algebra k R]
attribute [local instance 2000] moduleCatBaseModule moduleCatBaseTower
variable {X Y : ModuleCat.{u} R} (P : ProjectiveResolution X)

theorem homCochainCycleClass_eq_literal (n : ℕ)
    (f : LinearMap.ker (homShort k R (Y := Y) P n).g.hom) :
    homCochainCycleClass k R P n f =
      VectorCochain.literalClass k (homCochain k R P.complex Y) n f := by
  exact (VectorCochain.literalClass_eq_quotient k (homCochain k R P.complex Y) n f).symm

end ArExplicit.ExternalTensor

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_HomComplex_PositiveFullHomProducts
attribute [-instance] _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Abelian
open CochainComplex CochainComplex.HomComplex
namespace ArExplicit.CompleteComparison
universe u
variable {k R : Type u} [Field k] [Ring R] [Algebra k R] [CharP k 2]
variable [HasDerivedCategory (ModuleCat.{u} R)]
attribute [local instance] moduleCatBaseModule moduleCatBaseTower
variable (K : CochainComplex (ModuleCat.{u} R) ℤ)
variable (hK : TotallyAcyclicComplex (chainOfCochain K))

theorem fullPositiveExtEquiv_mk (n : ℕ) (x : Cocycle K K ((n+1 : ℕ) : ℤ)) :
    fullPositiveExtEquiv (k := k) K K hK hK.toExactProjectiveComplex n
      (CohomologyClass.mk x) = restrictedEndExt (k := k) K hK (n+1) x := by
  apply (positiveExtStableEquiv (k := k) hK
    (ModuleCat.of R (Cokernel (chainOfCochain K) 0)) n).injective
  rw [fullPositiveExtEquiv_stable, fullHomSourceStableLinearEquiv_mk]
  unfold restrictedEndExt restrictedCocycle
  erw [ResolutionProducts.natComparison_endExt_eq,
    positiveExtStableEquiv_extMk]
  unfold completeExtCyclesStable
  apply congrArg (StableHom.classOf R _ _)
  apply LinearMap.ext
  intro z
  obtain ⟨z,rfl⟩ := Submodule.mkQ_surjective
    (LinearMap.range ((chainOfCochain K).d (((n+1 : ℕ) : ℤ)+1) ((n+1 : ℕ) : ℤ)).hom) z
  exact (sourceCocycleMap_mk (k := k) x z).trans (by rfl)

theorem fullPositiveExtEquiv_product (n m : ℕ)
    (x : Cocycle K K ((n+1 : ℕ) : ℤ)) (y : Cocycle K K ((m+1 : ℕ) : ℤ)) :
    (fullPositiveExtEquiv (k := k) K K hK hK.toExactProjectiveComplex n
      (CohomologyClass.mk x)).comp
      (fullPositiveExtEquiv (k := k) K K hK hK.toExactProjectiveComplex m
        (CohomologyClass.mk y)) rfl =
    fullPositiveExtEquiv (k := k) K K hK hK.toExactProjectiveComplex (n+1+m)
      (CohomologyClass.mk (ResolutionProducts.natCocycleProduct (n := n+1) (m := m+1) x y)) := by
  rw [fullPositiveExtEquiv_mk, fullPositiveExtEquiv_mk, fullPositiveExtEquiv_mk,
    restrictedEndExt_product]
  rfl

end ArExplicit.CompleteComparison

end

end OAI
end


