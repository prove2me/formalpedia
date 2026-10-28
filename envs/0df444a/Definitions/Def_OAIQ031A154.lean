-- Prove2me | Definitions.Def_OAIQ031A154
-- name    : OAIQ031A154
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T15:29:16.415075+00:00
-- url     : https://prove2.me/theorems/d6102cb8-9348-4ae8-8eb9-78369af2800b
-- title:
--   Definitions bundle OAIQ031A154 of the split of OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.ArExplicit.Statement.main`, carved from OpenAI's openai/math development (OpenAI, *An explicit counterexample to the Auslander-Reiten conjecture (result family 199)*, OpenAI Math Release, September 23, 2026, result family 199, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 5 declarations of OpenAI's Lean: 5 theorems.
--
--   **Sources.** They come from these modules of lean/OAI/Algebra, in whole or in part: [`AuslanderReiten_Bar_ModuleBarExtTwist`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Bar/ModuleBarExtTwist.lean), [`AuslanderReiten_Bar_ModuleBarTwistExtAction`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Bar/ModuleBarTwistExtAction.lean), [`AuslanderReiten_Bar_ModuleBarTwistIdentity`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Bar/ModuleBarTwistIdentity.lean).
--
--   **Imports.** It imports the bundles `OAIQ031A126` and `OAIQ031A149` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ031A156`.
-- source:
--   OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 199; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/An-explicit-counterexample-to-the-Auslander-Reiten-conjecture-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algebra at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ031A126
import Definitions.Def_OAIQ031A149

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Bar_ModuleBarExtTwist
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.TrivialInduction.baseComm _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.moduleCatBaseComm _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Abelian
open scoped ModuleCat.Algebra
namespace ArExplicit.ModuleBar
universe u
variable (k R M : Type u) [Field k] [Ring R] [Algebra k R]
  [AddCommGroup M] [Module R M] [Module k M] [IsScalarTower k R M]
variable [CharP k 2]
variable (h : R ≃ₐ[k] R) (e : M ≃ₗ[k] M)
variable (he : ∀ a m, e (a • m) = h a • e m)

theorem twistExtAction_cycle (n : ℕ)
    (f g : LinearMap.ker
      (ExternalTensor.homShort k R (Y := ModuleCat.of R M) (resolution k R M) n).g.hom)
    (hfg : ∀ x : moduleObject k R M (n+1),
      (show moduleObject k R M (n+1) →ₗ[R] M from g.val) x =
        e.symm ((show moduleObject k R M (n+1) →ₗ[R] M from f.val)
          (transport k R M h e (n+1) x))) :
    twistExtAction k R M h e he n
      (ExternalTensor.homCyclesToExt k R (resolution k R M) n f) =
        ExternalTensor.homCyclesToExt k R (resolution k R M) n g := by
  apply ExternalTensor.homCochainEndExt_cycleClass k R (resolution k R M)
    (canonicalHomTransport k R M h e he) n f g
  apply LinearMap.ext
  intro x
  exact (hfg x).symm

end ArExplicit.ModuleBar

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Bar_ModuleBarTwistExtAction
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.TrivialInduction.baseComm _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.moduleCatBaseComm _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Abelian
open scoped ModuleCat.Algebra
namespace ArExplicit.ModuleBar
attribute [local instance] moduleCatBaseModule moduleCatBaseTower
universe u
variable (k R M : Type u) [Field k] [Ring R] [Algebra k R]
  [AddCommGroup M] [Module R M] [Module k M] [IsScalarTower k R M] [CharP k 2]
variable (h : R ≃ₐ[k] R) (e : M ≃ₗ[k] M)
variable (he : ∀ a m, e (a • m) = h a • e m)

theorem twistExtAction_extMk (n : ℕ)
    (f g : (resolution k R M).complex.X n ⟶ ModuleCat.of R M)
    (hf : (resolution k R M).complex.d (n+1) n ≫ f = 0)
    (hg : (resolution k R M).complex.d (n+1) n ≫ g = 0)
    (hfg : ∀ x : moduleObject k R M (n+1), g.hom x =
      e.symm (f.hom (transport k R M h e (n+1) x))) :
    twistExtAction k R M h e he n ((resolution k R M).extMk f (n+1) rfl hf) =
      (resolution k R M).extMk g (n+1) rfl hg := by
  let f' : LinearMap.ker (ExternalTensor.homShort k R (Y := ModuleCat.of R M)
      (resolution k R M) n).g.hom := ⟨f.hom, by
    rw [ExternalTensor.homShort_outgoing]
    exact congrArg ModuleCat.Hom.hom hf⟩
  let g' : LinearMap.ker (ExternalTensor.homShort k R (Y := ModuleCat.of R M)
      (resolution k R M) n).g.hom := ⟨g.hom, by
    rw [ExternalTensor.homShort_outgoing]
    exact congrArg ModuleCat.Hom.hom hg⟩
  exact twistExtAction_cycle k R M h e he n f' g' hfg

theorem twistExtAction_extMk_transported (n : ℕ)
    (f : (resolution k R M).complex.X n ⟶ ModuleCat.of R M)
    (hf : (resolution k R M).complex.d (n+1) n ≫ f=0) :
    twistExtAction k R M h e he n ((resolution k R M).extMk f (n+1) rfl hf) =
      (resolution k R M).extMk (transportedCochain k R M h e he n f) (n+1) rfl
        (transportedCochain_closed k R M h e he n f hf) :=
  twistExtAction_extMk k R M h e he n f _ hf _ (fun _ => rfl)

variable [HasDerivedCategory (ModuleCat.{u} R)]
variable (p : AbsoluteBar.Cochain3 k R) (hp : AbsoluteBar.IsCocycle3 k R p)

variable (c : k)
variable (hpc : ∀ a b d m, p (h a) (h b) (h d) • e m = c • e (p a b d • m))
include hpc

theorem twistExtAction_cubic (n : ℕ)
    (x : Ext (moduleObject k R M 0) (ModuleCat.of R M) n) :
    twistExtAction k R M h e he (n+3) ((extClass3 k R M p hp).comp x (by omega : 3+n=n+3)) =
      c • (extClass3 k R M p hp).comp (twistExtAction k R M h e he n x) (by omega : 3+n=n+3) := by
  obtain ⟨f,hf,rfl⟩ := (resolution k R M).extMk_surjective x (n+1) rfl
  rw [extClass3_comp_extMk, twistExtAction_extMk_transported,
    twistExtAction_extMk_transported, extClass3_comp_extMk]
  have hc := ResolutionProducts.cubicPrecomp_closed (resolution k R M) (cubicMap k R M p)
    (cubicMap_comm k R M p hp) (transportedCochain k R M h e he n f)
    (transportedCochain_closed k R M h e he n f hf)
  have hsc : (resolution k R M).complex.d (n+3+1) (n+3) ≫
      (c • (cubicMap k R M p n ≫ transportedCochain k R M h e he n f)) = 0 := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    have hx := LinearMap.congr_fun (congrArg ModuleCat.Hom.hom hc) x
    change (transportedCochain k R M h e he n f).hom
      ((cubicMap k R M p n).hom
        (((resolution k R M).complex.d (n+4) (n+3)).hom x)) = 0 at hx
    change c • (transportedCochain k R M h e he n f).hom
      ((cubicMap k R M p n).hom
        (((resolution k R M).complex.d (n+4) (n+3)).hom x)) = 0
    rw [hx, smul_zero]
  refine (extMk_congr k R M (n+3) _ _ _ hsc
    (transportedCochain_cubic k R M h e he p c hpc n f)).trans ?_
  exact extMk_smul_native k R M (n+3)
    (cubicMap k R M p n ≫ transportedCochain k R M h e he n f) hc c hsc

end ArExplicit.ModuleBar

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Bar_ModuleBarTwistIdentity
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Abelian
namespace ArExplicit.ModuleBar
universe u
variable (k R M : Type u) [Field k] [Ring R] [Algebra k R]
  [AddCommGroup M] [Module R M] [Module k M] [IsScalarTower k R M] [CharP k 2]
variable [HasDerivedCategory (ModuleCat.{u} R)]
variable (h : R ≃ₐ[k] R) (e : M ≃ₗ[k] M)
variable (he : ∀ a m, e (a • m) = h a • e m)

theorem twistExtAction_identity :
    twistExtAction k R M h e he 0 (Ext.mk₀ (𝟙 (moduleObject k R M 0))) =
      Ext.mk₀ (𝟙 (moduleObject k R M 0)) := by
  change twistExtAction k R M h e he 0 (Ext.mk₀ (𝟙 (ModuleCat.of R M))) =
    Ext.mk₀ (𝟙 (ModuleCat.of R M))
  let P := resolution k R M
  let f : P.complex.X 0 ⟶ ModuleCat.of R M := P.π.f 0
  have hf : P.complex.d 1 0 ≫ f = 0 := P.complex_d_comp_π_f_zero
  have ha : P.extMk f 1 rfl hf = Ext.mk₀ (𝟙 (ModuleCat.of R M)) :=
    ResolutionProducts.extMk_augmentation P
  have hz : twistExtAction k R M h e he 0 (P.extMk f 1 rfl hf) = P.extMk f 1 rfl hf := by
    rw [twistExtAction_extMk_transported]
    congr 1
    exact transportedCochain_augmentation k R M h e he
  exact ((congrArg (twistExtAction k R M h e he 0) ha.symm).trans hz).trans ha

end ArExplicit.ModuleBar

end

end OAI
end


