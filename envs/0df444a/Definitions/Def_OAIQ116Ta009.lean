-- Prove2me | Definitions.Def_OAIQ116Ta009
-- name    : OAIQ116Ta009
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-30T01:41:57.162817+00:00
-- url     : https://prove2.me/theorems/510dd733-9e05-40fc-b337-e74f7a2d05dc
-- title:
--   Definitions bundle OAIQ116Ta009 of the split of OpenAI, A counterexample to Tachikawa's second conjecture
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Tachikawa.main_theorem`, carved from OpenAI's openai/math development (OpenAI, *A counterexample to Tachikawa's second conjecture*, OpenAI Math Release, September 23, 2026, result family 199, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 5 declarations of OpenAI's Lean: 3 definitions and 2 theorems. The definitions and types are `OAI.Tachikawa.SymmetrizingForm.freeTwistIso`, `OAI.Tachikawa.SymmetrizingForm.twistFromFree`, `OAI.Tachikawa.SymmetrizingForm.twistToFree`.
--
--   **Sources.** They come from these modules of lean/OAI/RingTheory, in whole or in part: [`Tachikawa_Nakayama`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/RingTheory/Tachikawa/Nakayama.lean), [`Tachikawa_Twisting`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/RingTheory/Tachikawa/Twisting.lean).
--
--   **Imports.** It imports the bundles `OAIQ116Ta003` and `OAIQ116Ta004` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ116Ta012`.
-- source:
--   OpenAI, A counterexample to Tachikawa's second conjecture, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 199; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-counterexample-to-Tachikawas-second-conjecture-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/RingTheory at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ116Ta003
import Definitions.Def_OAIQ116Ta004

section
-- module Solutions.OAIQ116_Tach.Tachikawa_Twisting
attribute [-instance] _root_.OAI.Tachikawa.LeftCoinduced.coextend_additive _root_.OAI.Tachikawa.LeftCoinduced.coextend_preservesInjective _root_.OAI.Tachikawa.OuterTensor.restrictionPreservesHomology _root_.OAI.Tachikawa.TotalDualPairing.instTensorSignsNatUp_solutions _root_.OAI.Tachikawa.TotalMap.sourceHasCoproduct _root_.OAI.Tachikawa.downIntTensorSigns
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section



namespace Tachikawa
open CategoryTheory
open scoped ModuleCat.Algebra
namespace SymmetrizingForm
variable {k R : Type} [Field k] [Ring R] [Algebra k R]
  [FiniteDimensional k R] (t : SymmetrizingForm (k := k) (R := R))
  (σ : R ≃ₐ[k] R)

def freeTwistIso (ι : Type) :
    (twistFunctor σ).obj (ModuleCat.of R (ι → R)) ≅ ModuleCat.of R (ι → R) where
  hom := ModuleCat.ofHom (X := (twistFunctor σ).obj (ModuleCat.of R (ι → R)))
    (Y := ModuleCat.of R (ι → R))
    { toFun x i := σ (x i)
      map_add' x y := by ext i; exact map_add σ _ _
      map_smul' r x := by
        ext i
        change σ (σ.symm r * x i) = r * σ (x i)
        rw [map_mul,AlgEquiv.apply_symm_apply] }
  inv := ModuleCat.ofHom (X := ModuleCat.of R (ι → R))
    (Y := (twistFunctor σ).obj (ModuleCat.of R (ι → R)))
    { toFun x i := σ.symm (x i)
      map_add' x y := by
        change (fun i => σ.symm (x i+y i)) = fun i => σ.symm (x i)+σ.symm (y i)
        funext i
        exact map_add σ.symm _ _
      map_smul' r x := by
        change (fun i => σ.symm (r * x i)) = fun i => σ.symm r * σ.symm (x i)
        funext i
        rw [map_mul] }
  hom_inv_id := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change (fun i => σ.symm (σ (x i))) = x
    funext i
    exact AlgEquiv.symm_apply_apply σ _
  inv_hom_id := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change (fun i => σ (σ.symm (x i))) = x
    funext i
    exact AlgEquiv.apply_symm_apply σ _

variable (ι : Type) [Fintype ι] [DecidableEq ι] (N : ModuleCat R)

def twistToFree (g : N →ₗ[R] (ι → R)) :
    (twistFunctor σ).obj N →ₗ[R] (ι → R) :=
  ((twistFunctor σ).map (ModuleCat.ofHom g) ≫ (freeTwistIso σ ι).hom).hom

def twistFromFree (f : (ι → R) →ₗ[R] N) :
    (ι → R) →ₗ[R] (twistFunctor σ).obj N :=
  ((freeTwistIso σ ι).inv ≫ (twistFunctor σ).map (ModuleCat.ofHom f)).hom

end SymmetrizingForm
end Tachikawa



end

end OAI
end

section
-- module Solutions.OAIQ116_Tach.Tachikawa_Nakayama
attribute [-instance] _root_.OAI.Tachikawa.Construction.instModuleEX _root_.OAI.Tachikawa.LeftCoinduced.coextend_additive _root_.OAI.Tachikawa.LeftCoinduced.coextend_preservesInjective _root_.OAI.Tachikawa.downIntTensorSigns
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section



namespace Tachikawa
open CategoryTheory
open scoped ModuleCat.Algebra
variable {k R : Type} [Field k] [Ring R] [Algebra k R]
namespace Nakayama

variable {P Q Z : Type} [AddCommGroup P] [Module R P]
  [AddCommGroup Q] [Module R Q] [AddCommGroup Z] [Module R Z]

lemma map_surjective (g : Q →ₗ[R] Z) (hg : Function.Surjective g) :
    Function.Surjective (map (k := k) g) := by
  change Function.Surjective (homPrecomp (k := k) (Z := R) g).dualMap
  apply LinearMap.dualMap_surjective_of_injective
  intro a b hab
  ext z
  obtain ⟨q, rfl⟩ := hg z
  exact LinearMap.congr_fun hab q

end Nakayama
end Tachikawa



namespace Tachikawa
namespace TrivialInduction
variable {k R : Type} [Field k] [Ring R] [Algebra k R]
variable {M N : Type} [AddCommGroup M] [Module R M] [Module k M] [IsScalarTower k R M]
  [AddCommGroup N] [Module R N] [Module k N] [IsScalarTower k R N]

lemma map_surjective (f : M →ₗ[R] N) (hf : Function.Surjective f) :
    Function.Surjective (map (k := k) f) := by
  intro x
  obtain ⟨m,hm⟩ := hf x.1
  obtain ⟨ψ,hψ⟩ := Nakayama.map_surjective (k := k) f hf x.2
  exact ⟨(m,ψ), Prod.ext hm hψ⟩

end TrivialInduction
end Tachikawa



end

end OAI
end


