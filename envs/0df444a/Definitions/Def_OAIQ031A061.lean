-- Prove2me | Definitions.Def_OAIQ031A061
-- name    : OAIQ031A061
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T14:10:43.93581+00:00
-- url     : https://prove2.me/theorems/3f310952-f6f5-4629-8c04-7effbae20c68
-- title:
--   Definitions bundle OAIQ031A061 of the split of OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.ArExplicit.Statement.main`, carved from OpenAI's openai/math development (OpenAI, *An explicit counterexample to the Auslander-Reiten conjecture (result family 199)*, OpenAI Math Release, September 23, 2026, result family 199, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 24 declarations of OpenAI's Lean: 10 definitions, 1 inductive type or structure and 13 theorems. The definitions and types are `OAI.ArExplicit.AbsoluteBar.twistEnveloping`, `OAI.ArExplicit.CompleteComparison.cochainCokernelLinearEquiv`, `OAI.ArExplicit.CompleteComparison.homotopyCokernelEquiv`, `OAI.ArExplicit.CompleteComparison.stableCokernel`, `OAI.ArExplicit.StableHom.sourceEquiv`, `OAI.ArExplicit.StableHom.targetEquiv`, `OAI.ArExplicit.StableIsomorphism`, `OAI.ArExplicit.StableIsomorphism.ofExactProjectiveKernel`, `OAI.ArExplicit.StableIsomorphism.ofLinearEquiv`, `OAI.ArExplicit.StableIsomorphism.sourceAddEquiv`, `OAI.ArExplicit.StableIsomorphism.targetAddEquiv`.
--
--   **Sources.** They come from these modules of lean/OAI/Algebra, in whole or in part: [`AuslanderReiten_Bar_TwistedBar`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Bar/TwistedBar.lean), [`AuslanderReiten_Complete_CompleteNullhomotopy`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Complete/CompleteNullhomotopy.lean), [`AuslanderReiten_Complete_CompleteStableComparison`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Complete/CompleteStableComparison.lean), [`AuslanderReiten_Cones_CochainCokernel`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Cones/CochainCokernel.lean), [`AuslanderReiten_Stable_StableHom`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Stable/StableHom.lean), [`AuslanderReiten_Stable_StableHomEquiv`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Stable/StableHomEquiv.lean), [`AuslanderReiten_Stable_StableHomotopyIso`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Stable/StableHomotopyIso.lean), [`AuslanderReiten_Stable_StableIsomorphism`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Stable/StableIsomorphism.lean), [`AuslanderReiten_Tensor_EnvelopingStableEvaluation`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Tensor/EnvelopingStableEvaluation.lean).
--
--   **Imports.** It imports the bundles `OAIQ031A044` and `OAIQ031A045` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ031A077`, `OAIQ031A078`, `OAIQ031A079`, `OAIQ031A080`, `OAIQ031A086` and `OAIQ031A088`.
-- source:
--   OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 199; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/An-explicit-counterexample-to-the-Auslander-Reiten-conjecture-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algebra at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ031A044
import Definitions.Def_OAIQ031A045

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Bar_TwistedBar
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
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

def twistEnveloping (h : R ≃ₐ[k] R) : Enveloping k R ≃ₐ[k] Enveloping k R :=
  Algebra.TensorProduct.congr (AlgEquiv.refl : R ≃ₐ[k] R) (AlgEquiv.op h)

end ArExplicit.AbsoluteBar

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Stable_StableHom
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u

namespace ArExplicit

variable (R : Type u) [Ring R]
variable (M N : Type u) [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N]

variable {R M N}

variable {L P : Type u} [AddCommGroup L] [Module R L] [AddCommGroup P] [Module R P]

variable (R M N)

namespace StableHom

variable {R M N}

theorem comp_assoc {Q : Type u} [AddCommGroup Q] [Module R Q]
    (h : StableHom R P Q) (g : StableHom R N P) (f : StableHom R M N) :
    comp h (comp g f) = comp (comp h g) f := by
  obtain ⟨h, rfl⟩ := classOf_surjective h
  obtain ⟨g, rfl⟩ := classOf_surjective g
  obtain ⟨f, rfl⟩ := classOf_surjective f
  simp only [comp_classOf, LinearMap.comp_assoc]

theorem eq_zero_of_projective_source [Module.Finite R M] [Module.Projective R M]
    (f : StableHom R M N) : f = 0 := by
  obtain ⟨f, rfl⟩ := classOf_surjective f
  apply (classOf_eq_zero_iff_projective f).mpr
  exact ⟨M, inferInstance, inferInstance, inferInstance, inferInstance,
    LinearMap.id, f, LinearMap.comp_id _⟩

end StableHom

end ArExplicit

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Complete_CompleteNullhomotopy
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
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

theorem nullhomotopy_iff_stable_zero (hP : TotallyAcyclicComplex P)
    (hQ : ExactProjectiveComplex Q) (F : P ⟶ Q) :
    Nonempty (Homotopy F 0) ↔
      StableHom.classOf R (Cokernel P 0) (Cokernel Q 0) (cokernelMap F 0) = 0 := by
  rw [StableHom.classOf_eq_zero_iff_projective]
  exact ⟨fun ⟨h⟩ => factorization_of_nullhomotopy hP.toExactProjectiveComplex F h,
    nullhomotopy_of_factorization hP hQ F⟩

end ArExplicit.CompleteComparison

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Complete_CompleteStableComparison
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
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

def stableCokernel : (P ⟶ Q) →+ StableHom R (Cokernel P 0) (Cokernel Q 0) where
  toFun F := StableHom.classOf R _ _ (cokernelMap F 0)
  map_zero' := by simp
  map_add' F G := by simp

theorem stableCokernel_surjective (hP : TotallyAcyclicComplex P)
    (hQ : ExactProjectiveComplex Q) : Function.Surjective (stableCokernel (P := P) (Q := Q)) := by
  intro x
  obtain ⟨f, rfl⟩ := StableHom.classOf_surjective x
  obtain ⟨F, rfl⟩ := cokernelMap_surjective hP hQ f
  exact ⟨F, rfl⟩

theorem comparison_kernels (hP : TotallyAcyclicComplex P)
    (hQ : ExactProjectiveComplex Q) :
    (Functor.mapAddHom (HomotopyCategory.quotient (ModuleCat.{u} R) (ComplexShape.down ℤ))
      (X := P) (Y := Q)).ker = (stableCokernel (P := P) (Q := Q)).ker := by
  ext F
  change (HomotopyCategory.quotient _ _).map F = 0 ↔ stableCokernel F = 0
  rw [HomotopyCategory.quotient_map_eq_zero_iff]
  exact nullhomotopy_iff_stable_zero hP hQ F

noncomputable def homotopyCokernelEquiv (hP : TotallyAcyclicComplex P)
    (hQ : ExactProjectiveComplex Q) :
    ((HomotopyCategory.quotient (ModuleCat.{u} R) (ComplexShape.down ℤ)).obj P ⟶
      (HomotopyCategory.quotient (ModuleCat.{u} R) (ComplexShape.down ℤ)).obj Q) ≃+
        StableHom R (Cokernel P 0) (Cokernel Q 0) :=
  (QuotientAddGroup.quotientKerEquivOfSurjective
    (Functor.mapAddHom (HomotopyCategory.quotient (ModuleCat.{u} R) (ComplexShape.down ℤ)))
    (Functor.map_surjective _)).symm.trans
      ((QuotientAddGroup.quotientAddEquivOfEq (comparison_kernels hP hQ)).trans
        (QuotientAddGroup.quotientKerEquivOfSurjective stableCokernel
          (stableCokernel_surjective hP hQ)))

@[simp]
theorem homotopyCokernelEquiv_map (hP : TotallyAcyclicComplex P)
    (hQ : ExactProjectiveComplex Q) (F : P ⟶ Q) :
    homotopyCokernelEquiv hP hQ ((HomotopyCategory.quotient _ _).map F) =
      StableHom.classOf R _ _ (cokernelMap F 0) := by
  let f := Functor.mapAddHom
    (HomotopyCategory.quotient (ModuleCat.{u} R) (ComplexShape.down ℤ)) (X := P) (Y := Q)
  let e := QuotientAddGroup.quotientKerEquivOfSurjective f (Functor.map_surjective _)
  have he : e (QuotientAddGroup.mk F) = (HomotopyCategory.quotient _ _).map F := rfl
  change (QuotientAddGroup.quotientKerEquivOfSurjective stableCokernel
    (stableCokernel_surjective hP hQ))
      (QuotientAddGroup.quotientAddEquivOfEq (comparison_kernels hP hQ)
        (e.symm ((HomotopyCategory.quotient _ _).map F))) = _
  rw [← he, e.symm_apply_apply, QuotientAddGroup.quotientAddEquivOfEq_mk]
  rfl

theorem homotopyCokernelEquiv_comp {S : ChainComplex (ModuleCat.{u} R) ℤ}
    (hP : TotallyAcyclicComplex P) (hQ : TotallyAcyclicComplex Q)
    (hS : ExactProjectiveComplex S)
    (f : (HomotopyCategory.quotient _ _).obj P ⟶ (HomotopyCategory.quotient _ _).obj Q)
    (g : (HomotopyCategory.quotient _ _).obj Q ⟶ (HomotopyCategory.quotient _ _).obj S) :
    homotopyCokernelEquiv hP hS (f ≫ g) =
      StableHom.comp (homotopyCokernelEquiv hQ hS g)
        (homotopyCokernelEquiv hP hQ.toExactProjectiveComplex f) := by
  obtain ⟨F, rfl⟩ := Functor.map_surjective (HomotopyCategory.quotient _ _) f
  obtain ⟨G, rfl⟩ := Functor.map_surjective (HomotopyCategory.quotient _ _) g
  rw [← Functor.map_comp, homotopyCokernelEquiv_map, homotopyCokernelEquiv_map,
    homotopyCokernelEquiv_map, StableHom.comp_classOf, cokernelMap_comp]

end ArExplicit.CompleteComparison

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Cones_CochainCokernel
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open CategoryTheory HomologicalComplex

namespace ArExplicit.CompleteComparison

universe u

variable {R : Type u} [Ring R]
variable (K : CochainComplex (ModuleCat.{u} R) ℤ)

noncomputable def cochainCokernelLinearEquiv :
    Cokernel (chainOfCochain K) 0 ≃ₗ[R] CochainCokernel K :=
  cokernelLinearCongr _ _
    (K.extendXIso negIndexEmbedding (i := -1) (i' := 1) (by rfl)).toLinearEquiv
    (K.extendXIso negIndexEmbedding (i := 0) (i' := 0) (by rfl)).toLinearEquiv (by
      exact (congrArg ModuleCat.Hom.hom
        (reverseShortComplexIso K (-1) 0 1 1 0 (-1) rfl rfl rfl).hom.comm₁₂).symm)

variable {K}
variable {L : CochainComplex (ModuleCat.{u} R) ℤ} (f : K ⟶ L)

theorem cochainCokernelLinearEquiv_natural :
    (cochainCokernelLinearEquiv L).toLinearMap.comp
      (cokernelMap (extendMap f negIndexEmbedding) 0) =
    (cochainCokernelMap f).comp (cochainCokernelLinearEquiv K).toLinearMap := by
  apply LinearMap.ext
  intro z
  obtain ⟨x, rfl⟩ := (LinearMap.range ((chainOfCochain K).d 1 0).hom).mkQ_surjective z
  change (LinearMap.range (L.d (-1) 0).hom).mkQ
    ((L.extendXIso negIndexEmbedding (i := 0) (i' := 0) rfl).hom.hom
      (((extendMap f negIndexEmbedding).f 0).hom x)) =
    (LinearMap.range (L.d (-1) 0).hom).mkQ
      ((f.f 0).hom ((K.extendXIso negIndexEmbedding (i := 0) (i' := 0) rfl).hom.hom x))
  congr 1
  have h := extendMap_f f negIndexEmbedding (i := 0) (i' := 0) rfl
  rw [h]
  simp

end ArExplicit.CompleteComparison

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Stable_StableHomEquiv
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ArExplicit.StableHom

universe u

variable {k R : Type u} [CommRing k] [Ring R] [Algebra k R]
variable {M M' N N' : Type u}
variable [AddCommGroup M] [Module R M] [AddCommGroup M'] [Module R M']
variable [AddCommGroup N] [Module R N] [Module k N] [IsScalarTower k R N]
variable [AddCommGroup N'] [Module R N'] [Module k N'] [IsScalarTower k R N']

def sourceEquiv (e : M ≃ₗ[R] M') : StableHom R M' N ≃ₗ[k] StableHom R M N where
  toFun := precomp e.toLinearMap
  invFun := precomp e.symm.toLinearMap
  left_inv f := by
    obtain ⟨f, rfl⟩ := classOf_surjective f
    simp only [precomp_classOf]
    congr 1
    ext x
    simp
  right_inv f := by
    obtain ⟨f, rfl⟩ := classOf_surjective f
    simp only [precomp_classOf]
    congr 1
    ext x
    simp
  map_add' := map_add _
  map_smul' c f := by
    obtain ⟨f, rfl⟩ := classOf_surjective f
    rw [← classOf_smul k, precomp_classOf, precomp_classOf, ← classOf_smul k]
    rfl

def targetEquiv (e : N ≃ₗ[R] N') : StableHom R M N ≃ₗ[k] StableHom R M N' where
  toFun := postcomp e.toLinearMap
  invFun := postcomp e.symm.toLinearMap
  left_inv f := by
    obtain ⟨f, rfl⟩ := classOf_surjective f
    simp only [postcomp_classOf]
    congr 1
    ext x
    simp
  right_inv f := by
    obtain ⟨f, rfl⟩ := classOf_surjective f
    simp only [postcomp_classOf]
    congr 1
    ext x
    simp
  map_add' := map_add _
  map_smul' c f := by
    obtain ⟨f, rfl⟩ := classOf_surjective f
    rw [← classOf_smul k, postcomp_classOf, postcomp_classOf, ← classOf_smul k]
    congr 1
    exact LinearMap.comp_smul _ _ _

@[simp]
theorem sourceEquiv_classOf (e : M ≃ₗ[R] M') (f : M' →ₗ[R] N) :
    sourceEquiv (k := k) e (classOf R M' N f) = classOf R M N (f.comp e.toLinearMap) :=
  precomp_classOf _ _

@[simp]
theorem targetEquiv_classOf (e : N ≃ₗ[R] N') (f : M →ₗ[R] N) :
    targetEquiv (k := k) e (classOf R M N f) = classOf R M N' (e.toLinearMap.comp f) :=
  postcomp_classOf _ _

end ArExplicit.StableHom

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Stable_StableIsomorphism
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ArExplicit

universe u

variable (R M N : Type u) [Ring R]
variable [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

structure StableIsomorphism where
  hom : StableHom R M N
  inv : StableHom R N M
  hom_inv_id : StableHom.comp inv hom = StableHom.identity
  inv_hom_id : StableHom.comp hom inv = StableHom.identity

namespace StableIsomorphism

variable {R M N}
variable {P : Type u} [AddCommGroup P] [Module R P]

def ofLinearEquiv (e : M ≃ₗ[R] N) : StableIsomorphism R M N where
  hom := StableHom.classOf R _ _ e.toLinearMap
  inv := StableHom.classOf R _ _ e.symm.toLinearMap
  hom_inv_id := by simp [StableHom.identity]
  inv_hom_id := by simp [StableHom.identity]

def targetAddEquiv (e : StableIsomorphism R M N) : StableHom R P M ≃+ StableHom R P N where
  toFun := StableHom.comp e.hom
  invFun := StableHom.comp e.inv
  left_inv f := by rw [StableHom.comp_assoc, e.hom_inv_id, StableHom.identity_comp]
  right_inv f := by rw [StableHom.comp_assoc, e.inv_hom_id, StableHom.identity_comp]
  map_add' := map_add _

def sourceAddEquiv (e : StableIsomorphism R M N) : StableHom R N P ≃+ StableHom R M P where
  toFun f := StableHom.comp f e.hom
  invFun f := StableHom.comp f e.inv
  left_inv f := by
    change StableHom.comp (StableHom.comp f e.hom) e.inv = f
    rw [← StableHom.comp_assoc, e.inv_hom_id, StableHom.comp_identity]
  right_inv f := by
    change StableHom.comp (StableHom.comp f e.inv) e.hom = f
    rw [← StableHom.comp_assoc, e.hom_inv_id, StableHom.comp_identity]
  map_add' f g := by
    exact congrArg (fun a : StableHom R M N →+ StableHom R M P => a e.hom)
      (map_add (StableHom.comp (R := R) (M := M)) f g)

noncomputable def ofExactProjectiveKernel
    [Module.Finite R P] [Module.Projective R P] [Module.Injective R P]
    (i : P →ₗ[R] M) (q : M →ₗ[R] N) (hi : Function.Injective i)
    (hq : Function.Surjective q) (hex : Function.Exact i q) :
    StableIsomorphism R M N := by
  let r := Classical.choose (Module.Injective.extension_property R P P M i hi (LinearMap.id : P →ₗ[R] P))
  have hr := Classical.choose_spec (Module.Injective.extension_property R P P M i hi (LinearMap.id : P →ₗ[R] P))
  let t : M →ₗ[R] M := LinearMap.id - i.comp r
  have ht : LinearMap.ker q ≤ LinearMap.ker t := by
    intro x hx
    obtain ⟨p, rfl⟩ := (hex x).mp hx
    change i p - i (r (i p)) = 0
    rw [show r (i p) = p from DFunLike.congr_fun hr p, sub_self]
  let s : N →ₗ[R] M := ((LinearMap.ker q).liftQ t ht).comp
    (q.quotKerEquivOfSurjective hq).symm.toLinearMap
  have hs (x : M) : s (q x) = x - i (r x) := by
    simp only [s, LinearMap.comp_apply, LinearEquiv.coe_coe,
      LinearMap.quotKerEquivOfSurjective_symm_apply, Submodule.liftQ_apply]
    rfl
  have hqi (p : P) : q (i p) = 0 := (hex (i p)).mpr ⟨p, rfl⟩
  have hqs : q.comp s = LinearMap.id := by
    apply LinearMap.ext
    intro y
    obtain ⟨x, rfl⟩ := hq y
    change q (s (q x)) = q x
    rw [hs, map_sub, hqi, sub_zero]
  refine ⟨StableHom.classOf R _ _ q, StableHom.classOf R _ _ s, ?_, ?_⟩
  · rw [StableHom.comp_classOf]
    change StableHom.classOf R M M (s.comp q) = StableHom.classOf R M M LinearMap.id
    rw [StableHom.classOf_eq_iff, factorsThroughFiniteFree_iff_projective]
    refine ⟨P, inferInstance, inferInstance, inferInstance, inferInstance, r, -i, ?_⟩
    apply LinearMap.ext
    intro x
    change -i (r x) = s (q x) - x
    rw [hs]
    abel
  · rw [StableHom.comp_classOf, hqs]
    rfl

@[simp]
theorem ofExactProjectiveKernel_hom
    [Module.Finite R P] [Module.Projective R P] [Module.Injective R P]
    (i : P →ₗ[R] M) (q : M →ₗ[R] N) (hi : Function.Injective i)
    (hq : Function.Surjective q) (hex : Function.Exact i q) :
    (ofExactProjectiveKernel i q hi hq hex).hom = StableHom.classOf R _ _ q := by
  rfl

end StableIsomorphism
end ArExplicit

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Stable_StableHomotopyIso
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
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

@[simp]
theorem homotopyCokernelEquiv_id (hP : TotallyAcyclicComplex P) :
    homotopyCokernelEquiv hP hP.toExactProjectiveComplex (𝟙 _) = StableHom.identity := by
  rw [← (HomotopyCategory.quotient (ModuleCat.{u} R) (ComplexShape.down ℤ)).map_id,
    homotopyCokernelEquiv_map, cokernelMap_id]
  rfl

end ArExplicit.CompleteComparison

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Tensor_EnvelopingStableEvaluation
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory
open scoped TensorProduct ModuleCat.Algebra

namespace ArExplicit.EnvelopingBimodule
universe u
variable {k R : Type u} [Field k] [Ring R] [Algebra k R]
variable (X : ModuleCat.{u} R) [Module k X] [IsScalarTower k R X]
variable {M N P : ModuleCat.{u} (R ⊗[k] Rᵐᵒᵖ)}
variable [Module k M] [IsScalarTower k (R ⊗[k] Rᵐᵒᵖ) M]
variable [Module k N] [IsScalarTower k (R ⊗[k] Rᵐᵒᵖ) N]
variable [Module k P] [IsScalarTower k (R ⊗[k] Rᵐᵒᵖ) P]

variable [Module.Finite k R] [Module.Finite k X]

@[simp]
theorem stableEvaluation_id : stableEvaluation X
    (StableHom.classOf _ M M LinearMap.id) =
      StableHom.classOf R _ _ LinearMap.id := by
  rw [stableEvaluation_classOf]
  exact congrArg (StableHom.classOf R _ _) (tensorMap_id X)

end ArExplicit.EnvelopingBimodule

end

end OAI
end


