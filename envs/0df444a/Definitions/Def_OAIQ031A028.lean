-- Prove2me | Definitions.Def_OAIQ031A028
-- name    : OAIQ031A028
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T13:58:10.75084+00:00
-- url     : https://prove2.me/theorems/1832ece9-dee7-4f9e-9243-8234d93a5ffa
-- title:
--   Definitions bundle OAIQ031A028 of the split of OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.ArExplicit.Statement.main`, carved from OpenAI's openai/math development (OpenAI, *An explicit counterexample to the Auslander-Reiten conjecture (result family 199)*, OpenAI Math Release, September 23, 2026, result family 199, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 19 declarations of OpenAI's Lean: 6 definitions, 2 instances and 11 theorems. The definitions and types are `OAI.ArExplicit.Coinduced.evalOne`, `OAI.ArExplicit.CompleteComparison.cocycleComparisonMap`, `OAI.ArExplicit.CompleteComparison.reverseShortComplexIso`, `OAI.ArExplicit.coneBlockShortComplex`, `OAI.ArExplicit.coneShortComplexIso`, `OAI.ArExplicit.rawConeBlockEquiv`.
--
--   **Sources.** They come from these modules of lean/OAI/Algebra, in whole or in part: [`AuslanderReiten_Algebras_FrobeniusTrace`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Algebras/FrobeniusTrace.lean), [`AuslanderReiten_Bar_BarComplex`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Bar/BarComplex.lean), [`AuslanderReiten_Complete_CompleteShiftDual`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Complete/CompleteShiftDual.lean), [`AuslanderReiten_Complete_SelfInjectiveComplex`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Complete/SelfInjectiveComplex.lean), [`AuslanderReiten_Complete_TateKoszul`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Complete/TateKoszul.lean), [`AuslanderReiten_Cones_ConeExactness`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Cones/ConeExactness.lean), [`AuslanderReiten_Cones_MappingConeCokernel`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Cones/MappingConeCokernel.lean), [`AuslanderReiten_Cones_MappingConeModule`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Cones/MappingConeModule.lean), [`AuslanderReiten_Cones_MappingConeTotal`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Cones/MappingConeTotal.lean), [`AuslanderReiten_HomComplex_FullHomComparison`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/HomComplex/FullHomComparison.lean), [`AuslanderReiten_HomComplex_FullHomProducts`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/HomComplex/FullHomProducts.lean), [`AuslanderReiten_Modules_Coinduced`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Modules/Coinduced.lean).
--
--   **Imports.** It imports the bundles `OAIQ031A001`, `OAIQ031A003`, `OAIQ031A004`, `OAIQ031A005` and `OAIQ031A017` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ031A045`, `OAIQ031A047`, `OAIQ031A056`, `OAIQ031A057` and `OAIQ031A058`.
-- source:
--   OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 199; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/An-explicit-counterexample-to-the-Auslander-Reiten-conjecture-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algebra at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ031A001
import Definitions.Def_OAIQ031A003
import Definitions.Def_OAIQ031A004
import Definitions.Def_OAIQ031A005
import Definitions.Def_OAIQ031A017

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Modules_Coinduced
attribute [-instance] _root_.OAI.ArExplicit.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ArExplicit

namespace Coinduced

variable {k R : Type*} [CommRing k] [Ring R] [Algebra k R]

def evalOne : Coinduced k R →ₗ[k] k where
  toFun x := x.functional 1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

section Field

variable {k : Type*} [Field k] {R : Type*} [Ring R] [Algebra k R]

instance instInjective : Module.Injective R (Coinduced k R) := by
  apply Module.Baer.injective
  intro I g
  let φ : (I.restrictScalars k) →ₗ[k] k := evalOne.comp (g.restrictScalars k)
  obtain ⟨ψ, hψ⟩ := φ.exists_extend
  refine ⟨fromFunctional ψ, ?_⟩
  intro x hx
  apply Coinduced.ext
  ext r
  have h := LinearMap.congr_fun hψ (r • (⟨x, hx⟩ : I))
  change ψ (r * x) = (g ⟨x, hx⟩).functional r
  change ψ (r * x) = (g (r • (⟨x, hx⟩ : I))).functional 1 at h
  rw [map_smul] at h
  simpa using h

end Field
end Coinduced
end ArExplicit

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Algebras_FrobeniusTrace
attribute [-instance] _root_.OAI.ArExplicit.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ArExplicit

namespace FrobeniusTrace

variable {k R : Type*} [Field k] [Ring R] [Algebra k R] (τ : FrobeniusTrace k R)

variable [Module.Finite k R]

include τ in

theorem regular_injective : Module.Injective R R :=
  Module.Baer.injective <| Module.Baer.of_equiv τ.leftEquiv.symm
    (Module.Baer.of_injective (inferInstance : Module.Injective R (Coinduced k R)))

end FrobeniusTrace

end ArExplicit

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Bar_BarComplex
attribute [-instance] _root_.OAI.ArExplicit.finitePiProjective
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

theorem left_right (n : ℕ) (a : R) (b : Rᵐᵒᵖ) (x : object k R n) :
    left k R n a (right k R n b x) = right k R n b (left k R n a x) := by
  cases n with
  | zero => exact (mul_assoc _ _ _).symm
  | succ n =>
    induction x using OAI.tensorInductionOn with
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul c x => rfl

end ArExplicit.AbsoluteBar

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Complete_SelfInjectiveComplex
attribute [-instance] _root_.OAI.ArExplicit.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ArExplicit

universe u

variable {R : Type u} [Ring R] [Module.Injective R R]
variable {K L M : Type u}
variable [AddCommGroup K] [Module R K] [AddCommGroup L] [Module R L]
variable [AddCommGroup M] [Module R M]

theorem homExactAt_of_injective (e : K →ₗ[R] L) (d : L →ₗ[R] M)
    (hex : LinearMap.range e = LinearMap.ker d) : HomExactAt e d := by
  intro f hf
  have hk : LinearMap.ker d ≤ LinearMap.ker f := by
    rw [← hex]
    rintro _ ⟨x, rfl⟩
    exact DFunLike.congr_fun hf x
  let u : LinearMap.range d →ₗ[R] R :=
    ((LinearMap.ker d).liftQ f hk).comp d.quotKerEquivRange.symm.toLinearMap
  obtain ⟨g, hg⟩ := Module.Injective.extension_property R R (LinearMap.range d) M
    (LinearMap.range d).subtype Subtype.val_injective u
  refine ⟨g, ?_⟩
  apply LinearMap.ext
  intro x
  have h := DFunLike.congr_fun hg (d.rangeRestrict x)
  change g (d x) = f x
  calc
    g (d x) = u (d.rangeRestrict x) := h
    _ = f x := by
      exact congrArg ((LinearMap.ker d).liftQ f hk)
        (d.quotKerEquivRange_symm_apply_image x (LinearMap.mem_range_self d x))

theorem ExactProjectiveComplex.totallyAcyclic
    {P : ChainComplex (ModuleCat.{u} R) ℤ} (hP : ExactProjectiveComplex P) :
    TotallyAcyclicComplex P where
  toExactProjectiveComplex := hP
  dualExact n := homExactAt_of_injective _ _ (hP.exactAt n)

end ArExplicit

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_HomComplex_FullHomComparison
attribute [-instance] _root_.OAI.ArExplicit.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open CategoryTheory

namespace ArExplicit.CompleteComparison

universe u

variable {R : Type u} [Ring R]

instance negIndexFunctor_additive :
    (negIndexEmbedding.extendHomotopyFunctor (ModuleCat.{u} R)).Additive := by
  have := Functor.additive_of_iso
    (negIndexEmbedding.extendHomotopyFunctorFactors (ModuleCat.{u} R)).symm
  exact Functor.additive_of_full_essSurj_comp
    (HomotopyCategory.quotient (ModuleCat.{u} R) (ComplexShape.up ℤ)) _

end ArExplicit.CompleteComparison

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Complete_CompleteShiftDual
attribute [-instance] _root_.OAI.ArExplicit.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open CategoryTheory

namespace ArExplicit

universe u

variable {R : Type u} [Ring R]

namespace HomExactAt

variable {U V W U' V' W' : Type u}
variable [AddCommGroup U] [Module R U] [AddCommGroup V] [Module R V]
variable [AddCommGroup W] [Module R W] [AddCommGroup U'] [Module R U']
variable [AddCommGroup V'] [Module R V'] [AddCommGroup W'] [Module R W']

theorem congr {e : U →ₗ[R] V} {d : V →ₗ[R] W}
    (h : HomExactAt e d) (e' : U' →ₗ[R] V') (d' : V' →ₗ[R] W')
    (a : U ≃ₗ[R] U') (b : V ≃ₗ[R] V') (c : W ≃ₗ[R] W')
    (he : e'.comp a.toLinearMap = b.toLinearMap.comp e)
    (hd : d'.comp b.toLinearMap = c.toLinearMap.comp d) : HomExactAt e' d' := by
  intro f hf
  have hfb : (f.comp b.toLinearMap).comp e = 0 := by
    rw [LinearMap.comp_assoc, ← he, ← LinearMap.comp_assoc, hf, LinearMap.zero_comp]
  obtain ⟨g, hg⟩ := h (f.comp b.toLinearMap) hfb
  refine ⟨g.comp c.symm.toLinearMap, ?_⟩
  apply LinearMap.ext
  intro x'
  obtain ⟨x, rfl⟩ := b.surjective x'
  change g (c.symm (d' (b x))) = f (b x)
  rw [show d' (b x) = c (d x) from DFunLike.congr_fun hd x, c.symm_apply_apply]
  exact DFunLike.congr_fun hg x

theorem of_shortComplex_iso {S T : ShortComplex (ModuleCat.{u} R)} (E : S ≅ T)
    (h : HomExactAt S.f.hom S.g.hom) : HomExactAt T.f.hom T.g.hom := by
  apply h.congr T.f.hom T.g.hom (asIso E.hom.τ₁).toLinearEquiv
    (asIso E.hom.τ₂).toLinearEquiv (asIso E.hom.τ₃).toLinearEquiv
  · exact congrArg (fun f : S.X₁ ⟶ T.X₂ => f.hom) E.hom.comm₁₂
  · exact congrArg (fun f : S.X₂ ⟶ T.X₃ => f.hom) E.hom.comm₂₃

end HomExactAt

namespace CompleteComparison

noncomputable def reverseShortComplexIso
    (K : CochainComplex (ModuleCat.{u} R) ℤ) (i j l i' j' l' : ℤ)
    (hi : negIndexEmbedding.f i = i') (hj : negIndexEmbedding.f j = j')
    (hl : negIndexEmbedding.f l = l') :
    (chainOfCochain K).sc' i' j' l' ≅ K.sc' i j l :=
  ShortComplex.isoMk (K.extendXIso negIndexEmbedding hi)
    (K.extendXIso negIndexEmbedding hj) (K.extendXIso negIndexEmbedding hl)
    (by
      change (K.extendXIso negIndexEmbedding hi).hom ≫ K.d i j =
        (chainOfCochain K).d i' j' ≫ (K.extendXIso negIndexEmbedding hj).hom
      rw [K.extend_d_eq negIndexEmbedding hi hj]
      simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id])
    (by
      change (K.extendXIso negIndexEmbedding hj).hom ≫ K.d j l =
        (chainOfCochain K).d j' l' ≫ (K.extendXIso negIndexEmbedding hl).hom
      rw [K.extend_d_eq negIndexEmbedding hj hl]
      simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id])

end CompleteComparison

end ArExplicit

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Complete_TateKoszul
attribute [-instance] _root_.OAI.ArExplicit.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ArExplicit.TateKoszul

universe u
variable {k : Type u} [Field k]
variable (H : ℤ → Type u) [∀ a, AddCommGroup (H a)] [∀ a, Module k (H a)]

variable {H}

variable {x y : ∀ a : ℤ, H a →ₗ[k] H (a + 3)}

@[simp] theorem column_apply (a : ℤ) (v : H a) : column (x := x) (y := y) a v =
    (y a v, -(x a v)) := rfl

end ArExplicit.TateKoszul

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Cones_ConeExactness
attribute [-instance] _root_.OAI.ArExplicit.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ArExplicit

variable {R Q₁ Q₀ Q₂ P₁ P₀ P₂ : Type*} [Ring R]
variable [AddCommGroup Q₁] [Module R Q₁] [AddCommGroup Q₀] [Module R Q₀]
variable [AddCommGroup Q₂] [Module R Q₂] [AddCommGroup P₁] [Module R P₁]
variable [AddCommGroup P₀] [Module R P₀] [AddCommGroup P₂] [Module R P₂]

theorem coneBlock_comp_zero (eQ : Q₁ →ₗ[R] Q₀) (dQ : Q₀ →ₗ[R] Q₂)
    (eP : P₁ →ₗ[R] P₀) (dP : P₀ →ₗ[R] P₂)
    (f₁ : P₁ →ₗ[R] Q₀) (f₀ : P₀ →ₗ[R] Q₂)
    (hQ : dQ.comp eQ = 0) (hP : dP.comp eP = 0)
    (hf : dQ.comp f₁ = f₀.comp eP) :
    (coneBlock dQ dP f₀).comp (coneBlock eQ eP f₁) = 0 := by
  apply LinearMap.ext
  rintro ⟨x, y⟩
  apply Prod.ext
  · change dQ (eQ x + f₁ y) + f₀ (-eP y) = 0
    rw [map_add, show dQ (eQ x) = 0 from DFunLike.congr_fun hQ x, zero_add,
      show dQ (f₁ y) = f₀ (eP y) from DFunLike.congr_fun hf y, map_neg, add_neg_cancel]
  · change -dP (-eP y) = 0
    rw [map_neg, neg_neg]
    exact DFunLike.congr_fun hP y

theorem coneBlock_homExact (eQ : Q₁ →ₗ[R] Q₀) (dQ : Q₀ →ₗ[R] Q₂)
    (eP : P₁ →ₗ[R] P₀) (dP : P₀ →ₗ[R] P₂)
    (f₁ : P₁ →ₗ[R] Q₀) (f₀ : P₀ →ₗ[R] Q₂)
    (hQ : HomExactAt eQ dQ) (hP : HomExactAt eP dP)
    (hf : dQ.comp f₁ = f₀.comp eP) :
    HomExactAt (coneBlock eQ eP f₁) (coneBlock dQ dP f₀) := by
  intro g hg
  let a := g.comp (LinearMap.inl R Q₀ P₀)
  let b := g.comp (LinearMap.inr R Q₀ P₀)
  have ha : a.comp eQ = 0 := by
    ext x
    have h := DFunLike.congr_fun hg (x, 0)
    simpa [coneBlock, a] using h
  obtain ⟨u, hu⟩ := hQ a ha
  have hb : (b - u.comp f₀).comp eP = 0 := by
    ext y
    have h := DFunLike.congr_fun hg (0, y)
    have hab : a (f₁ y) = b (eP y) := by
      have hsplit : g (f₁ y, -eP y) = a (f₁ y) - b (eP y) := by
        rw [show (f₁ y, -eP y) = (f₁ y, 0) + (0, -eP y) by ext <;> simp]
        rw [map_add]
        change a (f₁ y) + b (-eP y) = _
        rw [map_neg, sub_eq_add_neg]
      apply sub_eq_zero.mp
      rw [← hsplit]
      simpa [coneBlock] using h
    change b (eP y) - u (f₀ (eP y)) = 0
    rw [← show dQ (f₁ y) = f₀ (eP y) from DFunLike.congr_fun hf y,
      show u (dQ (f₁ y)) = a (f₁ y) from DFunLike.congr_fun hu (f₁ y), hab, sub_self]
  obtain ⟨v, hv⟩ := hP (b - u.comp f₀) hb
  refine ⟨u.coprod (-v), ?_⟩
  apply LinearMap.ext
  rintro ⟨x, y⟩
  change u (dQ x + f₀ y) + -v (-dP y) = g (x, y)
  rw [map_add, map_neg, neg_neg,
    show u (dQ x) = a x from DFunLike.congr_fun hu x,
    show v (dP y) = b y - u (f₀ y) from DFunLike.congr_fun hv y]
  have hsplit : a x + b y = g (x, y) := by
    change g (x, 0) + g (0, y) = _
    rw [← map_add]
    simp
  rw [← hsplit]
  abel

end ArExplicit

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_HomComplex_FullHomProducts
attribute [-instance] _root_.OAI.ArExplicit.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open CategoryTheory
open CochainComplex CochainComplex.HomComplex

namespace ArExplicit.CompleteComparison

universe u

variable {R : Type u} [Ring R]
variable {K L M : CochainComplex (ModuleCat.{u} R) ℤ} {n m : ℤ}

noncomputable def cocycleComparisonMap (x : Cocycle K L n) :
    chainOfCochain K ⟶ chainOfCochain (L⟦n⟧) :=
  HomologicalComplex.extendMap (Cocycle.equivHomShift.symm x) negIndexEmbedding

end ArExplicit.CompleteComparison

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Cones_MappingConeModule
attribute [-instance] _root_.OAI.ArExplicit.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ArExplicit

open CategoryTheory HomologicalComplex
open CochainComplex CochainComplex.HomComplex CochainComplex.mappingCone

universe u

variable {R : Type u} [Ring R]
variable {F G : CochainComplex (ModuleCat.{u} R) ℤ} (φ : F ⟶ G)

theorem coneTermEquiv_differential (i : ℤ) :
    (coneTermEquiv φ (i + 1)).toLinearMap.comp ((mappingCone φ).d i (i + 1)).hom =
      (coneBlock (G.d i (i + 1)).hom (F.d (i + 1) ((i + 1) + 1)).hom
        (φ.f (i + 1)).hom).comp (coneTermEquiv φ i).toLinearMap := by
  apply LinearMap.ext
  intro x
  apply Prod.ext
  · change (((mappingCone φ).d i (i + 1) ≫ (snd φ).v (i + 1) (i + 1) (add_zero _)).hom x) =
      (G.d i (i + 1)).hom (((snd φ).v i i (add_zero _)).hom x) +
        (φ.f (i + 1)).hom (((fst φ).1.v i (i + 1) rfl).hom x)
    rw [d_snd_v φ i (i + 1) rfl]
    exact add_comm _ _
  · change (((mappingCone φ).d i (i + 1) ≫ (fst φ).1.v (i + 1) ((i + 1) + 1) rfl).hom x) =
      -(F.d (i + 1) ((i + 1) + 1)).hom (((fst φ).1.v i (i + 1) rfl).hom x)
    rw [d_fst_v φ i (i + 1) ((i + 1) + 1) rfl rfl]
    rfl

end ArExplicit

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Cones_MappingConeTotal
attribute [-instance] _root_.OAI.ArExplicit.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ArExplicit

open CategoryTheory HomologicalComplex CompleteComparison
open CochainComplex CochainComplex.HomComplex

universe u

variable {R : Type u} [Ring R]
variable {F G : CochainComplex (ModuleCat.{u} R) ℤ} (φ : F ⟶ G)

def coneBlockShortComplex (i : ℤ) : ShortComplex (ModuleCat.{u} R) :=
  ShortComplex.mk
    (ModuleCat.ofHom (coneBlock (G.d i (i + 1)).hom (F.d (i + 1) ((i + 1) + 1)).hom
      (φ.f (i + 1)).hom))
    (ModuleCat.ofHom (coneBlock (G.d (i + 1) ((i + 1) + 1)).hom
      (F.d ((i + 1) + 1) (((i + 1) + 1) + 1)).hom (φ.f ((i + 1) + 1)).hom))
    (by
      apply ModuleCat.hom_ext
      apply coneBlock_comp_zero
      · exact congrArg ModuleCat.Hom.hom (G.d_comp_d _ _ _)
      · exact congrArg ModuleCat.Hom.hom (F.d_comp_d _ _ _)
      · exact congrArg ModuleCat.Hom.hom (φ.comm _ _))

def coneShortComplexIso (i : ℤ) :
    (mappingCone φ).sc' i (i + 1) ((i + 1) + 1) ≅ coneBlockShortComplex φ i :=
  ShortComplex.isoMk (coneTermEquiv φ i).toModuleIso
    (coneTermEquiv φ (i + 1)).toModuleIso (coneTermEquiv φ ((i + 1) + 1)).toModuleIso
    (by
      apply ModuleCat.hom_ext
      exact (coneTermEquiv_differential φ i).symm)
    (by
      apply ModuleCat.hom_ext
      exact (coneTermEquiv_differential φ (i + 1)).symm)

end ArExplicit

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Cones_MappingConeCokernel
attribute [-instance] _root_.OAI.ArExplicit.finitePiProjective
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

def rawConeBlockEquiv : CochainCokernel (mappingCone φ) ≃ₗ[R]
    ConeQuotientMap.Cone (F.d 0 1).hom (G.d (-1) 0).hom (φ.f 0).hom :=
  cokernelLinearCongr _ _ (conePreviousTermEquiv φ) (coneTermEquiv φ 0) (by
    simpa [conePreviousTermEquiv] using coneTermEquiv_differential φ (-1))

variable {L : Type u} [AddCommGroup L] [Module R L]
variable (p : CochainCokernel G →ₗ[R] L)
variable (hex : Function.Exact (cochainCokernelMap φ) p)

theorem rawCokernelMap_comm :
    (LinearMap.range (G.d (-1) 0).hom).mkQ.comp (φ.f 0).hom =
    (cochainCokernelMap φ).comp (LinearMap.range (F.d (-1) 0).hom).mkQ := by
  apply LinearMap.ext
  intro x
  rfl

end ArExplicit

end

end OAI
end


