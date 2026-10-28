-- Prove2me | Definitions.Def_OAIQ031A053
-- name    : OAIQ031A053
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T14:07:08.95188+00:00
-- url     : https://prove2.me/theorems/dcacfc67-633e-485e-9253-295fb31d0195
-- title:
--   Definitions bundle OAIQ031A053 of the split of OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.ArExplicit.Statement.main`, carved from OpenAI's openai/math development (OpenAI, *An explicit counterexample to the Auslander-Reiten conjecture (result family 199)*, OpenAI Math Release, September 23, 2026, result family 199, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 14 declarations of OpenAI's Lean: 5 definitions and 9 theorems. The definitions and types are `OAI.ArExplicit.BalancedTensor.congr`, `OAI.ArExplicit.BalancedTensor.congrLeft`, `OAI.ArExplicit.CompleteComparison.completeTailHom`, `OAI.ArExplicit.CompleteComparison.nonnegativeTailMap`, `OAI.ArExplicit.TateKoszul.positiveAt`.
--
--   **Sources.** They come from these modules of lean/OAI/Algebra, in whole or in part: [`AuslanderReiten_Complete_CompleteTailMap`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Complete/CompleteTailMap.lean), [`AuslanderReiten_Complete_TateKoszul`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Complete/TateKoszul.lean), [`AuslanderReiten_Ext_ExtIsoFunctor`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Ext/ExtIsoFunctor.lean), [`AuslanderReiten_HomComplex_FullHomHomotopyMaps`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/HomComplex/FullHomHomotopyMaps.lean), [`AuslanderReiten_HomComplex_FullHomShiftedMaps`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/HomComplex/FullHomShiftedMaps.lean), [`AuslanderReiten_Tensor_BalancedTensorEquiv`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Tensor/BalancedTensorEquiv.lean).
--
--   **Imports.** It imports the bundles `OAIQ031A026`, `OAIQ031A031`, `OAIQ031A035` and `OAIQ031A036` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ031A070`, `OAIQ031A071`, `OAIQ031A074` and `OAIQ031A076`.
-- source:
--   OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 199; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/An-explicit-counterexample-to-the-Auslander-Reiten-conjecture-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algebra at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ031A026
import Definitions.Def_OAIQ031A031
import Definitions.Def_OAIQ031A035
import Definitions.Def_OAIQ031A036

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Complete_CompleteTailMap
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory
namespace ArExplicit.CompleteComparison
universe u
variable {R : Type u} [Ring R]
variable {P Q : ChainComplex (ModuleCat.{u} R) ℤ} (f : P ⟶ Q)

def nonnegativeTailMap : nonnegativeTail P ⟶ nonnegativeTail Q where
  f n := f.f (n : ℤ)
  comm' i j h := by
    change j+1=i at h
    subst i
    rw [nonnegativeTail_d, nonnegativeTail_d]
    exact f.comm _ _

theorem nonnegativeTailMap_augmentation :
    (nonnegativeTailMap f).f 0 ≫ (nonnegativeTailAugmentation Q).f 0 =
      (nonnegativeTailAugmentation P).f 0 ≫ ModuleCat.ofHom (cokernelMap f 0) := by
  rw [nonnegativeTailAugmentation_f_zero, nonnegativeTailAugmentation_f_zero]
  rfl

def completeTailHom (hP : TotallyAcyclicComplex P) (hQ : TotallyAcyclicComplex Q) :
    ProjectiveResolution.Hom (completeExtResolution hP) (completeExtResolution hQ)
      (ModuleCat.ofHom (cokernelMap f 0)) where
  hom := nonnegativeTailMap f
  hom_f_zero_comp_π_f_zero := by
    erw [ChainComplex.single₀_map_f_zero]
    exact nonnegativeTailMap_augmentation f

end ArExplicit.CompleteComparison

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Complete_TateKoszul
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
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

variable {x y : ∀ a : ℤ, H a →ₗ[k] H (a + 3)} (M : Model x y)

def positiveAt (a : ℤ) (n : ℕ) (ha : a = 3 * (n : ℤ)) :
    H a ≃ₗ[k] BinaryKoszul.Piece k n :=
  (degreeEquiv H ha).trans (M.positive n)

end ArExplicit.TateKoszul

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Ext_ExtIsoFunctor
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
namespace ArExplicit
universe u v w
variable {k : Type u} [CommRing k]
variable {C : Type v} [Category.{u} C] [Abelian C] [HasExt.{u} C] [Linear k C]
variable {D : Type w} [Category.{u} D] [Abelian D] [HasExt.{u} D] [Linear k D]
variable {X Y Z : C}

variable (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]

theorem selfExtIso_conjugated_functor
    (G : C ⥤ C) [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (e : Y ≅ X) (E : Y ≅ G.obj Y) (n : ℕ) (x : Ext X X n) :
    selfExtIso (k := k) e n
      (selfExtIso (k := k) E.symm n
        ((selfExtIso (k := k) e.symm n x).mapExactFunctor G)) =
    selfExtIso (k := k) (e.symm ≪≫ E ≪≫ G.mapIso e).symm n
      (x.mapExactFunctor G) := by
  rw [selfExtIso_mapExactFunctor, selfExtIso_trans, selfExtIso_trans]
  have heq : G.mapIso e.symm ≪≫ E.symm ≪≫ e =
      (e.symm ≪≫ E ≪≫ G.mapIso e).symm := by
    apply Iso.ext
    simp
  rw [heq]

end ArExplicit

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_HomComplex_FullHomShiftedMaps
attribute [-instance] _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ArExplicit
open CategoryTheory
open CochainComplex CochainComplex.HomComplex
universe u v w
variable (k : Type u) [CommRing k]
variable {C : Type w} [Category.{v} C] [Preadditive C] [Linear k C]
variable {K L M : CochainComplex C ℤ} (n : ℤ)

theorem fullHomShiftedHomotopyEquiv_postcomp (f : L ⟶ M) (x : CohomologyClass K L n) :
    fullHomShiftedHomotopyEquiv k K M n (fullHomPostcomp f n x) =
      fullHomShiftedHomotopyEquiv k K L n x ≫
        ((HomotopyCategory.quotient C _).map f)⟦n⟧' := by
  obtain ⟨x, rfl⟩ := CohomologyClass.mk_surjective x
  rw [fullHomPostcomp_mk, fullHomShiftedHomotopyEquiv_mk,
    fullHomShiftedHomotopyEquiv_mk, Cocycle.equivHomShift_symm_postcomp,
    Functor.map_comp, Category.assoc]
  simpa only [Category.assoc, Iso.app_hom] using congrArg
    (fun g => (HomotopyCategory.quotient C _).map (Cocycle.equivHomShift.symm x) ≫ g)
    ((HomotopyCategory.quotient C _).commShiftIso_hom_naturality f n)

end ArExplicit

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_HomComplex_FullHomHomotopyMaps
attribute [-instance] _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CochainComplex.HomComplex
namespace ArExplicit
universe u v w
variable (k : Type u) [CommRing k]
variable {C : Type w} [Category.{v} C] [Preadditive C] [Linear k C]
variable {K L M : CochainComplex C ℤ} (n : ℤ)
include k

theorem fullHomPostcomp_congr {f g : L ⟶ M}
    (h : (HomotopyCategory.quotient C _).map f = (HomotopyCategory.quotient C _).map g)
    (x : CohomologyClass K L n) : fullHomPostcomp f n x = fullHomPostcomp g n x := by
  apply (fullHomShiftedHomotopyEquiv k K M n).injective
  rw [fullHomShiftedHomotopyEquiv_postcomp, fullHomShiftedHomotopyEquiv_postcomp, h]

theorem fullHomPostcomp_id (x : CohomologyClass K L n) :
    fullHomPostcomp (𝟙 L) n x = x := by
  apply (fullHomShiftedHomotopyEquiv k K L n).injective
  rw [fullHomShiftedHomotopyEquiv_postcomp, CategoryTheory.Functor.map_id,
    CategoryTheory.Functor.map_id, Category.comp_id]

theorem fullHomPostcomp_homotopy_inverse (f : L ⟶ M) (g : M ⟶ L)
    (h : (HomotopyCategory.quotient C _).map (f ≫ g) = 𝟙 _)
    (x : CohomologyClass K L n) : fullHomPostcomp g n (fullHomPostcomp f n x) = x := by
  rw [fullHomPostcomp_comp]
  rw [fullHomPostcomp_congr k n (h.trans (CategoryTheory.Functor.map_id _ _).symm),
    fullHomPostcomp_id k n]

theorem fullHomPostcomp_bijective (f : L ⟶ M) (g : M ⟶ L)
    (hfg : (HomotopyCategory.quotient C _).map (f ≫ g) = 𝟙 _)
    (hgf : (HomotopyCategory.quotient C _).map (g ≫ f) = 𝟙 _) :
    Function.Bijective (fullHomPostcomp (K := K) f n) := by
  constructor
  · intro x y h
    have hh := congrArg (fullHomPostcomp g n) h
    simpa only [fullHomPostcomp_homotopy_inverse k n f g hfg] using hh
  · intro x
    exact ⟨fullHomPostcomp g n x, fullHomPostcomp_homotopy_inverse k n g f hgf x⟩

end ArExplicit

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Tensor_BalancedTensorEquiv
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ArExplicit.BalancedTensor
universe u
variable {k R F F' M M' : Type u} [CommRing k] [Ring R]
  [AddCommGroup F] [AddCommGroup F'] [AddCommGroup M] [AddCommGroup M']
  [Module k F] [Module k F'] [Module k M] [Module k M']
  [Module Rᵐᵒᵖ F] [Module Rᵐᵒᵖ F'] [Module R M] [Module R M']
variable (e : F ≃ₗ[k] F') (v : M ≃ₗ[k] M')
  (he : ∀ (r : Rᵐᵒᵖ) x, e (r • x) = r • e x)
  (hv : ∀ (r : R) x, v (r • x) = r • v x)

include he hv

def congr : BalancedTensor k R F M ≃ₗ[k] BalancedTensor k R F' M' where
  __ := map e.toLinearMap v.toLinearMap he hv
  invFun := map e.symm.toLinearMap v.symm.toLinearMap
    (inverse_equivariant_right e he) (inverse_equivariant_left v hv)
  left_inv z := by
    change map e.symm.toLinearMap v.symm.toLinearMap
      (inverse_equivariant_right e he) (inverse_equivariant_left v hv)
      (map e.toLinearMap v.toLinearMap he hv z) = z
    induction z using induction_on with
    | zero => simp
    | add z w hz hw => simp only [map_add, hz, hw]
    | tmul f m => simp only [map_tmul, LinearEquiv.coe_coe,
        LinearEquiv.symm_apply_apply]
  right_inv z := by
    change map e.toLinearMap v.toLinearMap he hv
      (map e.symm.toLinearMap v.symm.toLinearMap
        (inverse_equivariant_right e he) (inverse_equivariant_left v hv) z) = z
    induction z using induction_on with
    | zero => simp
    | add z w hz hw => simp only [map_add, hz, hw]
    | tmul f m => simp only [map_tmul, LinearEquiv.coe_coe,
        LinearEquiv.apply_symm_apply]

@[simp] theorem congr_tmul (f : F) (m : M) :
    congr e v he hv (tmul f m) = tmul (e f) (v m) := rfl

variable {S : Type u} [Ring S] [Module S F] [Module S F']
  [SMulCommClass k S F] [SMulCommClass k S F']
  [SMulCommClass S Rᵐᵒᵖ F] [SMulCommClass S Rᵐᵒᵖ F']
  (hs : ∀ (s : S) x, e (s • x) = s • e x)

include hs

theorem congr_smul (s : S) (z : BalancedTensor k R F M) :
    congr e v he hv (s • z) = s • congr e v he hv z := by
  induction z using induction_on with
  | zero => simp
  | add z w hz hw => simp only [smul_add, map_add, hz, hw]
  | tmul f m => rw [smul_tmul, congr_tmul, hs, congr_tmul, smul_tmul]

def congrLeft : BalancedTensor k R F M ≃ₗ[S] BalancedTensor k R F' M' where
  __ := (congr e v he hv).toAddEquiv
  map_smul' := congr_smul e v he hv hs

end ArExplicit.BalancedTensor

end

end OAI
end


