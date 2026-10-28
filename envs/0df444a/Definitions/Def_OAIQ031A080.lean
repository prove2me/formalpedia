-- Prove2me | Definitions.Def_OAIQ031A080
-- name    : OAIQ031A080
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T14:23:05.453123+00:00
-- url     : https://prove2.me/theorems/f7115440-0efb-4ca6-80e8-5fe4341fb76c
-- title:
--   Definitions bundle OAIQ031A080 of the split of OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.ArExplicit.Statement.main`, carved from OpenAI's openai/math development (OpenAI, *An explicit counterexample to the Auslander-Reiten conjecture (result family 199)*, OpenAI Math Release, September 23, 2026, result family 199, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 22 declarations of OpenAI's Lean: 11 definitions and 11 theorems. The definitions and types are `OAI.ArExplicit.ExternalTensor.augmentation`, `OAI.ArExplicit.ExternalTensor.firstComparison`, `OAI.ArExplicit.ExternalTensor.homCochainTermEquiv`, `OAI.ArExplicit.ExternalTensor.homEquiv`, `OAI.ArExplicit.ExternalTensor.projectiveResolution`, `OAI.ArExplicit.ExternalTensor.scalarForgetTotalIso`, `OAI.ArExplicit.ExternalTensor.singleTotalIso`, `OAI.ArExplicit.ExternalTensor.singleTotalTermIso`, `OAI.ArExplicit.ExternalTensor.singleTotalZeroEquiv`, `OAI.ArExplicit.ModuleBar.suffixComparison`, `OAI.ArExplicit.TwoCone.middleTerm`.
--
--   **Sources.** They come from these modules of lean/OAI/Algebra, in whole or in part: [`AuslanderReiten_Bar_ModuleBarSuffix`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Bar/ModuleBarSuffix.lean), [`AuslanderReiten_Complete_CompleteShiftDual`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Complete/CompleteShiftDual.lean), [`AuslanderReiten_Cones_TwoConeSkeleton`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Cones/TwoConeSkeleton.lean), [`AuslanderReiten_Duality_DualResolution`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Duality/DualResolution.lean), [`AuslanderReiten_Tensor_ExternalTensorCubicExt`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Tensor/ExternalTensorCubicExt.lean), [`AuslanderReiten_Tensor_ExternalTensorExact`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Tensor/ExternalTensorExact.lean), [`AuslanderReiten_Tensor_ExternalTensorForget`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Tensor/ExternalTensorForget.lean), [`AuslanderReiten_Tensor_ExternalTensorHom`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Tensor/ExternalTensorHom.lean), [`AuslanderReiten_Tensor_ExternalTensorHomComplex`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Tensor/ExternalTensorHomComplex.lean), [`AuslanderReiten_Tensor_ExternalTensorResolution`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Tensor/ExternalTensorResolution.lean), [`AuslanderReiten_Tensor_ExternalTensorSingle`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Tensor/ExternalTensorSingle.lean).
--
--   **Imports.** It imports the bundles `OAIQ031A061`, `OAIQ031A062`, `OAIQ031A063`, `OAIQ031A064` and `OAIQ031A065` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ031A093`, `OAIQ031A094`, `OAIQ031A095`, `OAIQ031A096`, `OAIQ031A098`, `OAIQ031A100` and `OAIQ031A101`.
-- source:
--   OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 199; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/An-explicit-counterexample-to-the-Auslander-Reiten-conjecture-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algebra at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ031A061
import Definitions.Def_OAIQ031A062
import Definitions.Def_OAIQ031A063
import Definitions.Def_OAIQ031A064
import Definitions.Def_OAIQ031A065

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Bar_ModuleBarSuffix
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
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

def suffixComparison (p : AbsoluteBar.Cochain3 k R) : (n : ℕ) → object k R M (n + 3) →ₗ[k] object k R M n
  | 0 => suffix3 k R M p
  | n + 1 => (suffixComparison p n).lTensor R

end ArExplicit.ModuleBar

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Complete_CompleteShiftDual
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open CategoryTheory

namespace ArExplicit

universe u

variable {R : Type u} [Ring R]

namespace DualExactCochain

open CompleteComparison

theorem of_chain {K : CochainComplex (ModuleCat.{u} R) ℤ}
    (hK : TotallyAcyclicComplex (chainOfCochain K)) : DualExactCochain K := by
  intro i
  let E := reverseShortComplexIso K (i - 1) i (i + 1) (-i + 1) (-i) (-i - 1)
    (by change -(i - 1) = -i + 1; omega) rfl (by change -(i + 1) = -i - 1; omega)
  exact HomExactAt.of_shortComplex_iso E (hK.dualExact (-i))

end DualExactCochain

end ArExplicit

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Cones_TwoConeSkeleton
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
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

abbrev middleTerm (n : ℕ) := D.term (n + 2) × D.term (n + 2)

end ArExplicit.TwoCone

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Duality_DualResolution
attribute [-instance] _root_.OAI.ArExplicit.A.instIsTwoSidedAugmentationIdeal _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.Resolution.instIsScalarTowerTSimple _root_.OAI.ArExplicit.Resolution.instModuleTSimple _root_.OAI.ArExplicit.Resolution.simpleRightAction _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ArExplicit.Resolution

open ArExplicit.Letter ArExplicit.BaseAlgebra

variable {k : Type*} [Field k] (q : k)

local notation "C" => BaseAlgebra k q

theorem rightE_expand (a : rightE q) : (a : C) =
    (a : C).coeff e • basisVector q e + (a : C).coeff x • basisVector q x +
    (a : C).coeff y • basisVector q y + (a : C).coeff z • basisVector q z +
    (a : C).coeff u • basisVector q u + (a : C).coeff v • basisVector q v := by
  ext i
  cases i <;> simp

end ArExplicit.Resolution

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Tensor_ExternalTensorForget
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ExternalTensor.hasHomCochainTotal _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped TensorProduct
namespace ArExplicit.ExternalTensor
universe u
variable (k A B : Type u) [Field k] [Ring A] [Ring B] [Algebra k A] [Algebra k B]
attribute [local instance] moduleCatBaseModule moduleCatBaseTower

variable (P : ChainComplex (ModuleCat.{u} A) ℕ) (Q : ChainComplex (ModuleCat.{u} B) ℕ)

theorem scalarHorizontal_comp (i j n : ℕ) (h : i+j=n+1) :
    scalarHorizontal k A B P Q i j n ≫ (forgetTermIso k A B P Q n).inv =
      ModuleCat.ofHom ((horizontal k A B P Q i j n).hom.restrictScalars k) := by
  cases i with
  | zero =>
    rw [show scalarHorizontal k A B P Q 0 j n = 0 from
      mapBifunctor.d₁_eq_zero _ _ _ _ 0 j n (by change ¬ ((ComplexShape.down ℕ).next 0 + 1 = 0); omega),
      zero_comp, horizontal_zero]
    rfl
  | succ i =>
    have hij : i+j=n := by omega
    dsimp only [scalarHorizontal]
    rw [mapBifunctor.d₁_eq _ _ _ _ (show (ComplexShape.down ℕ).Rel (i+1) i from rfl) j n hij]
    change ((1 : ℤˣ) • _) ≫ _ = _
    rw [one_smul, Category.assoc, scalarInclusion_forgetTermIso_inv,
      horizontal_succ k A B P Q i j n hij]
    apply ModuleCat.hom_ext
    apply TensorProduct.ext
    apply LinearMap.ext
    intro x
    apply LinearMap.ext
    intro y
    rfl

theorem scalarInclusion_d (i j n n' : ℕ) (h : i+j=n) :
    scalarInclusion k A B P Q i j n h ≫ (scalarTotal k A B P Q).d n n' =
      scalarHorizontal k A B P Q i j n' + scalarVertical k A B P Q i j n' := by
  change ιMapBifunctor _ _ _ _ i j n h ≫ _ = _
  rw [mapBifunctor.d_eq, Preadditive.comp_add, mapBifunctor.ι_D₁, mapBifunctor.ι_D₂]

def scalarForgetTotalIso : scalarTotal k A B P Q ≅
    forgetComplex k (A ⊗[k] B) (complex k A B P Q) :=
  HomologicalComplex.Hom.isoOfComponents (fun n => (forgetTermIso k A B P Q n).symm)
    (fun n m h => by
      have hnm : m+1=n := h
      subst n
      apply mapBifunctor.hom_ext
      intro i j hij
      change scalarInclusion k A B P Q i j (m+1) hij ≫
        ((forgetTermIso k A B P Q (m+1)).inv ≫ _) =
        scalarInclusion k A B P Q i j (m+1) hij ≫
        ((scalarTotal k A B P Q).d (m+1) m ≫ (forgetTermIso k A B P Q m).inv)
      rw [← Category.assoc, scalarInclusion_forgetTermIso_inv, ← Category.assoc,
        scalarInclusion_d, Preadditive.add_comp,
        scalarHorizontal_comp k A B P Q i j m hij,
        scalarVertical_comp k A B P Q i j m hij]
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      exact congrArg (fun f => f.hom x) (inclusion_d k A B P Q i j (m+1) m hij))

variable {P Q}
variable {P' : ChainComplex (ModuleCat.{u} A) ℕ} {Q' : ChainComplex (ModuleCat.{u} B) ℕ}

theorem scalarForgetTotalIso_naturality (f : P ⟶ P') (g : Q ⟶ Q') :
    mapBifunctorMap (((forgetField k A).mapHomologicalComplex _).map f)
      (((forgetField k B).mapHomologicalComplex _).map g)
      (MonoidalCategory.curriedTensor (ModuleCat.{u} k)) (ComplexShape.down ℕ) ≫
        (scalarForgetTotalIso k A B P' Q').hom =
      (scalarForgetTotalIso k A B P Q).hom ≫
        (((forgetField k (A ⊗[k] B)).mapHomologicalComplex _).map
          (mapBifunctorMap f g (bifunctor k A B) (ComplexShape.down ℕ))) := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply mapBifunctor.hom_ext
  intro i j hij
  change scalarInclusion k A B P Q i j n hij ≫
    ((mapBifunctorMap _ _ _ _).f n ≫ (forgetTermIso k A B P' Q' n).inv) =
      scalarInclusion k A B P Q i j n hij ≫
        ((forgetTermIso k A B P Q n).inv ≫ _)
  rw [← Category.assoc, ι_mapBifunctorMap, Category.assoc, Category.assoc,
    scalarInclusion_forgetTermIso_inv, ← Category.assoc, scalarInclusion_forgetTermIso_inv]
  apply ModuleCat.hom_ext
  apply TensorProduct.ext
  apply LinearMap.ext
  intro x
  apply LinearMap.ext
  intro y
  exact (congrArg (fun u => u.hom (x ⊗ₜ[k] y))
    (ι_mapBifunctorMap f g (bifunctor k A B) (ComplexShape.down ℕ) i j n hij)).symm

end ArExplicit.ExternalTensor

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Tensor_ExternalTensorHom
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct
namespace ArExplicit.ExternalTensor
universe u
variable (k A B : Type u) [Field k] [Ring A] [Ring B] [Algebra k A] [Algebra k B]
variable {M N U V : Type u}
variable [AddCommGroup M] [AddCommGroup N] [AddCommGroup U] [AddCommGroup V]
variable [Module k M] [Module k N] [Module k U] [Module k V]
variable [Module A M] [Module B N] [Module A U] [Module B V]
variable [IsScalarTower k A M] [IsScalarTower k B N] [IsScalarTower k A U] [IsScalarTower k B V]

variable {M' N' : Type u} [AddCommGroup M'] [AddCommGroup N']
variable [Module k M'] [Module k N'] [Module A M'] [Module B N']
variable [IsScalarTower k A M'] [IsScalarTower k B N']

theorem homMap_bijective [Module.Finite A M] [Module.Projective A M]
    [Module.Finite B N] [Module.Projective B N] :
    Function.Bijective (homMap k A B (M := M) (N := N) (U := U) (V := V)) := by
  obtain ⟨n,p,hp⟩ := Module.Finite.exists_fin' A M
  obtain ⟨m,q,hq⟩ := Module.Finite.exists_fin' B N
  obtain ⟨s,hs⟩ := Module.projective_lifting_property p (LinearMap.id : M →ₗ[A] M) hp
  obtain ⟨t,ht⟩ := Module.projective_lifting_property q (LinearMap.id : N →ₗ[B] N) hq
  let a := TensorProduct.map (LinearMap.lcomp k U p) (LinearMap.lcomp k V q)
  let b := TensorProduct.map (LinearMap.lcomp k U s) (LinearMap.lcomp k V t)
  have hba (x : (M →ₗ[A] U) ⊗[k] (N →ₗ[B] V)) : b (a x) = x := by
    induction x using OAI.tensorInductionOn with
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul u v =>
      change ((u.comp p).comp s) ⊗ₜ[k] ((v.comp q).comp t) = u ⊗ₜ[k] v
      rw [LinearMap.comp_assoc, LinearMap.comp_assoc, hs, ht, LinearMap.comp_id, LinearMap.comp_id]
  have hsplit : (map k A B p q).comp (map k A B s t) = LinearMap.id := by
    apply LinearMap.restrictScalars_injective k
    apply TensorProduct.ext
    apply LinearMap.ext
    intro x
    apply LinearMap.ext
    intro y
    change p (s x) ⊗ₜ[k] q (t y) = x ⊗ₜ[k] y
    rw [show p (s x) = x from DFunLike.congr_fun hs x,
      show q (t y) = y from DFunLike.congr_fun ht y]
  have hfree := homMap_bijective_free k A B (U := U) (V := V) n m
  constructor
  · intro x y hxy
    have hab : a x = a y := hfree.1 (by simp only [a, homMap_precomp, hxy])
    exact (hba x).symm.trans ((congrArg b hab).trans (hba y))
  · intro f
    obtain ⟨x,hx⟩ := hfree.2 (f.comp (map k A B p q))
    refine ⟨b x, ?_⟩
    rw [show b = TensorProduct.map (LinearMap.lcomp k U s) (LinearMap.lcomp k V t) from rfl,
      homMap_precomp, hx, LinearMap.comp_assoc, hsplit, LinearMap.comp_id]

def homEquiv [Module.Finite A M] [Module.Projective A M]
    [Module.Finite B N] [Module.Projective B N] :
    (M →ₗ[A] U) ⊗[k] (N →ₗ[B] V) ≃ₗ[k]
      (moduleObject k A B M N →ₗ[A ⊗[k] B] moduleObject k A B U V) :=
  LinearEquiv.ofBijective (homMap k A B) (homMap_bijective k A B)

end ArExplicit.ExternalTensor

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Tensor_ExternalTensorHomComplex
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ExternalTensor.diagonalZeroUnique _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped TensorProduct
namespace ArExplicit.ExternalTensor
universe u
variable (k A B : Type u) [Field k] [Ring A] [Ring B] [Algebra k A] [Algebra k B]
attribute [local instance] moduleCatBaseModule moduleCatBaseTower

variable (P : ChainComplex (ModuleCat.{u} A) ℕ) (Q : ChainComplex (ModuleCat.{u} B) ℕ)

variable (U : ModuleCat.{u} A) (V : ModuleCat.{u} B)

variable [∀ n, Module.Finite A (P.X n)] [∀ n, Module.Projective A (P.X n)]
variable [∀ n, Module.Finite B (Q.X n)] [∀ n, Module.Projective B (Q.X n)]

def homCochainTermEquiv (n : ℕ) :
    (homCochainTotal k A B P Q U V).X n ≃ₗ[k]
      (homCochain k (A ⊗[k] B) (complex k A B P Q) (moduleObject k A B U V)).X n :=
  (homCochainTermCoordinates k A B P Q U V n).trans
    ((LinearEquiv.piCongrRight fun p => homEquiv k A B
      (M := P.X p.val.1) (N := Q.X p.val.2) (U := U) (V := V)).trans
      (homOutTermEquiv k A B P Q U V n).symm)

theorem homCochainTermEquiv_restrict (n : ℕ) (x : (homCochainTotal k A B P Q U V).X n)
    (p : Diagonal n) :
    (homCochainTermEquiv k A B P Q U V n x).comp
      (inclusion k A B P Q p.val.1 p.val.2 n p.property).hom =
      homMap k A B (homCochainTermCoordinates k A B P Q U V n x p) := by
  exact congrFun ((homOutTermEquiv k A B P Q U V n).apply_symm_apply
    ((LinearEquiv.piCongrRight fun p => homEquiv k A B
      (M := P.X p.val.1) (N := Q.X p.val.2) (U := U) (V := V))
        (homCochainTermCoordinates k A B P Q U V n x))) p

@[simp] theorem homCochainTermEquiv_inclusion_same (i j n : ℕ) (h : i+j=n)
    (x : (P.X i →ₗ[A] U) ⊗[k] (Q.X j →ₗ[B] V)) :
    (homCochainTermEquiv k A B P Q U V n (homCochainInclusion k A B P Q U V i j n h x)).comp
      (inclusion k A B P Q i j n h).hom = homMap k A B x := by
  exact (homCochainTermEquiv_restrict k A B P Q U V n _ ⟨(i,j),h⟩).trans
    (congrArg (homMap k A B) ((congrFun (homCochainTermCoordinates_inclusion k A B P Q U V i j n h x) ⟨(i,j),h⟩).trans (Pi.single_eq_same _ _)))

@[simp] theorem homCochainTermEquiv_inclusion_ne (i j n : ℕ) (h : i+j=n)
    (x : (P.X i →ₗ[A] U) ⊗[k] (Q.X j →ₗ[B] V)) (a b : ℕ) (hab : a+b=n)
    (hne : (a,b) ≠ (i,j)) :
    (homCochainTermEquiv k A B P Q U V n (homCochainInclusion k A B P Q U V i j n h x)).comp
      (inclusion k A B P Q a b n hab).hom = 0 := by
  refine (homCochainTermEquiv_restrict k A B P Q U V n _ ⟨(a,b),hab⟩).trans ?_
  rw [homCochainTermCoordinates_inclusion,
    Pi.single_eq_of_ne (show (⟨(a,b),hab⟩ : Diagonal n) ≠ ⟨(i,j),h⟩ from fun hh => hne (congrArg Subtype.val hh)),
    map_zero]

end ArExplicit.ExternalTensor

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Tensor_ExternalTensorExact
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ArExplicit.ExternalTensor
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped TensorProduct
universe u
variable (k A B : Type u) [Field k] [Ring A] [Ring B] [Algebra k A] [Algebra k B]
attribute [local instance] moduleCatBaseModule moduleCatBaseTower

theorem map_quasiIso {P P' : ChainComplex (ModuleCat.{u} A) ℕ}
    {Q Q' : ChainComplex (ModuleCat.{u} B) ℕ} (f : P ⟶ P') (g : Q ⟶ Q')
    [QuasiIso f] [QuasiIso g] :
    QuasiIso (mapBifunctorMap f g (bifunctor k A B) (ComplexShape.down ℕ)) := by
  let Φ := (forgetField k (A ⊗[k] B)).mapHomologicalComplex (ComplexShape.down ℕ)
  let f₀ := ((forgetField k A).mapHomologicalComplex (ComplexShape.down ℕ)).map f
  let g₀ := ((forgetField k B).mapHomologicalComplex (ComplexShape.down ℕ)).map g
  let t := mapBifunctorMap f₀ g₀ (MonoidalCategory.curriedTensor (ModuleCat.{u} k))
    (ComplexShape.down ℕ)
  have : QuasiIso f₀ := inferInstance
  have : QuasiIso g₀ := inferInstance
  have : QuasiIso t := VectorComplex.totalMap_quasiIso k _ f₀ g₀
  have h := scalarForgetTotalIso_naturality k A B f g
  have : QuasiIso ((scalarForgetTotalIso k A B P Q).hom ≫
      Φ.map (mapBifunctorMap f g (bifunctor k A B) (ComplexShape.down ℕ))) := by
    rw [← h]
    infer_instance
  have : QuasiIso (Φ.map (mapBifunctorMap f g (bifunctor k A B) (ComplexShape.down ℕ))) :=
    (quasiIso_iff_comp_left (scalarForgetTotalIso k A B P Q).hom
      (Φ.map (mapBifunctorMap f g (bifunctor k A B) (ComplexShape.down ℕ)))).mp inferInstance
  exact (quasiIso_map_iff_of_preservesHomology _ (forgetField k (A ⊗[k] B))).mp inferInstance

end ArExplicit.ExternalTensor

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Tensor_ExternalTensorSingle
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ExternalTensor.hasHomCochainTotal _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ArExplicit.ExternalTensor
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped TensorProduct
universe u
variable (k A B : Type u) [Field k] [Ring A] [Ring B] [Algebra k A] [Algebra k B]
attribute [local instance] moduleCatBaseModule moduleCatBaseTower

variable (M : ModuleCat.{u} A) (N : ModuleCat.{u} B)

def singleTotalZeroEquiv : (singleTotal k A B M N).X 0 ≃ₗ[A ⊗[k] B]
    moduleObject k A B M N :=
  (termPiEquiv k A B _ _ 0).trans
    { Equiv.piUnique (fun p : Diagonal 0 =>
        summands k A B ((ChainComplex.single₀ (ModuleCat A)).obj M)
          ((ChainComplex.single₀ (ModuleCat B)).obj N) 0 p) with
      map_add' _ _ := rfl
      map_smul' _ _ := rfl }

theorem singleTotal_isZero (n : ℕ) (hn : n ≠ 0) : IsZero ((singleTotal k A B M N).X n) := by
  have (p : Diagonal n) : Subsingleton
      (summands k A B ((ChainComplex.single₀ (ModuleCat A)).obj M)
        ((ChainComplex.single₀ (ModuleCat B)).obj N) n p) :=
    ModuleCat.subsingleton_of_isZero (singleTotal_summand_isZero k A B M N n hn p)
  apply ModuleCat.isZero_iff_subsingleton.mpr
  exact (termPiEquiv k A B _ _ n).injective.subsingleton

def singleTotalTermIso (n : ℕ) : (singleTotal k A B M N).X n ≅
    ((ChainComplex.single₀ (ModuleCat (A ⊗[k] B))).obj (moduleObject k A B M N)).X n := by
  by_cases hn : n=0
  · subst n
    exact (singleTotalZeroEquiv k A B M N).toModuleIso
  · exact (singleTotal_isZero k A B M N n hn).iso (isZero_single_obj_X _ _ _ _ hn)

def singleTotalIso : singleTotal k A B M N ≅
    (ChainComplex.single₀ (ModuleCat (A ⊗[k] B))).obj (moduleObject k A B M N) :=
  HomologicalComplex.Hom.isoOfComponents (singleTotalTermIso k A B M N) (by
    intro i j hij
    have hi : i ≠ 0 := by change j+1=i at hij; omega
    exact (singleTotal_isZero k A B M N i hi).eq_of_src _ _)

end ArExplicit.ExternalTensor

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Tensor_ExternalTensorResolution
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ExternalTensor.hasHomCochainTotal _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ArExplicit.ExternalTensor
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped TensorProduct
universe u
variable (k A B : Type u) [Field k] [Ring A] [Ring B] [Algebra k A] [Algebra k B]
attribute [local instance] moduleCatBaseModule moduleCatBaseTower
variable {M : ModuleCat.{u} A} {N : ModuleCat.{u} B}
variable (P : ProjectiveResolution M) (Q : ProjectiveResolution N)
variable [∀ n, Module.Finite A (P.complex.X n)] [∀ n, Module.Finite B (Q.complex.X n)]

def augmentation : complex k A B P.complex Q.complex ⟶
    (ChainComplex.single₀ (ModuleCat (A ⊗[k] B))).obj (moduleObject k A B M N) :=
  mapBifunctorMap P.π Q.π (bifunctor k A B) (ComplexShape.down ℕ) ≫
    (singleTotalIso k A B M N).hom

def projectiveResolution : ProjectiveResolution (moduleObject k A B M N) where
  complex := complex k A B P.complex Q.complex
  projective n := by
    have : Module.Projective (A ⊗[k] B) ((complex k A B P.complex Q.complex).X n) :=
      term_projective k A B P.complex Q.complex n
    infer_instance
  π := augmentation k A B P Q
  quasiIso := by
    have := map_quasiIso k A B P.π Q.π
    change QuasiIso (mapBifunctorMap P.π Q.π (bifunctor k A B) (ComplexShape.down ℕ) ≫
      (singleTotalIso k A B M N).hom)
    infer_instance

end ArExplicit.ExternalTensor

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Tensor_ExternalTensorCubicExt
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Abelian
open scoped TensorProduct
namespace ArExplicit.ExternalTensor
universe u
variable (k A B : Type u) [Field k] [Ring A] [Ring B] [Algebra k A] [Algebra k B]
variable [CharP k 2] [Module.Finite k A] [Module.Finite k B]
variable [HasDerivedCategory (ModuleCat.{u} (A ⊗[k] B))]
attribute [local instance] moduleCatBaseModule moduleCatBaseTower
variable {X : ModuleCat.{u} A} {Y : ModuleCat.{u} B}
variable (P : ProjectiveResolution X) (Q : ProjectiveResolution Y)
variable [∀ n, Module.Finite A (P.complex.X n)] [∀ n, Module.Finite B (Q.complex.X n)]
variable (p : ∀ n, P.complex.X (n+3) ⟶ P.complex.X n)
variable (r : ∀ n, Q.complex.X (n+3) ⟶ Q.complex.X n)

def firstComparison (n : ℕ) : (projectiveResolution k A B P Q).complex.X (n+3) ⟶
    (projectiveResolution k A B P Q).complex.X n :=
  ModuleCat.ofHom (firstCubic k A B P.complex Q.complex p n)

end ArExplicit.ExternalTensor

end

end OAI
end


