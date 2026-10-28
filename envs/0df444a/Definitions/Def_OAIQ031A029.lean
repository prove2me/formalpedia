-- Prove2me | Definitions.Def_OAIQ031A029
-- name    : OAIQ031A029
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T13:58:09.453712+00:00
-- url     : https://prove2.me/theorems/04f5bee3-8e32-4cd0-8ac2-64a4baaf5c06
-- title:
--   Definitions bundle OAIQ031A029 of the split of OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.ArExplicit.Statement.main`, carved from OpenAI's openai/math development (OpenAI, *An explicit counterexample to the Auslander-Reiten conjecture (result family 199)*, OpenAI Math Release, September 23, 2026, result family 199, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 33 declarations of OpenAI's Lean: 15 definitions, 4 instances and 14 theorems. The definitions and types are `OAI.ArExplicit.ExternalTensor.bifunctor`, `OAI.ArExplicit.ExternalTensor.complex`, `OAI.ArExplicit.ExternalTensor.cubicInsert`, `OAI.ArExplicit.ExternalTensor.desc`, `OAI.ArExplicit.ExternalTensor.firstCubic`, `OAI.ArExplicit.ExternalTensor.firstCubicEntry`, `OAI.ArExplicit.ExternalTensor.horizontal`, `OAI.ArExplicit.ExternalTensor.inclusion`, `OAI.ArExplicit.ExternalTensor.mapHom`, `OAI.ArExplicit.ExternalTensor.rightFunctor`, `OAI.ArExplicit.ExternalTensor.secondCubic`, `OAI.ArExplicit.ExternalTensor.secondCubicEntry`, `OAI.ArExplicit.ExternalTensor.summands`, `OAI.ArExplicit.ExternalTensor.termDirectSumEquiv`, `OAI.ArExplicit.TwoCone.firstD`.
--
--   **Sources.** They come from these modules of lean/OAI/Algebra, in whole or in part: [`AuslanderReiten_Bar_BarComplex`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Bar/BarComplex.lean), [`AuslanderReiten_Cones_ConeExactness`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Cones/ConeExactness.lean), [`AuslanderReiten_Cones_TwoCone`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Cones/TwoCone.lean), [`AuslanderReiten_Tensor_ExternalTensorComplex`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Tensor/ExternalTensorComplex.lean), [`AuslanderReiten_Tensor_ExternalTensorCubic`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Tensor/ExternalTensorCubic.lean), [`AuslanderReiten_Tensor_ExternalTensorCubicDifferential`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Tensor/ExternalTensorCubicDifferential.lean), [`AuslanderReiten_Tensor_ExternalTensorDifferential`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Tensor/ExternalTensorDifferential.lean), [`AuslanderReiten_Tensor_ExternalTensorFunctor`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Tensor/ExternalTensorFunctor.lean).
--
--   **Imports.** It imports the bundles `OAIQ031A001`, `OAIQ031A004` and `OAIQ031A005` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ031A045`, `OAIQ031A046`, `OAIQ031A047`, `OAIQ031A048`, `OAIQ031A055`, `OAIQ031A056` and `OAIQ031A057`.
-- source:
--   OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 199; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/An-explicit-counterexample-to-the-Auslander-Reiten-conjecture-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algebra at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ031A001
import Definitions.Def_OAIQ031A004
import Definitions.Def_OAIQ031A005

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Bar_BarComplex
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

theorem boundary_left (n : ℕ) (a : R) (x : object k R (n + 1)) :
    boundary k R n (left k R (n + 1) a x) = left k R n a (boundary k R n x) := by
  induction x using OAI.tensorInductionOn with
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul b x =>
    cases n with
    | zero => exact mul_assoc _ _ _
    | succ n =>
      rw [left_tmul, boundary_succ_tmul, boundary_succ_tmul, map_add, left_tmul, ← left_mul]

variable [CharP k 2]

theorem boundary_squared (n : ℕ) (x : object k R (n + 2)) :
    boundary k R n (boundary k R (n + 1) x) = 0 := by
  induction n with
  | zero =>
    induction x using OAI.tensorInductionOn with
    | add x y hx hy => simp only [map_add, hx, hy, add_zero]
    | tmul a x =>
      rw [boundary_succ_tmul, map_add, boundary_left, boundary_zero_tmul, left_zero]
      exact double_zero_p1 k _
  | succ n ih =>
    induction x using OAI.tensorInductionOn with
    | add x y hx hy => simp only [map_add, hx, hy, add_zero]
    | tmul a x =>
      rw [boundary_succ_tmul, map_add, boundary_left, boundary_succ_tmul, ih,
        TensorProduct.tmul_zero, add_zero]
      exact double_zero_p1 k _

end ArExplicit.AbsoluteBar

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Cones_ConeExactness
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

theorem coneBlock_exact (eQ : Q₁ →ₗ[R] Q₀) (dQ : Q₀ →ₗ[R] Q₂)
    (eP : P₁ →ₗ[R] P₀) (dP : P₀ →ₗ[R] P₂)
    (f₁ : P₁ →ₗ[R] Q₀) (f₀ : P₀ →ₗ[R] Q₂)
    (hQ : Function.Exact eQ dQ) (hP : Function.Exact eP dP)
    (hf : dQ.comp f₁ = f₀.comp eP) :
    Function.Exact (coneBlock eQ eP f₁) (coneBlock dQ dP f₀) := by
  rintro ⟨x, y⟩
  constructor
  · intro hz
    have hy : dP y = 0 := neg_eq_zero.mp (congrArg Prod.snd hz)
    obtain ⟨v, hv⟩ := (hP y).mp hy
    have hx : dQ (x + f₁ v) = 0 := by
      have hxy : dQ x + f₀ y = 0 := congrArg Prod.fst hz
      rw [map_add, show dQ (f₁ v) = f₀ (eP v) from DFunLike.congr_fun hf v, hv, hxy]
    obtain ⟨u, hu⟩ := (hQ (x + f₁ v)).mp hx
    refine ⟨(u, -v), ?_⟩
    simp [coneBlock_apply, hu, hv]
  · rintro ⟨⟨u, v⟩, huv⟩
    rw [← huv]
    apply Prod.ext
    · change dQ (eQ u + f₁ v) + f₀ (-eP v) = 0
      rw [map_add, (hQ (eQ u)).mpr ⟨u, rfl⟩, zero_add,
        show dQ (f₁ v) = f₀ (eP v) from DFunLike.congr_fun hf v, map_neg, add_neg_cancel]
    · change -dP (-eP v) = 0
      rw [map_neg, neg_neg, (hP (eP v)).mpr ⟨v, rfl⟩]

end ArExplicit

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Cones_TwoCone
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open CategoryTheory

namespace ArExplicit.TwoCone

universe u

variable {R : Type u} [Ring R]

variable (D : Data R)

def firstD (n : ℕ) : firstTerm D (n+1) →ₗ[R] firstTerm D n :=
  coneBlock (D.d n) (D.d (n+2)) (D.first n)

end ArExplicit.TwoCone

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Tensor_ExternalTensorFunctor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ArExplicit.ExternalTensor

open CategoryTheory
open scoped TensorProduct

universe u

variable (k A B : Type u) [Field k] [Ring A] [Ring B] [Algebra k A] [Algebra k B]

attribute [local instance] moduleCatBaseModule moduleCatBaseTower

def mapHom {M M' : ModuleCat.{u} A} {N N' : ModuleCat.{u} B}
    (f : M ⟶ M') (g : N ⟶ N') :
    moduleObject k A B M N ⟶ moduleObject k A B M' N' :=
  ModuleCat.ofHom (X := moduleObject k A B M N) (Y := moduleObject k A B M' N')
    (map k A B f.hom g.hom)

@[simp] theorem mapHom_id (M : ModuleCat.{u} A) (N : ModuleCat.{u} B) :
    mapHom k A B (𝟙 M) (𝟙 N) = 𝟙 (moduleObject k A B M N) := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  let w : M ⊗[k] N := z
  change TensorProduct.map (LinearMap.id : M →ₗ[k] M) (LinearMap.id : N →ₗ[k] N) w = w
  simp

@[simp] theorem mapHom_comp {M M' M'' : ModuleCat.{u} A} {N N' N'' : ModuleCat.{u} B}
    (f : M ⟶ M') (f' : M' ⟶ M'') (g : N ⟶ N') (g' : N' ⟶ N'') :
    mapHom k A B (f ≫ f') (g ≫ g') = mapHom k A B f g ≫ mapHom k A B f' g' := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  let w : M ⊗[k] N := z
  change TensorProduct.map ((f'.hom.comp f.hom).restrictScalars k)
      ((g'.hom.comp g.hom).restrictScalars k) w =
    TensorProduct.map (f'.hom.restrictScalars k) (g'.hom.restrictScalars k)
      (TensorProduct.map (f.hom.restrictScalars k) (g.hom.restrictScalars k) w)
  induction w using OAI.tensorInductionOn with
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul x y => rfl

theorem mapHom_add_left {M M' : ModuleCat.{u} A} {N N' : ModuleCat.{u} B}
    (f f' : M ⟶ M') (g : N ⟶ N') :
    mapHom k A B (f+f') g = mapHom k A B f g + mapHom k A B f' g := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  let w : M ⊗[k] N := z
  change TensorProduct.map ((f.hom+f'.hom).restrictScalars k) (g.hom.restrictScalars k) w =
    TensorProduct.map (f.hom.restrictScalars k) (g.hom.restrictScalars k) w +
      TensorProduct.map (f'.hom.restrictScalars k) (g.hom.restrictScalars k) w
  induction w using OAI.tensorInductionOn with
  | add x y hx hy => simp only [map_add, hx, hy]; abel
  | tmul x y => exact TensorProduct.add_tmul _ _ _

theorem mapHom_add_right {M M' : ModuleCat.{u} A} {N N' : ModuleCat.{u} B}
    (f : M ⟶ M') (g g' : N ⟶ N') :
    mapHom k A B f (g+g') = mapHom k A B f g + mapHom k A B f g' := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  let w : M ⊗[k] N := z
  change TensorProduct.map (f.hom.restrictScalars k) ((g.hom+g'.hom).restrictScalars k) w =
    TensorProduct.map (f.hom.restrictScalars k) (g.hom.restrictScalars k) w +
      TensorProduct.map (f.hom.restrictScalars k) (g'.hom.restrictScalars k) w
  induction w using OAI.tensorInductionOn with
  | add x y hx hy => simp only [map_add, hx, hy]; abel
  | tmul x y => exact TensorProduct.tmul_add _ _ _

def rightFunctor (M : ModuleCat.{u} A) : ModuleCat.{u} B ⥤ ModuleCat.{u} (A ⊗[k] B) where
  obj N := moduleObject k A B M N
  map f := mapHom k A B (𝟙 M) f
  map_id N := mapHom_id k A B M N
  map_comp f g := by simpa only [Category.id_comp] using mapHom_comp k A B (𝟙 M) (𝟙 M) f g

instance instAdditiveModuleCatTensorProductRightFunctor (M : ModuleCat.{u} A) : (rightFunctor k A B M).Additive where
  map_add := by intros; exact mapHom_add_right k A B (𝟙 M) _ _

def bifunctor : ModuleCat.{u} A ⥤ ModuleCat.{u} B ⥤ ModuleCat.{u} (A ⊗[k] B) where
  obj := rightFunctor k A B
  map f :=
    { app := fun N => mapHom k A B f (𝟙 N)
      naturality N N' g := by
        change mapHom k A B (𝟙 _) g ≫ mapHom k A B f (𝟙 _) =
          mapHom k A B f (𝟙 _) ≫ mapHom k A B (𝟙 _) g
        simp only [← mapHom_comp, Category.id_comp, Category.comp_id] }
  map_id M := by
    apply NatTrans.ext
    funext N
    exact mapHom_id k A B M N
  map_comp f g := by
    apply NatTrans.ext
    funext N
    change mapHom k A B (f ≫ g) (𝟙 N) = mapHom k A B f (𝟙 N) ≫ mapHom k A B g (𝟙 N)
    simpa only [Category.id_comp] using mapHom_comp k A B f g (𝟙 N) (𝟙 N)

instance instAdditiveModuleCatFunctorTensorProductBifunctor : (bifunctor k A B).Additive where
  map_add := by
    intro M N f g
    apply NatTrans.ext
    funext L
    exact mapHom_add_left k A B f g (𝟙 L)

instance instAdditiveModuleCatTensorProductObjFunctorBifunctor (M : ModuleCat.{u} A) : ((bifunctor k A B).obj M).Additive :=
  inferInstanceAs ((rightFunctor k A B M).Additive)

end ArExplicit.ExternalTensor

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Tensor_ExternalTensorComplex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ArExplicit.ExternalTensor

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

universe u

variable (k A B : Type u) [Field k] [Ring A] [Ring B] [Algebra k A] [Algebra k B]

attribute [local instance] moduleCatBaseModule moduleCatBaseTower

variable (P : ChainComplex (ModuleCat.{u} A) ℕ) (Q : ChainComplex (ModuleCat.{u} B) ℕ)

instance hasTotal : HomologicalComplex.HasMapBifunctor P Q (bifunctor k A B) (ComplexShape.down ℕ) :=
  fun _ => inferInstance

abbrev complex : ChainComplex (ModuleCat.{u} (A ⊗[k] B)) ℕ :=
  HomologicalComplex.mapBifunctor P Q (bifunctor k A B) (ComplexShape.down ℕ)

abbrev summands (n : ℕ) (p : Diagonal n) : ModuleCat.{u} (A ⊗[k] B) :=
  moduleObject k A B (P.X p.val.1) (Q.X p.val.2)

def termDirectSumEquiv (n : ℕ) :
    (complex k A B P Q).X n ≃ₗ[A ⊗[k] B] (Π₀ p : Diagonal n, summands k A B P Q n p) :=
  CategoryTheory.Iso.toLinearEquiv (ModuleCat.coprodIsoDirectSum (summands k A B P Q n))

end ArExplicit.ExternalTensor

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Tensor_ExternalTensorCubic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ArExplicit.ExternalTensor

open CategoryTheory
open scoped TensorProduct

universe u
variable (k A B : Type u) [Field k] [Ring A] [Ring B] [Algebra k A] [Algebra k B]
attribute [local instance] moduleCatBaseModule moduleCatBaseTower
variable (P : ChainComplex (ModuleCat.{u} A) ℕ) (Q : ChainComplex (ModuleCat.{u} B) ℕ)
local notation "E" => A ⊗[k] B

def cubicInsert (n : ℕ) (ij : Diagonal n) :
    summands k A B P Q n ij →ₗ[E] (complex k A B P Q).X n :=
  (termDirectSumEquiv k A B P Q n).symm.toLinearMap.comp (DFinsupp.lsingle (R := E)
    (M := fun t : Diagonal n => ↥(summands k A B P Q n t)) ij)

variable (p : (n : ℕ) → P.X (n+3) ⟶ P.X n)
variable (r : (n : ℕ) → Q.X (n+3) ⟶ Q.X n)

def firstCubicEntry (n : ℕ) : (ij : Diagonal (n+3)) →
    summands k A B P Q (n+3) ij →ₗ[E] (complex k A B P Q).X n
  | ⟨(0, _), _⟩ => 0
  | ⟨(1, _), _⟩ => 0
  | ⟨(2, _), _⟩ => 0
  | ⟨(i+3, j), h⟩ => (cubicInsert k A B P Q n ⟨(i,j), by omega⟩).comp
      (map k A B (p i).hom (LinearMap.id : Q.X j →ₗ[B] Q.X j))

def secondCubicEntry (n : ℕ) : (ij : Diagonal (n+3)) →
    summands k A B P Q (n+3) ij →ₗ[E] (complex k A B P Q).X n
  | ⟨(_, 0), _⟩ => 0
  | ⟨(_, 1), _⟩ => 0
  | ⟨(_, 2), _⟩ => 0
  | ⟨(i, j+3), h⟩ => (cubicInsert k A B P Q n ⟨(i,j), by omega⟩).comp
      (map k A B (LinearMap.id : P.X i →ₗ[A] P.X i) (r j).hom)

def firstCubic (n : ℕ) : (complex k A B P Q).X (n+3) →ₗ[E] (complex k A B P Q).X n :=
  (DFinsupp.coprodMap (firstCubicEntry k A B P Q p n)).comp
    (termDirectSumEquiv k A B P Q (n+3)).toLinearMap

def secondCubic (n : ℕ) : (complex k A B P Q).X (n+3) →ₗ[E] (complex k A B P Q).X n :=
  (DFinsupp.coprodMap (secondCubicEntry k A B P Q r n)).comp
    (termDirectSumEquiv k A B P Q (n+3)).toLinearMap

@[simp] theorem firstCubic_insert (n : ℕ) (ij : Diagonal (n+3))
    (x : summands k A B P Q (n+3) ij) :
    firstCubic k A B P Q p n (cubicInsert k A B P Q (n+3) ij x) =
      firstCubicEntry k A B P Q p n ij x := by
  simp [firstCubic, cubicInsert, DFinsupp.coprodMap_apply_single]

@[simp] theorem secondCubic_insert (n : ℕ) (ij : Diagonal (n+3))
    (x : summands k A B P Q (n+3) ij) :
    secondCubic k A B P Q r n (cubicInsert k A B P Q (n+3) ij x) =
      secondCubicEntry k A B P Q r n ij x := by
  simp [secondCubic, cubicInsert, DFinsupp.coprodMap_apply_single]

end ArExplicit.ExternalTensor

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Tensor_ExternalTensorDifferential
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

variable (P : ChainComplex (ModuleCat.{u} A) ℕ) (Q : ChainComplex (ModuleCat.{u} B) ℕ)

abbrev inclusion (i j n : ℕ) (h : i+j=n) :
    moduleObject k A B (P.X i) (Q.X j) ⟶ (complex k A B P Q).X n :=
  ιMapBifunctor P Q (bifunctor k A B) (ComplexShape.down ℕ) i j n h

abbrev desc {N : ModuleCat.{u} (A ⊗[k] B)} {n : ℕ}
    (f : ∀ (i j : ℕ) (_ : i+j=n), moduleObject k A B (P.X i) (Q.X j) ⟶ N) :
    (complex k A B P Q).X n ⟶ N :=
  mapBifunctorDesc (K₁ := P) (K₂ := Q) (F := bifunctor k A B) (c := ComplexShape.down ℕ) f

@[simp] theorem inclusion_desc {N : ModuleCat.{u} (A ⊗[k] B)} {n : ℕ}
    (f : ∀ (i j : ℕ) (_ : i+j=n), moduleObject k A B (P.X i) (Q.X j) ⟶ N)
    (i j : ℕ) (h : i+j=n) :
    inclusion k A B P Q i j n h ≫ desc k A B P Q f = f i j h :=
  ι_mapBifunctorDesc (K₁ := P) (K₂ := Q) (F := bifunctor k A B)
    (c := ComplexShape.down ℕ) f i j h

abbrev horizontal (i j n : ℕ) : moduleObject k A B (P.X i) (Q.X j) ⟶ (complex k A B P Q).X n :=
  mapBifunctor.d₁ P Q (bifunctor k A B) (ComplexShape.down ℕ) i j n

theorem horizontal_succ (i j n : ℕ) (h : i+j=n) :
    horizontal k A B P Q (i+1) j n =
      mapHom k A B (P.d (i+1) i) (𝟙 (Q.X j)) ≫ inclusion k A B P Q i j n h := by
  dsimp only [horizontal]
  rw [mapBifunctor.d₁_eq P Q (bifunctor k A B) (ComplexShape.down ℕ) (by rfl) j n h]
  change (1 : ℤˣ) • _ = _
  exact one_smul _ _

theorem termDirectSumEquiv_inclusion (i j n : ℕ) (h : i+j=n) :
    (termDirectSumEquiv k A B P Q n).toLinearMap.comp
      (inclusion k A B P Q i j n h).hom =
      DFinsupp.lsingle (R := A ⊗[k] B) (M := fun p : Diagonal n => summands k A B P Q n p)
        ⟨(i,j),h⟩ := by
  exact congrArg (fun f => f.hom)
    (ModuleCat.ι_coprodIsoDirectSum_hom (summands k A B P Q n) ⟨(i,j),h⟩)

theorem inclusion_eq_directSum (i j n : ℕ) (h : i+j=n) :
    (inclusion k A B P Q i j n h).hom =
      (termDirectSumEquiv k A B P Q n).symm.toLinearMap.comp
        (DFinsupp.lsingle (R := A ⊗[k] B) (M := fun p : Diagonal n => summands k A B P Q n p)
          ⟨(i,j),h⟩) := by
  ext x
  apply (termDirectSumEquiv k A B P Q n).injective
  simpa only [LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.apply_symm_apply] using
    LinearMap.congr_fun (termDirectSumEquiv_inclusion k A B P Q i j n h) x

end ArExplicit.ExternalTensor

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Tensor_ExternalTensorCubicDifferential
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ArExplicit.ExternalTensor

open CategoryTheory
open scoped TensorProduct
universe u
variable (k A B : Type u) [Field k] [Ring A] [Ring B] [Algebra k A] [Algebra k B]
attribute [local instance] moduleCatBaseModule moduleCatBaseTower
variable (P : ChainComplex (ModuleCat.{u} A) ℕ) (Q : ChainComplex (ModuleCat.{u} B) ℕ)

@[simp] theorem inclusion_eq_cubicInsert (i j n : ℕ) (h : i+j=n) :
    (inclusion k A B P Q i j n h).hom = cubicInsert k A B P Q n ⟨(i,j),h⟩ :=
  inclusion_eq_directSum k A B P Q i j n h

end ArExplicit.ExternalTensor

end

end OAI
end


