-- Prove2me | Definitions.Def_OAIQ031A046
-- name    : OAIQ031A046
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T14:03:22.223729+00:00
-- url     : https://prove2.me/theorems/51f4629c-5d73-4e2e-ac69-9afa5911c5bf
-- title:
--   Definitions bundle OAIQ031A046 of the split of OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.ArExplicit.Statement.main`, carved from OpenAI's openai/math development (OpenAI, *An explicit counterexample to the Auslander-Reiten conjecture (result family 199)*, OpenAI Math Release, September 23, 2026, result family 199, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 22 declarations of OpenAI's Lean: 4 definitions and 18 theorems. The definitions and types are `OAI.ArExplicit.ExternalTensor.bottomMap`, `OAI.ArExplicit.ExternalTensor.bottomProjection`, `OAI.ArExplicit.ExternalTensor.vertical`, `OAI.ArExplicit.TwoCone.d`.
--
--   **Sources.** They come from these modules of lean/OAI/Algebra, in whole or in part: [`AuslanderReiten_Algebras_TMultiplication`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Algebras/TMultiplication.lean), [`AuslanderReiten_Cones_TwoCone`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Cones/TwoCone.lean), [`AuslanderReiten_Tensor_ExternalTensorBottom`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Tensor/ExternalTensorBottom.lean), [`AuslanderReiten_Tensor_ExternalTensorCubicChain`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Tensor/ExternalTensorCubicChain.lean), [`AuslanderReiten_Tensor_ExternalTensorCubicComm`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Tensor/ExternalTensorCubicComm.lean), [`AuslanderReiten_Tensor_ExternalTensorCubicDifferential`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Tensor/ExternalTensorCubicDifferential.lean), [`AuslanderReiten_Tensor_ExternalTensorDifferential`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Tensor/ExternalTensorDifferential.lean).
--
--   **Imports.** It imports the bundles `OAIQ031A025` and `OAIQ031A029` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ031A062`, `OAIQ031A063`, `OAIQ031A065`, `OAIQ031A072`, `OAIQ031A073` and `OAIQ031A074`; the proof of `OAI_ArExplicit_MainConclusions_scalarExtension`.
-- source:
--   OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 199; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/An-explicit-counterexample-to-the-Auslander-Reiten-conjecture-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algebra at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ031A025
import Definitions.Def_OAIQ031A029

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Algebras_TMultiplication
attribute [-instance] _root_.OAI.ArExplicit.Resolution.instIsScalarTowerTSimple _root_.OAI.ArExplicit.Resolution.instModuleTSimple _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ArExplicit

namespace CocycleData

open BaseAlgebra TrivialExtension

variable {k : Type*} [Field k] (q : k)

theorem dual_apply (φ : Module.Dual k (BaseAlgebra k q)) (a : BaseAlgebra k q) :
    φ a = ∑ i, a.coeff i * φ (basisVector q i) := by
  conv_lhs => rw [T.base_expand q a]
  simp

end CocycleData
end ArExplicit

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Cones_TwoCone
attribute [-instance] _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
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

def d (n : ℕ) : term D (n+1) →ₗ[R] term D n :=
  coneBlock (firstD D n) (firstD D (n+2)) (secondOnFirst D n)

end ArExplicit.TwoCone

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Tensor_ExternalTensorCubicComm
attribute [-instance] _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
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

theorem cubic_hom_ext {V : Type u} [AddCommGroup V] [Module E V] (n : ℕ)
    (f g : (complex k A B P Q).X n →ₗ[E] V)
    (h : ∀ (ij : Diagonal n) (x : summands k A B P Q n ij),
      f (cubicInsert k A B P Q n ij x) = g (cubicInsert k A B P Q n ij x)) : f = g := by
  have hh : f.comp (termDirectSumEquiv k A B P Q n).symm.toLinearMap =
      g.comp (termDirectSumEquiv k A B P Q n).symm.toLinearMap := by
    apply DFinsupp.lhom_ext
    intro ij x
    exact h ij x
  apply LinearMap.ext
  intro x
  have hx := DFunLike.congr_fun hh (termDirectSumEquiv k A B P Q n x)
  simpa only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply] using hx

theorem map_interchange {M M' : ModuleCat.{u} A} {N N' : ModuleCat.{u} B}
    (f : M ⟶ M') (g : N ⟶ N') (x : moduleObject k A B M N) :
    map k A B f.hom (LinearMap.id : N' →ₗ[B] N')
      (map k A B (LinearMap.id : M →ₗ[A] M) g.hom x) =
    map k A B (LinearMap.id : M' →ₗ[A] M') g.hom
      (map k A B f.hom (LinearMap.id : N →ₗ[B] N) x) := by
  have h : mapHom k A B (𝟙 M) g ≫ mapHom k A B f (𝟙 N') =
      mapHom k A B f (𝟙 N) ≫ mapHom k A B (𝟙 M') g := by
    rw [← mapHom_comp, ← mapHom_comp]
    simp only [Category.id_comp, Category.comp_id]
  exact congrArg (fun t => t.hom x) h

variable (p : (n : ℕ) → P.X (n+3) ⟶ P.X n)
variable (r : (n : ℕ) → Q.X (n+3) ⟶ Q.X n)

theorem cubic_commute (n : ℕ) :
    (firstCubic k A B P Q p n).comp (secondCubic k A B P Q r (n+3)) =
      (secondCubic k A B P Q r n).comp (firstCubic k A B P Q p (n+3)) := by
  apply cubic_hom_ext k A B P Q (n+3+3)
  rintro ⟨⟨i,j⟩,h⟩ x
  simp only [LinearMap.comp_apply, firstCubic_insert, secondCubic_insert]
  rcases i with _ | (_ | (_ | i)) <;> rcases j with _ | (_ | (_ | j))
  all_goals simp only [firstCubicEntry, secondCubicEntry, LinearMap.zero_apply,
    LinearMap.comp_apply, firstCubic_insert, secondCubic_insert, map_zero]
  exact congrArg (cubicInsert k A B P Q n ⟨(i,j), by omega⟩)
    (map_interchange k A B (p i) (r j) x)

end ArExplicit.ExternalTensor

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Tensor_ExternalTensorDifferential
attribute [-instance] _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
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

abbrev vertical (i j n : ℕ) : moduleObject k A B (P.X i) (Q.X j) ⟶ (complex k A B P Q).X n :=
  mapBifunctor.d₂ P Q (bifunctor k A B) (ComplexShape.down ℕ) i j n

theorem inclusion_d (i j n n' : ℕ) (h : i+j=n) :
    inclusion k A B P Q i j n h ≫ (complex k A B P Q).d n n' =
      horizontal k A B P Q i j n' + vertical k A B P Q i j n' := by
  change ιMapBifunctor P Q (bifunctor k A B) (ComplexShape.down ℕ) i j n h ≫
    (mapBifunctor P Q (bifunctor k A B) (ComplexShape.down ℕ)).d n n' =
    mapBifunctor.d₁ P Q (bifunctor k A B) (ComplexShape.down ℕ) i j n' +
    mapBifunctor.d₂ P Q (bifunctor k A B) (ComplexShape.down ℕ) i j n'
  rw [mapBifunctor.d_eq, Preadditive.comp_add, mapBifunctor.ι_D₁, mapBifunctor.ι_D₂]

theorem vertical_succ (i j n : ℕ) (h : i+j=n) :
    vertical k A B P Q i (j+1) n =
      (-1 : ℤˣ)^i • (mapHom k A B (𝟙 (P.X i)) (Q.d (j+1) j) ≫
        inclusion k A B P Q i j n h) := by
  dsimp only [vertical]
  rw [mapBifunctor.d₂_eq P Q (bifunctor k A B) (ComplexShape.down ℕ) i (by rfl) n h]
  rfl

theorem horizontal_zero (j n : ℕ) : horizontal k A B P Q 0 j n = 0 :=
  mapBifunctor.d₁_eq_zero P Q (bifunctor k A B) (ComplexShape.down ℕ) 0 j n (by
    change ¬ (ComplexShape.down ℕ).next 0 + 1 = 0
    omega)

theorem vertical_zero (i n : ℕ) : vertical k A B P Q i 0 n = 0 :=
  mapBifunctor.d₂_eq_zero P Q (bifunctor k A B) (ComplexShape.down ℕ) i 0 n (by
    change ¬ (ComplexShape.down ℕ).next 0 + 1 = 0
    omega)

end ArExplicit.ExternalTensor

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Tensor_ExternalTensorCubicDifferential
attribute [-instance] _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
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

theorem cubicInsert_d (i j n m : ℕ) (h : i+j=n)
    (x : moduleObject k A B (P.X i) (Q.X j)) :
    (complex k A B P Q).d n m (cubicInsert k A B P Q n ⟨(i,j),h⟩ x) =
      horizontal k A B P Q i j m x + vertical k A B P Q i j m x := by
  have hh := congrArg (fun f => f.hom x) (inclusion_d k A B P Q i j n m h)
  simpa only [ModuleCat.hom_comp, LinearMap.comp_apply, inclusion_eq_cubicInsert,
    ModuleCat.hom_add, LinearMap.add_apply] using hh

@[simp] theorem horizontal_succ_apply (i j n : ℕ) (h : i+j=n)
    (x : moduleObject k A B (P.X (i+1)) (Q.X j)) :
    horizontal k A B P Q (i+1) j n x =
      cubicInsert k A B P Q n ⟨(i,j),h⟩
        (map k A B (P.d (i+1) i).hom (LinearMap.id : Q.X j →ₗ[B] Q.X j) x) := by
  rw [horizontal_succ k A B P Q i j n h]
  change (inclusion k A B P Q i j n h).hom _ = _
  rw [inclusion_eq_cubicInsert]
  rfl

variable [CharP k 2]

theorem module_neg_eq (M : ModuleCat.{u} E) (x : M) : -x=x := by
  apply neg_eq_iff_add_eq_zero.mpr
  have ht : (2 : k)=0 := CharP.cast_eq_zero k 2
  rw [← two_smul k, ht, zero_smul]

theorem signed_hom_eq {M N : ModuleCat.{u} E} (f : M ⟶ N) (v : ℤˣ) : v • f = f := by
  rcases Int.units_eq_one_or v with rfl | rfl
  · exact one_smul _ _
  · change (-1 : ℤ) • f = f
    rw [neg_one_smul]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact module_neg_eq k A B N (f x)

@[simp] theorem vertical_succ_apply (i j n : ℕ) (h : i+j=n)
    (x : moduleObject k A B (P.X i) (Q.X (j+1))) :
    vertical k A B P Q i (j+1) n x =
      cubicInsert k A B P Q n ⟨(i,j),h⟩
        (map k A B (LinearMap.id : P.X i →ₗ[A] P.X i) (Q.d (j+1) j).hom x) := by
  rw [vertical_succ k A B P Q i j n h, signed_hom_eq k A B]
  change (inclusion k A B P Q i j n h).hom _ = _
  rw [inclusion_eq_cubicInsert]
  rfl

end ArExplicit.ExternalTensor

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Tensor_ExternalTensorBottom
attribute [-instance] _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
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

def bottomProjection (n : ℕ) : (complex k A B P Q).X n →ₗ[E]
    moduleObject k A B (P.X n) (Q.X 0) :=
  (DFinsupp.lapply ⟨(n,0), Nat.add_zero n⟩).comp
    (termDirectSumEquiv k A B P Q n).toLinearMap

@[simp] theorem bottomProjection_bottom (n : ℕ)
    (x : moduleObject k A B (P.X n) (Q.X 0)) :
    bottomProjection k A B P Q n (cubicInsert k A B P Q n ⟨(n,0), Nat.add_zero n⟩ x) = x := by
  simp [bottomProjection, cubicInsert]

@[simp] theorem bottomProjection_positive (n i j : ℕ) (h : i+(j+1)=n)
    (x : moduleObject k A B (P.X i) (Q.X (j+1))) :
    bottomProjection k A B P Q n (cubicInsert k A B P Q n ⟨(i,j+1),h⟩ x) = 0 := by
  have hh : (⟨(n,0), Nat.add_zero n⟩ : Diagonal n) ≠ ⟨(i,j+1),h⟩ := by
    intro he
    have := congrArg (fun t : Diagonal n => t.val.2) he
    simp only at this
    omega
  simp [bottomProjection, cubicInsert, DFinsupp.single_apply, Ne.symm hh]

variable (U : ChainComplex (ModuleCat.{u} A) ℕ) (V : ChainComplex (ModuleCat.{u} B) ℕ)

def bottomMap (s t : ℕ) (f : U.X s ⟶ P.X t) (g : V.X 0 ⟶ Q.X 0) :
    (complex k A B U V).X s →ₗ[E] (complex k A B P Q).X t :=
  (cubicInsert k A B P Q t ⟨(t,0),Nat.add_zero t⟩).comp
    ((map k A B f.hom g.hom).comp (bottomProjection k A B U V s))

@[simp] theorem bottomMap_bottom (s t : ℕ) (f : U.X s ⟶ P.X t) (g : V.X 0 ⟶ Q.X 0)
    (x : moduleObject k A B (U.X s) (V.X 0)) :
    bottomMap k A B P Q U V s t f g
      (cubicInsert k A B U V s ⟨(s,0),Nat.add_zero s⟩ x) =
      cubicInsert k A B P Q t ⟨(t,0),Nat.add_zero t⟩ (map k A B f.hom g.hom x) := by
  simp only [bottomMap, LinearMap.comp_apply, bottomProjection_bottom]

@[simp] theorem bottomMap_positive (s t i j : ℕ) (h : i+(j+1)=s)
    (f : U.X s ⟶ P.X t) (g : V.X 0 ⟶ Q.X 0)
    (x : moduleObject k A B (U.X i) (V.X (j+1))) :
    bottomMap k A B P Q U V s t f g
      (cubicInsert k A B U V s ⟨(i,j+1),h⟩ x) = 0 := by
  simp only [bottomMap, LinearMap.comp_apply, bottomProjection_positive, map_zero]

end ArExplicit.ExternalTensor

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Tensor_ExternalTensorCubicChain
attribute [-instance] _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
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

variable (p : (n : ℕ) → P.X (n+3) ⟶ P.X n)
variable (r : (n : ℕ) → Q.X (n+3) ⟶ Q.X n)
variable (hp : ∀ n, p (n+1) ≫ P.d (n+1) n = P.d (n+4) (n+3) ≫ p n)
variable (hr : ∀ n, r (n+1) ≫ Q.d (n+1) n = Q.d (n+4) (n+3) ≫ r n)

include hp in
theorem first_map_chain (i j : ℕ)
    (x : moduleObject k A B (P.X (i+4)) (Q.X j)) :
    map k A B (P.d (i+1) i).hom (LinearMap.id : Q.X j →ₗ[B] Q.X j)
      (map k A B (p (i+1)).hom (LinearMap.id : Q.X j →ₗ[B] Q.X j) x) =
    map k A B (p i).hom (LinearMap.id : Q.X j →ₗ[B] Q.X j)
      (map k A B (P.d (i+4) (i+3)).hom (LinearMap.id : Q.X j →ₗ[B] Q.X j) x) := by
  have hh := congrArg (fun f => mapHom k A B f (𝟙 (Q.X j))) (hp i)
  rw [show 𝟙 (Q.X j) = 𝟙 (Q.X j) ≫ 𝟙 (Q.X j) from (Category.id_comp _).symm,
    mapHom_comp, mapHom_comp] at hh
  exact congrArg (fun f => f.hom x) hh

end ArExplicit.ExternalTensor

end

end OAI
end


