-- Prove2me | Definitions.Def_OAIQ031A063
-- name    : OAIQ031A063
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T14:11:23.85655+00:00
-- url     : https://prove2.me/theorems/db3df316-869b-437c-8976-016874a2c9e9
-- title:
--   Definitions bundle OAIQ031A063 of the split of OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.ArExplicit.Statement.main`, carved from OpenAI's openai/math development (OpenAI, *An explicit counterexample to the Auslander-Reiten conjecture (result family 199)*, OpenAI Math Release, September 23, 2026, result family 199, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 20 declarations of OpenAI's Lean: 4 definitions, 2 instances and 14 theorems. The definitions and types are `OAI.ArExplicit.AbsoluteBar.baseEquiv`, `OAI.ArExplicit.AbsoluteBar.rotateEquiv`, `OAI.ArExplicit.ModuleBar.cochain3Linear`, `OAI.ArExplicit.ModuleBar.suffix3`.
--
--   **Sources.** They come from these modules of lean/OAI/Algebra, in whole or in part: [`AuslanderReiten_Algebras_SymmetricSocle`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Algebras/SymmetricSocle.lean), [`AuslanderReiten_Bar_BarBimodule`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Bar/BarBimodule.lean), [`AuslanderReiten_Bar_BarCochain`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Bar/BarCochain.lean), [`AuslanderReiten_Bar_BarProjective`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Bar/BarProjective.lean), [`AuslanderReiten_Bar_ModuleBarCochain`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Bar/ModuleBarCochain.lean), [`AuslanderReiten_Evaluation_TensorBeta`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Evaluation/TensorBeta.lean), [`AuslanderReiten_Tensor_ExternalTensorBottomCubic`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Tensor/ExternalTensorBottomCubic.lean), [`AuslanderReiten_Tensor_ExternalTensorBottomDifferential`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Tensor/ExternalTensorBottomDifferential.lean).
--
--   **Imports.** It imports the bundles `OAIQ031A044`, `OAIQ031A045`, `OAIQ031A046` and `OAIQ031A047` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ031A078`, `OAIQ031A079`, `OAIQ031A080`, `OAIQ031A081`, `OAIQ031A082`, `OAIQ031A083`, `OAIQ031A084` and `OAIQ031A088`.
-- source:
--   OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 199; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/An-explicit-counterexample-to-the-Auslander-Reiten-conjecture-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algebra at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ031A044
import Definitions.Def_OAIQ031A045
import Definitions.Def_OAIQ031A046
import Definitions.Def_OAIQ031A047

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Algebras_SymmetricSocle
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ArExplicit.FrobeniusTrace

universe u
variable {k R : Type u} [Field k] [Ring R] [Algebra k R]
variable (τ : FrobeniusTrace k R)
variable (hs : ∀ a b : R, τ.trace (a * b) = τ.trace (b * a))
variable (J : Ideal R) [J.IsTwoSided]

include τ hs

variable {M N : Type u} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
variable (hM : ∀ j ∈ J, ∀ x : M, j • x = 0)
variable (ι : N →ₗ[R] R) (hι : Function.Injective ι) (hN : ∀ x : N, ι x ∈ J)

include hM hι hN

theorem stable_class_ne_zero {f : M →ₗ[R] N} (hf : f ≠ 0) :
    StableHom.classOf R M N f ≠ 0 := by
  intro hz
  exact hf (τ.projective_factor_zero hs J hM ι hι hN f
    ((StableHom.classOf_eq_zero_iff_projective f).mp hz))

end ArExplicit.FrobeniusTrace

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Bar_BarBimodule
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
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

instance baseModule (n : ℕ) : Module k (moduleObject k R n) :=
  (object k R n).isModule

instance bimoduleTower (n : ℕ) : IsScalarTower k (Enveloping k R) (moduleObject k R n) :=
  IsScalarTower.of_algebraMap_smul (A := Enveloping k R) fun a x => by
    change (representation k R n (algebraMap k (Enveloping k R) a)) x = a • x
    rw [AlgHom.commutes]
    rfl

variable [CharP k 2]

theorem differential_exact (n : ℕ) :
    LinearMap.range (differential k R (n + 1)) = LinearMap.ker (differential k R n) := by
  ext x
  change (∃ y, boundary k R (n + 1) y = x) ↔ boundary k R n x = 0
  exact SetLike.ext_iff.mp (boundary_exact k R n) x

end ArExplicit.AbsoluteBar

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Bar_BarProjective
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
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

def baseEquiv : moduleObject k R 1 ≃ₗ[Enveloping k R] Enveloping k R where
  __ := (TensorProduct.congr (LinearEquiv.refl k R) (MulOpposite.opLinearEquiv k)).toAddEquiv
  map_smul' a x := by
    let y : R ⊗[k] R := x
    change (TensorProduct.congr (LinearEquiv.refl k R) (MulOpposite.opLinearEquiv k))
      ((representation k R 1 a) y) =
      a * (TensorProduct.congr (LinearEquiv.refl k R) (MulOpposite.opLinearEquiv k)) y
    induction a using OAI.tensorInductionOn with
    | add a b ha hb => simp only [map_add, LinearMap.add_apply, ha, hb, add_mul]
    | tmul a b =>
      induction y using OAI.tensorInductionOn with
      | add x y hx hy => simp only [map_add, hx, hy, mul_add]
      | tmul x y =>
        change (a * x) ⊗ₜ[k] MulOpposite.op (y * MulOpposite.unop b) =
          (a ⊗ₜ[k] b) * (x ⊗ₜ[k] MulOpposite.op y)
        rw [Algebra.TensorProduct.tmul_mul_tmul]
        rfl

def rotateEquiv (n : ℕ) : moduleObject k R (n + 2) ≃ₗ[Enveloping k R]
    (moduleObject k R (n + 1) ⊗[k] R) where
  __ := (rotateLinear k R n).toAddEquiv
  map_smul' a x := by
    let y : object k R (n + 2) := x
    change rotateLinear k R n ((representation k R (n + 2) a) y) =
      ((representation k R (n + 1) a).rTensor R) (rotateLinear k R n y)
    induction a using OAI.tensorInductionOn with
    | add a b ha hb => simp only [map_add, LinearMap.rTensor_add, LinearMap.add_apply, ha, hb]
    | tmul a b =>
      induction y using OAI.tensorInductionOn with
      | add x y hx hy => simp only [map_add, hx, hy]
      | tmul x y =>
        induction y using OAI.tensorInductionOn with
        | add y z hy hz => simp only [TensorProduct.tmul_add, map_add, hy, hz]
        | tmul y z =>
          change ((a * x) ⊗ₜ[k] right k R n b z) ⊗ₜ[k] y =
            ((representation k R (n + 1) (a ⊗ₜ[k] b)) (x ⊗ₜ[k] z)) ⊗ₜ[k] y
          rfl

theorem free (n : ℕ) : Module.Free (Enveloping k R) (moduleObject k R (n + 1)) := by
  induction n with
  | zero => exact Module.Free.of_equiv (baseEquiv k R).symm
  | succ n ih =>
    let := ih
    exact Module.Free.of_equiv (rotateEquiv k R n).symm

end ArExplicit.AbsoluteBar

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Bar_BarCochain
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
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

theorem cochain3Linear_left (p : Cochain3 k R) (a : R) (x : object k R 4) :
    cochain3Linear k R p (left k R 4 a x) = a * cochain3Linear k R p x := by
  induction x using OAI.tensorInductionOn with
  | add x y hx hy => simp only [map_add, hx, hy, mul_add]
  | tmul b x => exact mul_assoc _ _ _

end ArExplicit.AbsoluteBar

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Bar_ModuleBarCochain
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
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

def suffix3 (p : AbsoluteBar.Cochain3 k R) : object k R M 3 →ₗ[k] M :=
  TensorProduct.lift {
    toFun := fun a => TensorProduct.lift {
      toFun := fun b => TensorProduct.lift (((Algebra.lsmul k k M).toLinearMap).comp (p a b))
      map_add' := by
        intro b c
        apply TensorProduct.ext'
        intro d e
        simp
      map_smul' := by
        intro t b
        apply TensorProduct.ext'
        intro d e
        simp }
    map_add' := by
      intro a b
      apply TensorProduct.ext'
      intro c y
      induction y using OAI.tensorInductionOn with
      | add y z hy hz =>
        simp only [TensorProduct.tmul_add, map_add, LinearMap.add_apply] at *
        rw [hy, hz]
      | tmul d e => simp
    map_smul' := by
      intro t a
      apply TensorProduct.ext'
      intro b y
      induction y using OAI.tensorInductionOn with
      | add y z hy hz =>
        simp only [TensorProduct.tmul_add, map_add, LinearMap.smul_apply] at *
        rw [hy, hz]
      | tmul c d => simp }

@[simp] theorem suffix3_tmul (p : AbsoluteBar.Cochain3 k R) (a b c : R) (d : M) :
    suffix3 k R M p (a ⊗ₜ[k] (b ⊗ₜ[k] (c ⊗ₜ[k] d))) = p a b c • d := rfl

def cochain3Linear (p : AbsoluteBar.Cochain3 k R) : object k R M 4 →ₗ[k] M :=
  TensorProduct.lift (((Algebra.lsmul k k M).toLinearMap).compl₂ (suffix3 k R M p))

@[simp] theorem cochain3Linear_tmul (p : AbsoluteBar.Cochain3 k R) (a b c d : R) (e : M) :
    cochain3Linear k R M p (a ⊗ₜ[k] (b ⊗ₜ[k] (c ⊗ₜ[k] (d ⊗ₜ[k] e)))) =
      (a * p b c d) • e := by
  change a • (p b c d • e) = _
  exact (mul_smul _ _ _).symm

end ArExplicit.ModuleBar

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Evaluation_TensorBeta
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct

namespace ArExplicit.A

variable {k : Type*} [Field k] (q : k)

theorem beta_ne_zero : beta q ≠ 0 := by
  intro h
  have hh := congrArg (fun z : augmentationIdeal q => betaDetector q z.val)
    (DFunLike.congr_fun h (simpleGenerator q))
  change betaDetector q (socleMap q (simpleGenerator q)) = 0 at hh
  rw [socleMap_generator, betaDetector_socle] at hh
  exact one_ne_zero hh

end ArExplicit.A

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Tensor_ExternalTensorBottomDifferential
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ExternalTensor.diagonalZeroUnique _root_.OAI.ArExplicit.ExternalTensor.hasHomCochainTotal _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
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
variable (P U : ChainComplex (ModuleCat.{u} A) ℕ) (Q V : ChainComplex (ModuleCat.{u} B) ℕ)

theorem map_comp_apply {M₀ M₁ M₂ : ModuleCat.{u} A} {N₀ N₁ N₂ : ModuleCat.{u} B}
    (f : M₀ ⟶ M₁) (f' : M₁ ⟶ M₂) (g : N₀ ⟶ N₁) (g' : N₁ ⟶ N₂)
    (x : moduleObject k A B M₀ N₀) :
    map k A B f'.hom g'.hom (map k A B f.hom g.hom x) =
      map k A B (f ≫ f').hom (g ≫ g').hom x :=
  (congrArg (fun h => h.hom x) (mapHom_comp k A B f f' g g')).symm

@[simp] theorem map_zero_right_apply {M M' : ModuleCat.{u} A} {N N' : ModuleCat.{u} B}
    (f : M ⟶ M') (x : moduleObject k A B M N) :
    map k A B f.hom (0 : N →ₗ[B] N') x = 0 := by
  let y : M ⊗[k] N := x
  change TensorProduct.map (f.hom.restrictScalars k) (0 : N →ₗ[k] N') y = 0
  rw [TensorProduct.map_zero_right, LinearMap.zero_apply]

theorem bottomMap_d_target (s t : ℕ) (f : U.X s ⟶ P.X (t+1)) (g : V.X 0 ⟶ Q.X 0) :
    ((complex k A B P Q).d (t+1) t).hom.comp (bottomMap k A B P Q U V s (t+1) f g) =
      bottomMap k A B P Q U V s t (f ≫ P.d (t+1) t) g := by
  apply cubic_hom_ext k A B U V s
  rintro ⟨⟨i,j⟩,h⟩ x
  cases j with
  | zero =>
    have hi : i=s := by simpa using h
    subst i
    simp only [LinearMap.comp_apply, bottomMap_bottom, cubicInsert_d,
      horizontal_succ_apply k A B P Q t 0 t (Nat.add_zero t), vertical_zero,
      hom_zero_apply_p0, add_zero]
    congr 1
    have hh := map_comp_apply k A B f (P.d (t+1) t) g (𝟙 (Q.X 0)) x
    simp only [Category.comp_id] at hh
    convert! hh using 1
    all_goals try with_reducible_and_instances rfl
  | succ j => simp only [LinearMap.comp_apply, bottomMap_positive, map_zero]

variable [CharP k 2]

theorem bottomMap_d_source (s t : ℕ) (f : U.X s ⟶ P.X t) (g : V.X 0 ⟶ Q.X 0)
    (hg : V.d 1 0 ≫ g = 0) :
    (bottomMap k A B P Q U V s t f g).comp ((complex k A B U V).d (s+1) s).hom =
      bottomMap k A B P Q U V (s+1) t (U.d (s+1) s ≫ f) g := by
  apply cubic_hom_ext k A B U V (s+1)
  rintro ⟨⟨i,j⟩,h⟩ x
  cases j with
  | zero =>
    have hi : i=s+1 := by simpa using h
    subst i
    simp only [LinearMap.comp_apply, cubicInsert_d,
      horizontal_succ_apply k A B U V s 0 s (Nat.add_zero s), vertical_zero,
      hom_zero_apply_p0, add_zero, bottomMap_bottom]
    congr 1
    have hh := map_comp_apply k A B (U.d (s+1) s) f (𝟙 (V.X 0)) g x
    simp only [Category.id_comp] at hh
    convert! hh using 1
    all_goals try with_reducible_and_instances rfl
  | succ j =>
    cases j with
    | zero =>
      have hi : i=s := by omega
      subst i
      cases s with
      | zero =>
        simp only [LinearMap.comp_apply, cubicInsert_d, horizontal_zero, hom_zero_apply_p0,
          vertical_succ_apply k A B U V 0 0 0 rfl, zero_add, bottomMap_bottom,
          bottomMap_positive]
        have hh := map_comp_apply k A B (𝟙 (U.X 0)) f (V.d 1 0) g x
        simp only [Category.id_comp, hg, ModuleCat.hom_zero, map_zero_right_apply] at hh
        have he : map k A B f.hom g.hom (map k A B LinearMap.id (V.d 1 0).hom x) = 0 := by
          convert! hh using 1
          all_goals try with_reducible_and_instances rfl
        rw [he, map_zero]
      | succ s =>
        simp only [LinearMap.comp_apply, cubicInsert_d,
          horizontal_succ_apply k A B U V s 1 (s+1) rfl,
          vertical_succ_apply k A B U V (s+1) 0 (s+1) (Nat.add_zero _), map_add,
          bottomMap_positive, bottomMap_bottom, zero_add]
        have hh := map_comp_apply k A B (𝟙 (U.X (s+1))) f (V.d 1 0) g x
        simp only [Category.id_comp, hg, ModuleCat.hom_zero, map_zero_right_apply] at hh
        have he : map k A B f.hom g.hom (map k A B LinearMap.id (V.d 1 0).hom x) = 0 := by
          convert! hh using 1
          all_goals try with_reducible_and_instances rfl
        rw [he, map_zero]
    | succ j =>
      cases i with
      | zero =>
        simp (disch := omega) only [LinearMap.comp_apply, cubicInsert_d,
          horizontal_zero, hom_zero_apply_p0, vertical_succ_apply, zero_add,
          bottomMap_positive]
      | succ i =>
        simp (disch := omega) only [LinearMap.comp_apply, cubicInsert_d,
          horizontal_succ_apply, vertical_succ_apply, map_add, bottomMap_positive,
          zero_add]

end ArExplicit.ExternalTensor

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Tensor_ExternalTensorBottomCubic
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ExternalTensor.diagonalZeroUnique _root_.OAI.ArExplicit.ExternalTensor.hasHomCochainTotal _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
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
variable (P U : ChainComplex (ModuleCat.{u} A) ℕ) (Q V : ChainComplex (ModuleCat.{u} B) ℕ)

theorem bottomMap_add (s t : ℕ) (f f' : U.X s ⟶ P.X t) (g : V.X 0 ⟶ Q.X 0) :
    bottomMap k A B P Q U V s t (f+f') g =
      bottomMap k A B P Q U V s t f g + bottomMap k A B P Q U V s t f' g := by
  apply LinearMap.ext
  intro x
  have hh := congrArg (fun h => h.hom (bottomProjection k A B U V s x))
    (mapHom_add_left k A B f f' g)
  change map k A B (f+f').hom g.hom _ =
    map k A B f.hom g.hom _ + map k A B f'.hom g.hom _ at hh
  simpa only [bottomMap, LinearMap.comp_apply, LinearMap.add_apply, map_add] using
    congrArg (cubicInsert k A B P Q t ⟨(t,0),Nat.add_zero t⟩) hh

theorem firstCubic_bottomMap (p : (n : ℕ) → P.X (n+3) ⟶ P.X n)
    (s n : ℕ) (f : U.X s ⟶ P.X (n+3)) (g : V.X 0 ⟶ Q.X 0) :
    (firstCubic k A B P Q p n).comp (bottomMap k A B P Q U V s (n+3) f g) =
      bottomMap k A B P Q U V s n (f ≫ p n) g := by
  apply LinearMap.ext
  intro x
  simp only [LinearMap.comp_apply, bottomMap, firstCubic_insert, firstCubicEntry]
  congr 1
  have hh := map_comp_apply k A B f (p n) g (𝟙 (Q.X 0))
    (bottomProjection k A B U V s x)
  simp only [Category.comp_id] at hh
  convert! hh using 1
  all_goals try with_reducible_and_instances rfl

theorem secondCubic_bottomMap (r : (n : ℕ) → Q.X (n+3) ⟶ Q.X n)
    (s n : ℕ) (f : U.X s ⟶ P.X (n+3)) (g : V.X 0 ⟶ Q.X 0) :
    (secondCubic k A B P Q r n).comp (bottomMap k A B P Q U V s (n+3) f g) = 0 := by
  apply LinearMap.ext
  intro x
  simp only [LinearMap.comp_apply, bottomMap, secondCubic_insert, secondCubicEntry,
    LinearMap.zero_apply]

end ArExplicit.ExternalTensor

end

end OAI
end


