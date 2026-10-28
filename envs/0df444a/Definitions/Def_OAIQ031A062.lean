-- Prove2me | Definitions.Def_OAIQ031A062
-- name    : OAIQ031A062
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T14:11:28.806597+00:00
-- url     : https://prove2.me/theorems/09d1c9a2-37f2-4e78-9069-446d0e7c51d4
-- title:
--   Definitions bundle OAIQ031A062 of the split of OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.ArExplicit.Statement.main`, carved from OpenAI's openai/math development (OpenAI, *An explicit counterexample to the Auslander-Reiten conjecture (result family 199)*, OpenAI Math Release, September 23, 2026, result family 199, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 32 declarations of OpenAI's Lean: 8 definitions and 24 theorems. The definitions and types are `OAI.ArExplicit.AbsoluteBar.IsCocycle3`, `OAI.ArExplicit.AbsoluteBar.bimoduleMap`, `OAI.ArExplicit.AbsoluteBar.casimirInsertion`, `OAI.ArExplicit.AbsoluteBar.casimirMap`, `OAI.ArExplicit.AbsoluteBar.suffixComparisonMap`, `OAI.ArExplicit.ExternalTensor.twoConeData`, `OAI.ArExplicit.T.twistedCasimir`, `OAI.ArExplicit.TwoCone.Cokernel`.
--
--   **Sources.** They come from these modules of lean/OAI/Algebra, in whole or in part: [`AuslanderReiten_Algebras_TMultiplication`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Algebras/TMultiplication.lean), [`AuslanderReiten_Bar_BarCasimir`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Bar/BarCasimir.lean), [`AuslanderReiten_Bar_BarCochain`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Bar/BarCochain.lean), [`AuslanderReiten_Bar_BarSuffix`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Bar/BarSuffix.lean), [`AuslanderReiten_Bar_TCasimir`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Bar/TCasimir.lean), [`AuslanderReiten_Cones_TwoCone`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Cones/TwoCone.lean), [`AuslanderReiten_Tensor_ExternalTensorCubicChain`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Tensor/ExternalTensorCubicChain.lean), [`AuslanderReiten_Tensor_ExternalTensorTwoCone`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Tensor/ExternalTensorTwoCone.lean).
--
--   **Imports.** It imports the bundles `OAIQ031A045` and `OAIQ031A046` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ031A078`, `OAIQ031A079`, `OAIQ031A080`, `OAIQ031A081`, `OAIQ031A083`, `OAIQ031A086`, `OAIQ031A088` and `OAIQ031A089`.
-- source:
--   OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 199; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/An-explicit-counterexample-to-the-Auslander-Reiten-conjecture-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algebra at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ031A045
import Definitions.Def_OAIQ031A046

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Algebras_TMultiplication
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.Resolution.instIsScalarTowerTSimple _root_.OAI.ArExplicit.Resolution.instModuleTSimple _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
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

theorem upper_product_coefficient (a b : T k q) (i : Letter) :
    T.coefficient q (true, i) (a * b) =
      (∑ jidx, (basisVector q i * a.base).coeff jidx * b.dual (basisVector q jidx)) +
      (∑ jidx, (b.base * basisVector q i).coeff jidx * a.dual (basisVector q jidx)) := by
  change b.dual (basisVector q i * a.base) + a.dual (b.base * basisVector q i) = _
  rw [dual_apply, dual_apply]

theorem multiplication_true_e (a b : T k q) :
    T.coefficient q (true, .e) (a * b) = multiplicationCoefficient q a b (true, .e) := by
  rw [upper_product_coefficient]
  simp [multiplicationCoefficient, multiplication, T.coefficient, BaseAlgebra.product, Letter.sum_univ]
  ring

theorem multiplication_true_x (a b : T k q) :
    T.coefficient q (true, .x) (a * b) = multiplicationCoefficient q a b (true, .x) := by
  rw [upper_product_coefficient]
  simp [multiplicationCoefficient, multiplication, T.coefficient, BaseAlgebra.product, Letter.sum_univ]
  ring

theorem multiplication_true_y (a b : T k q) :
    T.coefficient q (true, .y) (a * b) = multiplicationCoefficient q a b (true, .y) := by
  rw [upper_product_coefficient]
  simp [multiplicationCoefficient, multiplication, T.coefficient, BaseAlgebra.product, Letter.sum_univ]
  ring

theorem multiplication_true_z (a b : T k q) :
    T.coefficient q (true, .z) (a * b) = multiplicationCoefficient q a b (true, .z) := by
  rw [upper_product_coefficient]
  simp [multiplicationCoefficient, multiplication, T.coefficient, BaseAlgebra.product, Letter.sum_univ]
  ring

theorem multiplication_true_u (a b : T k q) :
    T.coefficient q (true, .u) (a * b) = multiplicationCoefficient q a b (true, .u) := by
  rw [upper_product_coefficient]
  simp [multiplicationCoefficient, multiplication, T.coefficient, BaseAlgebra.product, Letter.sum_univ]
  ring

theorem multiplication_true_v (a b : T k q) :
    T.coefficient q (true, .v) (a * b) = multiplicationCoefficient q a b (true, .v) := by
  rw [upper_product_coefficient]
  simp [multiplicationCoefficient, multiplication, T.coefficient, BaseAlgebra.product, Letter.sum_univ]
  ring

theorem multiplication_true_t (a b : T k q) :
    T.coefficient q (true, .t) (a * b) = multiplicationCoefficient q a b (true, .t) := by
  rw [upper_product_coefficient]
  simp [multiplicationCoefficient, multiplication, T.coefficient, BaseAlgebra.product, Letter.sum_univ]
  ring

theorem multiplication_true_j (a b : T k q) :
    T.coefficient q (true, .j) (a * b) = multiplicationCoefficient q a b (true, .j) := by
  rw [upper_product_coefficient]
  simp [multiplicationCoefficient, multiplication, T.coefficient, BaseAlgebra.product, Letter.sum_univ]
  ring

theorem multiplication_true_f (a b : T k q) :
    T.coefficient q (true, .f) (a * b) = multiplicationCoefficient q a b (true, .f) := by
  rw [upper_product_coefficient]
  simp [multiplicationCoefficient, multiplication, T.coefficient, BaseAlgebra.product, Letter.sum_univ]
  ring

theorem multiplication_true_n (a b : T k q) :
    T.coefficient q (true, .n) (a * b) = multiplicationCoefficient q a b (true, .n) := by
  rw [upper_product_coefficient]
  simp [multiplicationCoefficient, multiplication, T.coefficient, BaseAlgebra.product, Letter.sum_univ]
  ring

end CocycleData
end ArExplicit

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Bar_BarCochain
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

def bimoduleMap {n m : ℕ} (f : object k R n →ₗ[k] object k R m)
    (hl : ∀ a x, f (left k R n a x) = left k R m a (f x))
    (hr : ∀ a x, f (right k R n a x) = right k R m a (f x)) :
    moduleObject k R n →ₗ[Enveloping k R] moduleObject k R m where
  toAddHom := f.toAddHom
  map_smul' a x := by
    let y : object k R n := x
    change f (representation k R n a y) = representation k R m a (f y)
    induction a using OAI.tensorInductionOn with
    | add a b ha hb => simp only [map_add, LinearMap.add_apply, ha, hb]
    | tmul a b =>
      change f (left k R n a (right k R n b y)) =
        left k R m a (right k R m b (f y))
      rw [hl, hr]

theorem suffix3_right (p : Cochain3 k R) (a : Rᵐᵒᵖ) (x : object k R 3) :
    suffix3 k R p (right k R 3 a x) = suffix3 k R p x * MulOpposite.unop a := by
  induction x using OAI.tensorInductionOn with
  | add x y hx hy => simp only [map_add, hx, hy, add_mul]
  | tmul b y =>
    induction y using OAI.tensorInductionOn with
    | add y z hy hz => simp only [map_add, TensorProduct.tmul_add, hy, hz, add_mul]
    | tmul c z =>
      induction z using OAI.tensorInductionOn with
      | add z w hz hw => simp only [map_add, TensorProduct.tmul_add, hz, hw, add_mul]
      | tmul d e => exact (mul_assoc _ _ _).symm

def IsCocycle3 (p : Cochain3 k R) : Prop :=
  ∀ a b c d, a * p b c d + p (a * b) c d + p a (b * c) d +
    p a b (c * d) + p a b c * d = 0

end ArExplicit.AbsoluteBar

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Bar_BarSuffix
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

@[simp] theorem suffixComparison_succ_tmul (p : Cochain3 k R) (n : ℕ)
    (a : R) (x : object k R (n + 3)) :
    suffixComparison k R p (n + 1) (a ⊗ₜ[k] x) = a ⊗ₜ[k] suffixComparison k R p n x := rfl

theorem suffixComparison_left (p : Cochain3 k R) (n : ℕ) (a : R)
    (x : object k R (n + 4)) :
    suffixComparison k R p (n + 1) (left k R (n + 4) a x) =
      left k R (n + 1) a (suffixComparison k R p (n + 1) x) := by
  induction x using OAI.tensorInductionOn with
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul b x => rfl

theorem suffixComparison_right (p : Cochain3 k R) (n : ℕ) (a : Rᵐᵒᵖ)
    (x : object k R (n + 3)) :
    suffixComparison k R p n (right k R (n + 3) a x) =
      right k R n a (suffixComparison k R p n x) := by
  induction n with
  | zero => exact suffix3_right k R p a x
  | succ n ih =>
    induction x using OAI.tensorInductionOn with
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul b x =>
      change b ⊗ₜ[k] suffixComparison k R p n (right k R (n + 3) a x) =
        b ⊗ₜ[k] right k R n a (suffixComparison k R p n x)
      rw [ih]

def suffixComparisonMap (p : Cochain3 k R) (n : ℕ) :
    moduleObject k R (n + 4) →ₗ[Enveloping k R] moduleObject k R (n + 1) :=
  bimoduleMap k R (suffixComparison k R p (n + 1))
    (suffixComparison_left k R p n) (suffixComparison_right k R p (n + 1))

variable [CharP k 2]

theorem suffixComparison_boundary_zero (p : Cochain3 k R) (hp : IsCocycle3 k R p) :
    (boundary k R 0).comp (suffixComparison k R p 1) =
      (suffixComparison k R p 0).comp (boundary k R 3) := by
  ext a b c d e
  change a * (p b c d * e) = suffix3 k R p
    (boundary k R 3 (a ⊗ₜ[k] (b ⊗ₜ[k] (c ⊗ₜ[k] (d ⊗ₜ[k] e)))))
  have h := congrArg (fun x : R => x * e) (hp a b c d)
  simp only [add_mul, zero_mul, mul_assoc] at h
  simp only [boundary_succ_tmul k R 2, boundary_succ_tmul k R 1,
    boundary_succ_tmul k R 0, boundary_zero_tmul k R,
    left_tmul k R 2, left_tmul k R 1, left_tmul k R 0,
    TensorProduct.tmul_add, map_add, suffix3_tmul k R p]
  have h' : a * (p b c d * e) +
      (p (a * b) c d * e + (p a (b * c) d * e +
        (p a b (c * d) * e + p a b c * (d * e)))) = 0 := by
    simpa only [add_assoc] using h
  have hz := double_zero_p2 k (a * (p b c d * e))
  have hh := congrArg (fun x : R => a * (p b c d * e) + x) h'
  simpa only [← add_assoc, hz, zero_add, add_zero] using hh.symm

theorem suffixComparison_boundary (p : Cochain3 k R) (hp : IsCocycle3 k R p) (n : ℕ)
    (x : object k R (n + 4)) :
    boundary k R n (suffixComparison k R p (n + 1) x) =
      suffixComparison k R p n (boundary k R (n + 3) x) := by
  induction n with
  | zero => exact LinearMap.congr_fun (suffixComparison_boundary_zero k R p hp) x
  | succ n ih =>
    induction x using OAI.tensorInductionOn with
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul a x =>
      change boundary k R (n + 1) (a ⊗ₜ[k] suffixComparison k R p (n + 1) x) =
        suffixComparison k R p (n + 1) (boundary k R (n + 4) (a ⊗ₜ[k] x))
      rw [boundary_succ_tmul k R n, boundary_succ_tmul k R (n + 3), map_add,
        suffixComparison_left k R p n, suffixComparison_succ_tmul, ih]

end ArExplicit.AbsoluteBar

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Bar_BarCasimir
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

def casimirMap (ξ : object k R 1) : R →ₗ[k] object k R 1 :=
  (left k R 1).toLinearMap.flip ξ

@[simp] theorem casimirMap_apply (ξ : object k R 1) (a : R) :
    casimirMap k R ξ a = left k R 1 a ξ := rfl

theorem casimirMap_left (ξ : object k R 1) (a b : R) :
    casimirMap k R ξ (a * b) = left k R 1 a (casimirMap k R ξ b) :=
  left_mul k R 1 a b ξ

def casimirInsertion (ξ : object k R 1) : (n : ℕ) → object k R n →ₗ[k] object k R (n + 1)
  | 0 => casimirMap k R ξ
  | n + 1 => (casimirInsertion ξ n).lTensor R

@[simp] theorem casimirInsertion_tmul (ξ : object k R 1) (n : ℕ)
    (a : R) (x : object k R n) :
    casimirInsertion k R ξ (n + 1) (a ⊗ₜ[k] x) =
      a ⊗ₜ[k] casimirInsertion k R ξ n x := rfl

end ArExplicit.AbsoluteBar

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Bar_TCasimir
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.Resolution.instIsScalarTowerTSimple _root_.OAI.ArExplicit.Resolution.instModuleTSimple _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct

namespace ArExplicit.T

variable {k : Type*} [Field k] (q : k)
local notation "R" => T k q

def twistedCasimir (H : kˣ) : AbsoluteBar.object k R 1 :=
  ∑ i : TIndex, TrivialExtension.twist H (vector q i) ⊗ₜ[k] vector q i.star

end ArExplicit.T

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Cones_TwoCone
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
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

abbrev Cokernel (N : ℕ) := term D N ⧸ LinearMap.range (d D N)

@[simp] theorem d_apply (n : ℕ) (a : D.term (n+1)) (b c : D.term (n+3))
    (e : D.term (n+5)) :
    d D n ((a,b),(c,e)) =
      ((D.d n a + D.first n b + D.second n c,
        -D.d (n+2) b + D.second (n+2) e),
       (-D.d (n+2) c - D.first (n+2) e, D.d (n+4) e)) := by
  simp [d, firstD, secondOnFirst, coneBlock_apply, sub_eq_add_neg]
  abel

end ArExplicit.TwoCone

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Tensor_ExternalTensorCubicChain
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
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

variable [CharP k 2]

include hp in

theorem firstCubic_chain (n : ℕ) :
    ((complex k A B P Q).d (n+1) n).hom.comp (firstCubic k A B P Q p (n+1)) =
      (firstCubic k A B P Q p n).comp ((complex k A B P Q).d (n+4) (n+3)).hom := by
  apply cubic_hom_ext k A B P Q (n+4)
  rintro ⟨⟨i,j⟩,h⟩ x
  simp only [LinearMap.comp_apply, firstCubic_insert, cubicInsert_d]
  rcases i with _ | (_ | (_ | (_ | i))) <;> rcases j with _ | j
  all_goals simp (disch := omega) only [firstCubicEntry, LinearMap.comp_apply, map_zero,
    cubicInsert_d, horizontal_zero, vertical_zero, hom_zero_apply_p1,
    horizontal_succ_apply, vertical_succ_apply, map_add, add_zero, zero_add,
    firstCubic_insert, LinearMap.zero_apply]
  all_goals simp only [first_map_chain k A B P Q p hp, map_interchange k A B]

omit [CharP k 2] in
include hr in
theorem second_map_chain (i j : ℕ)
    (x : moduleObject k A B (P.X i) (Q.X (j+4))) :
    map k A B (LinearMap.id : P.X i →ₗ[A] P.X i) (Q.d (j+1) j).hom
      (map k A B (LinearMap.id : P.X i →ₗ[A] P.X i) (r (j+1)).hom x) =
    map k A B (LinearMap.id : P.X i →ₗ[A] P.X i) (r j).hom
      (map k A B (LinearMap.id : P.X i →ₗ[A] P.X i) (Q.d (j+4) (j+3)).hom x) := by
  have hh := congrArg (fun f => mapHom k A B (𝟙 (P.X i)) f) (hr j)
  rw [show 𝟙 (P.X i) = 𝟙 (P.X i) ≫ 𝟙 (P.X i) from (Category.id_comp _).symm,
    mapHom_comp, mapHom_comp] at hh
  exact congrArg (fun f => f.hom x) hh

include hr in

theorem secondCubic_chain (n : ℕ) :
    ((complex k A B P Q).d (n+1) n).hom.comp (secondCubic k A B P Q r (n+1)) =
      (secondCubic k A B P Q r n).comp ((complex k A B P Q).d (n+4) (n+3)).hom := by
  apply cubic_hom_ext k A B P Q (n+4)
  rintro ⟨⟨i,j⟩,h⟩ x
  simp only [LinearMap.comp_apply, secondCubic_insert, cubicInsert_d]
  rcases j with _ | (_ | (_ | (_ | j))) <;> rcases i with _ | i
  all_goals simp (disch := omega) only [secondCubicEntry, LinearMap.comp_apply, map_zero,
    cubicInsert_d, horizontal_zero, vertical_zero, hom_zero_apply_p1,
    horizontal_succ_apply, vertical_succ_apply, map_add, add_zero, zero_add,
    secondCubic_insert, LinearMap.zero_apply]
  all_goals simp only [second_map_chain k A B P Q r hr, map_interchange k A B]

end ArExplicit.ExternalTensor

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Tensor_ExternalTensorTwoCone
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
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
variable [CharP k 2]
variable (P : ChainComplex (ModuleCat.{u} A) ℕ) (Q : ChainComplex (ModuleCat.{u} B) ℕ)
variable (p : (n : ℕ) → P.X (n+3) ⟶ P.X n)
variable (r : (n : ℕ) → Q.X (n+3) ⟶ Q.X n)
variable (hp : ∀ n, p (n+1) ≫ P.d (n+1) n = P.d (n+4) (n+3) ≫ p n)
variable (hr : ∀ n, r (n+1) ≫ Q.d (n+1) n = Q.d (n+4) (n+3) ≫ r n)

abbrev twoConeData : TwoCone.Data (A ⊗[k] B) where
  term := (complex k A B P Q).X
  d n := ((complex k A B P Q).d (n+1) n).hom
  first := firstCubic k A B P Q p
  second := secondCubic k A B P Q r
  square n := congrArg ModuleCat.Hom.hom ((complex k A B P Q).d_comp_d (n+2) (n+1) n)
  first_comm := firstCubic_chain k A B P Q p hp
  second_comm := secondCubic_chain k A B P Q r hr
  comparisons_comm := cubic_commute k A B P Q p r

end ArExplicit.ExternalTensor

end

end OAI
end


