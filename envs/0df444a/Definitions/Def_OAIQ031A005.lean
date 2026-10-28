-- Prove2me | Definitions.Def_OAIQ031A005
-- name    : OAIQ031A005
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T13:56:49.146362+00:00
-- url     : https://prove2.me/theorems/b3fbe6e4-3f7e-438f-a30d-d11565a462f7
-- title:
--   Definitions bundle OAIQ031A005 of the split of OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.ArExplicit.Statement.main`, carved from OpenAI's openai/math development (OpenAI, *An explicit counterexample to the Auslander-Reiten conjecture (result family 199)*, OpenAI Math Release, September 23, 2026, result family 199, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 46 declarations of OpenAI's Lean: 20 definitions, 1 inductive type or structure and 25 theorems. The definitions and types are `OAI.ArExplicit.AbsoluteBar.boundary`, `OAI.ArExplicit.AbsoluteBar.left`, `OAI.ArExplicit.AbsoluteBar.object`, `OAI.ArExplicit.AbsoluteBar.right`, `OAI.ArExplicit.CocycleData.TripleMonomial.linear`, `OAI.ArExplicit.CocycleData.differentialTerms`, `OAI.ArExplicit.CocycleData.evalMul`, `OAI.ArExplicit.CocycleData.evalQuad`, `OAI.ArExplicit.CocycleData.evalTriple`, `OAI.ArExplicit.CocycleData.p`, `OAI.ArExplicit.ExternalTensor.Diagonal`, `OAI.ArExplicit.ExternalTensor.EnvelopingProduct`, `OAI.ArExplicit.ExternalTensor.ProductEnveloping`, `OAI.ArExplicit.ExternalTensor.envelopingEquiv`, `OAI.ArExplicit.TwoCone.Data`, `OAI.ArExplicit.TwoCone.firstTerm`, `OAI.ArExplicit.TwoCone.secondOnFirst`, `OAI.ArExplicit.TwoCone.term`, `OAI.ArExplicit.conePreviousTermEquiv`, `OAI.ArExplicit.coneTermEquiv`, `OAI.ArExplicit.moduleCatBaseModule`.
--
--   **Sources.** They come from these modules of lean/OAI/Algebra, in whole or in part: `AuslanderReiten_Bar_BarComplex`, `AuslanderReiten_Bar_BarSuffix`, `AuslanderReiten_BaseChange_ScalarExtensionComplete`, `AuslanderReiten_Cocycles_CocycleCertificate`, `AuslanderReiten_Cocycles_CocycleDifferential`, `AuslanderReiten_Cocycles_CocycleFormula`, `AuslanderReiten_Cocycles_SparseCocycle`, `AuslanderReiten_Cocycles_SparseParity`, `AuslanderReiten_Cones_MappingConeCokernel`, `AuslanderReiten_Cones_MappingConeModule`, `AuslanderReiten_Cones_TwoCone`, `AuslanderReiten_Tensor_BalancedTensorFirst`, `AuslanderReiten_Tensor_ExternalEnveloping`, `AuslanderReiten_Tensor_ExternalTensorComplex`, `AuslanderReiten_Tensor_ExternalTensorCubicChain`.
--
--   **Imports.** It imports the bundle `OAIQ031A000` of this split; the published statement `OAI.ArExplicit.CocycleData.certificate_valid`.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ031A027`, `OAIQ031A028`, `OAIQ031A029`, `OAIQ031A030`, `OAIQ031A031`, `OAIQ031A032`, `OAIQ031A034`, `OAIQ031A037`, `OAIQ031A038`, `OAIQ031A039`, `OAIQ031A040` and `OAIQ031A042`.
-- source:
--   OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 199; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/An-explicit-counterexample-to-the-Auslander-Reiten-conjecture-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algebra at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ031A000
import Theorems.Thm_OAI_ArExplicit_CocycleData_certificate_valid

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

abbrev object : ℕ → ModuleCat.{u} k
  | 0 => ModuleCat.of k R
  | n + 1 => ModuleCat.of k (R ⊗[k] object n)

def left : (n : ℕ) → R →ₐ[k] Module.End k (object k R n)
  | 0 => Algebra.lsmul k k R
  | n + 1 => (Module.End.rTensorAlgHom k R (object k R n)).comp (Algebra.lsmul k k R)

def right : (n : ℕ) → Rᵐᵒᵖ →ₐ[k] Module.End k (object k R n)
  | 0 => Algebra.lsmul k k R
  | n + 1 => (Module.End.lTensorAlgHom k (object k R n) R).comp (right n)

@[simp] theorem left_zero (a x : R) : left k R 0 a x = a * x := rfl
@[simp] theorem right_zero (a : Rᵐᵒᵖ) (x : R) : right k R 0 a x = x * MulOpposite.unop a := rfl
@[simp] theorem left_tmul (n : ℕ) (a b : R) (x : object k R n) :
    left k R (n + 1) a (b ⊗ₜ[k] x) = (a * b) ⊗ₜ[k] x := rfl
@[simp] theorem right_tmul (n : ℕ) (a : Rᵐᵒᵖ) (b : R) (x : object k R n) :
    right k R (n + 1) a (b ⊗ₜ[k] x) = b ⊗ₜ[k] right k R n a x := rfl

@[simp] theorem left_one (n : ℕ) (x : object k R n) : left k R n 1 x = x := by
  rw [map_one]
  rfl

theorem left_mul (n : ℕ) (a b : R) (x : object k R n) :
    left k R n (a * b) x = left k R n a (left k R n b x) := by
  rw [map_mul]
  rfl

def boundary : (n : ℕ) → object k R (n + 1) →ₗ[k] object k R n
  | 0 => LinearMap.mul' k R
  | n + 1 => TensorProduct.lift (left k R (n + 1)).toLinearMap + (boundary n).lTensor R

@[simp] theorem boundary_zero_tmul (a b : R) : boundary k R 0 (a ⊗ₜ[k] b) = a * b := rfl
@[simp] theorem boundary_succ_tmul (n : ℕ) (a : R) (x : object k R (n + 1)) :
    boundary k R (n + 1) (a ⊗ₜ[k] x) =
      left k R (n + 1) a x + a ⊗ₜ[k] boundary k R n x := rfl

variable [CharP k 2]

theorem double_zero_p1 {V : Type u} [AddCommGroup V] [Module k V] (x : V) : x + x = 0 := by
  have htwo : (2 : k) = 0 := CharP.cast_eq_zero k 2
  rw [← two_smul k x, htwo, zero_smul]

end ArExplicit.AbsoluteBar

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Bar_BarSuffix
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

variable [CharP k 2]

theorem double_zero_p2 {V : Type u} [AddCommGroup V] [Module k V] (x : V) : x + x = 0 := by
  have htwo : (2 : k) = 0 := CharP.cast_eq_zero k 2
  rw [← two_smul k x, htwo, zero_smul]

end ArExplicit.AbsoluteBar

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_BaseChange_ScalarExtensionComplete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory
open scoped TensorProduct
namespace ArExplicit
universe u v w
variable (k : Type u) [Field k] (E : Type v) [Field E] [Algebra k E]
  (R : Type w) [Ring R] [Algebra k R]

@[instance_reducible]
def moduleCatBaseModule (M : ModuleCat.{w} R) : Module k M :=
  Module.compHom M (algebraMap k R)

attribute [local instance] moduleCatBaseModule

theorem moduleCatBaseTower (M : ModuleCat.{w} R) : IsScalarTower k R M :=
  IsScalarTower.of_algebraMap_smul fun _ _ => rfl

attribute [local instance] moduleCatBaseTower

end ArExplicit

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Cocycles_CocycleDifferential
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ArExplicit.CocycleData

def differentialTerms : List QuadMonomial :=
  cochain.flatMap fun p => multiplication.flatMap (contributions p)

theorem differentialBlock_eq (a : TIndex) :
    differentialBlock a = differentialTerms.filter (fun x => decide (x.first = a)) := by
  simp [differentialBlock, differentialTerms, List.filter_flatMap]

end ArExplicit.CocycleData

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Cocycles_SparseParity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ArExplicit.SparseParity

variable {α : Type*}

theorem sum_eq_zero_of_paired {α M : Type*} [DecidableEq α]
    [AddCommMonoid M] (hchar : ∀ x : M, x + x = 0) (f : α → M)
    (l : List α) (hl : paired l = true) : (l.map f).sum = 0 := by
  induction l using paired.induct with
  | case1 => rfl
  | case2 a b rest ih =>
    simp only [paired, Bool.and_eq_true, decide_eq_true_eq] at hl
    rcases hl with ⟨rfl, hrest⟩
    simp only [List.map_cons, List.sum_cons, ← add_assoc, hchar, zero_add]
    exact ih hrest
  | case3 a => simp [paired] at hl

theorem sum_insert {α M : Type*} [AddCommMonoid M] (cmp : α → α → Bool)
    (f : α → M) (a : α) (l : List α) :
    ((insert cmp a l).map f).sum = f a + (l.map f).sum := by
  induction l with
  | nil => simp [insert]
  | cons b l ih =>
    simp only [insert]
    split <;> simp_all [add_left_comm]

theorem sum_sort {α M : Type*} [AddCommMonoid M] (cmp : α → α → Bool)
    (f : α → M) (l : List α) : ((sort cmp l).map f).sum = (l.map f).sum := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [sort, sum_insert, ih]

theorem sum_eq_zero_of_sorted_paired {α M : Type*} [DecidableEq α] [AddCommMonoid M]
    (hchar : ∀ x : M, x + x = 0) (f : α → M) (l : List α) (cmp : α → α → Bool)
    (hl : paired (sort cmp l) = true) : (l.map f).sum = 0 := by
  rw [← sum_sort cmp f l]
  exact sum_eq_zero_of_paired hchar f _ hl

end ArExplicit.SparseParity

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Cocycles_CocycleCertificate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ArExplicit.CocycleData

theorem differentialBlock_sum_zero {M : Type*} [AddCommMonoid M]
    (hchar : ∀ x : M, x + x = 0) (f : QuadMonomial → M) (a : TIndex) :
    ((differentialBlock a).map f).sum = 0 :=
  SparseParity.sum_eq_zero_of_sorted_paired hchar f _ _ (certificate_valid a)

theorem sum_partition {α ι M : Type*} [Fintype ι] [DecidableEq ι]
    [AddCommMonoid M] (l : List α) (key : α → ι) (f : α → M) :
    (l.map f).sum = ∑ i, ((l.filter fun a => decide (key a = i)).map f).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    have hstep (i : ι) :
        (((a :: l).filter fun x => decide (key x = i)).map f).sum =
          (if key a = i then f a else 0) + ((l.filter fun x => decide (key x = i)).map f).sum := by
      by_cases h : key a = i <;> simp [h]
    simp_rw [hstep]
    simp [Finset.sum_add_distrib, ← ih]

theorem differentialTerms_sum_zero {M : Type*} [AddCommMonoid M]
    (hchar : ∀ x : M, x + x = 0) (f : QuadMonomial → M) :
    (differentialTerms.map f).sum = 0 := by
  rw [sum_partition differentialTerms QuadMonomial.first f]
  apply Finset.sum_eq_zero
  intro a _
  rw [← differentialBlock_eq]
  exact differentialBlock_sum_zero hchar f a

end ArExplicit.CocycleData

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Cocycles_SparseCocycle
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ArExplicit.CocycleData

variable {k : Type*} [Field k] (q : k)

def evalMul (a b : T k q) (m : MulMonomial) : T k q :=
  (q ^ m.degree * T.coefficient q m.first a * T.coefficient q m.second b) • T.vector q m.output

def TripleMonomial.linear (p : TripleMonomial) :
    T k q →ₗ[k] T k q →ₗ[k] T k q →ₗ[k] T k q :=
  (T.coefficient q p.first).smulRight
    ((T.coefficient q p.second).smulRight
      ((T.coefficient q p.third).smulRight (q ^ p.degree • T.vector q p.output)))

def evalTriple (a b c : T k q) (p : TripleMonomial) : T k q :=
  (q ^ p.degree * T.coefficient q p.first a * T.coefficient q p.second b *
    T.coefficient q p.third c) • T.vector q p.output

def p : T k q →ₗ[k] T k q →ₗ[k] T k q →ₗ[k] T k q :=
  (cochain.map (TripleMonomial.linear q)).sum

end ArExplicit.CocycleData

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Cocycles_CocycleFormula
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ArExplicit.CocycleData

variable {α β k : Type*} [Field k] (q : k)

def evalQuad (a b c d : T k q) (m : QuadMonomial) : T k q :=
  (q ^ m.degree * T.coefficient q m.first a * T.coefficient q m.second b *
    T.coefficient q m.third c * T.coefficient q m.fourth d) • T.vector q m.output

end ArExplicit.CocycleData

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Cones_MappingConeModule
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

def coneTermEquiv (i : ℤ) : (mappingCone φ).X i ≃ₗ[R] G.X i × F.X (i + 1) where
  toLinearMap := ((snd φ).v i i (add_zero i)).hom.prod ((fst φ).1.v i (i + 1) rfl).hom
  invFun x := ((inr φ).f i).hom x.1 + ((inl φ).v (i + 1) i (by omega)).hom x.2
  left_inv x := by
    have h := congrArg (fun f : (mappingCone φ).X i ⟶ (mappingCone φ).X i => f.hom x)
      (id_X φ i (i + 1) rfl)
    simpa [add_comm] using h
  right_inv x := by
    apply Prod.ext
    · change ((snd φ).v i i (add_zero i)).hom
        (((inr φ).f i).hom x.1 + ((inl φ).v (i + 1) i (by omega)).hom x.2) = x.1
      rw [map_add]
      change (((inr φ).f i ≫ (snd φ).v i i (add_zero i)).hom x.1) +
        (((inl φ).v (i + 1) i (by omega) ≫ (snd φ).v i i (add_zero i)).hom x.2) = x.1
      simp
    · change ((fst φ).1.v i (i + 1) rfl).hom
        (((inr φ).f i).hom x.1 + ((inl φ).v (i + 1) i (by omega)).hom x.2) = x.2
      rw [map_add]
      change (((inr φ).f i ≫ (fst φ).1.v i (i + 1) rfl).hom x.1) +
        (((inl φ).v (i + 1) i (by omega) ≫ (fst φ).1.v i (i + 1) rfl).hom x.2) = x.2
      simp

@[simp] theorem coneTermEquiv_fst (i : ℤ) (x : (mappingCone φ).X i) :
    (coneTermEquiv φ i x).1 = ((snd φ).v i i (add_zero i)).hom x := rfl

@[simp] theorem coneTermEquiv_snd (i : ℤ) (x : (mappingCone φ).X i) :
    (coneTermEquiv φ i x).2 = ((fst φ).1.v i (i + 1) rfl).hom x := rfl

end ArExplicit

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Cones_MappingConeCokernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory HomologicalComplex
open CochainComplex CochainComplex.HomComplex

namespace ArExplicit

universe u

variable {R : Type u} [Ring R]
variable {F G : CochainComplex (ModuleCat.{u} R) ℤ} (φ : F ⟶ G)

def conePreviousTermEquiv :
    (mappingCone φ).X (-1) ≃ₗ[R] (G.X (-1) × F.X 0) := by
  simpa using coneTermEquiv φ (-1)

end ArExplicit

end

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

structure Data (R : Type u) [Ring R] where
  term : ℕ → ModuleCat.{u} R
  d : (n : ℕ) → term (n+1) →ₗ[R] term n
  first : (n : ℕ) → term (n+3) →ₗ[R] term n
  second : (n : ℕ) → term (n+3) →ₗ[R] term n
  square : ∀ n, (d n).comp (d (n+1)) = 0
  first_comm : ∀ n, (d n).comp (first (n+1)) = (first n).comp (d (n+3))
  second_comm : ∀ n, (d n).comp (second (n+1)) = (second n).comp (d (n+3))
  comparisons_comm : ∀ n,
    (first n).comp (second (n+3)) = (second n).comp (first (n+3))

variable (D : Data R)

abbrev firstTerm (n : ℕ) : ModuleCat.{u} R :=
  ModuleCat.of R (D.term n × D.term (n+2))

def secondOnFirst (n : ℕ) : firstTerm D (n+3) →ₗ[R] firstTerm D n :=
  (D.second n).prodMap (D.second (n+2))

abbrev term (n : ℕ) : ModuleCat.{u} R :=
  ModuleCat.of R (firstTerm D n × firstTerm D (n+2))

end ArExplicit.TwoCone

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Tensor_BalancedTensorFirst
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ArExplicit.BalancedTensor

universe u
variable {k R F G Q X : Type u} [Field k] [Ring R] [Algebra k R]
variable [AddCommGroup F] [Module k F] [Module Rᵐᵒᵖ F] [IsScalarTower k Rᵐᵒᵖ F]
variable [AddCommGroup G] [Module k G] [Module Rᵐᵒᵖ G] [IsScalarTower k Rᵐᵒᵖ G]
variable [AddCommGroup Q] [Module k Q] [Module Rᵐᵒᵖ Q] [IsScalarTower k Rᵐᵒᵖ Q]
variable [AddCommGroup X] [Module k X] [Module R X] [IsScalarTower k R X]

theorem exists_splitting (f : F →ₗ[Rᵐᵒᵖ] G) (g : G →ₗ[Rᵐᵒᵖ] Q)
    (hf : Function.Injective f) (hg : Function.Surjective g)
    (he : LinearMap.range f = LinearMap.ker g) [Module.Projective Rᵐᵒᵖ Q] :
    ∃ c : G →ₗ[Rᵐᵒᵖ] F, ∃ s : Q →ₗ[Rᵐᵒᵖ] G,
      c.comp f = LinearMap.id ∧ g.comp s = LinearMap.id ∧
        f.comp c + s.comp g = LinearMap.id := by
  obtain ⟨s, hs⟩ := Module.projective_lifting_property g (LinearMap.id : Q →ₗ[Rᵐᵒᵖ] Q) hg
  let e : F ≃ₗ[Rᵐᵒᵖ] LinearMap.range f := LinearEquiv.ofBijective f.rangeRestrict
    ⟨fun x y h => hf (congrArg Subtype.val h), by
      rintro ⟨y, x, rfl⟩
      exact ⟨x, rfl⟩⟩
  let r : G →ₗ[Rᵐᵒᵖ] LinearMap.range f :=
    { toFun := fun y => ⟨y - s (g y), by
        rw [he]
        change g (y - s (g y)) = 0
        rw [map_sub, show g (s (g y)) = g y from DFunLike.congr_fun hs (g y), sub_self]⟩
      map_add' a b := by
        apply Subtype.ext
        change a + b - s (g (a + b)) = (a - s (g a)) + (b - s (g b))
        simp only [map_add, add_sub_add_comm]
      map_smul' a b := by
        apply Subtype.ext
        change a • b - s (g (a • b)) = a • (b - s (g b))
        simp only [map_smul, smul_sub] }
  let c : G →ₗ[Rᵐᵒᵖ] F := e.symm.toLinearMap.comp r
  have hc (y : G) : f (c y) = y - s (g y) := by
    exact congrArg Subtype.val (e.apply_symm_apply (r y))
  have hgf : g.comp f = 0 := LinearMap.range_le_ker_iff.mp he.le
  refine ⟨c, s, ?_, hs, ?_⟩
  · apply LinearMap.ext
    intro x
    apply hf
    rw [LinearMap.comp_apply, hc]
    have hz : g (f x) = 0 := DFunLike.congr_fun hgf x
    simp [hz]
  · apply LinearMap.ext
    intro y
    change f (c y) + s (g y) = y
    rw [hc, sub_add_cancel]

end ArExplicit.BalancedTensor

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Tensor_ExternalEnveloping
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory
open scoped TensorProduct

namespace ArExplicit.ExternalTensor

attribute [local instance] RingHomInvPair.of_ringEquiv RingHomInvPair.of_ringEquiv_symm

universe u
variable (k A B : Type u) [Field k] [Ring A] [Ring B] [Algebra k A] [Algebra k B]

abbrev ProductEnveloping := (A ⊗[k] Aᵐᵒᵖ) ⊗[k] (B ⊗[k] Bᵐᵒᵖ)
abbrev EnvelopingProduct := (A ⊗[k] B) ⊗[k] (A ⊗[k] B)ᵐᵒᵖ

def envelopingEquiv : ProductEnveloping k A B ≃ₐ[k] EnvelopingProduct k A B :=
  (Algebra.TensorProduct.tensorTensorTensorComm k k k k A Aᵐᵒᵖ B Bᵐᵒᵖ).trans
    (Algebra.TensorProduct.congr (AlgEquiv.refl : (A ⊗[k] B) ≃ₐ[k] (A ⊗[k] B))
      (Algebra.TensorProduct.opAlgEquiv k k A B))

@[simp] theorem envelopingEquiv_tmul (a c : A) (b d : B) :
    envelopingEquiv k A B ((a ⊗ₜ[k] MulOpposite.op c) ⊗ₜ[k] (b ⊗ₜ[k] MulOpposite.op d)) =
      (a ⊗ₜ[k] b) ⊗ₜ[k] MulOpposite.op (c ⊗ₜ[k] d) := by
  simp [envelopingEquiv]

@[simp] theorem envelopingEquiv_symm_tmul (a c : A) (b d : B) :
    (envelopingEquiv k A B).symm ((a ⊗ₜ[k] b) ⊗ₜ[k] MulOpposite.op (c ⊗ₜ[k] d)) =
      (a ⊗ₜ[k] MulOpposite.op c) ⊗ₜ[k] (b ⊗ₜ[k] MulOpposite.op d) := by
  apply (envelopingEquiv k A B).injective
  simp

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

abbrev Diagonal (n : ℕ) := {p : ℕ × ℕ // p.1 + p.2 = n}

end ArExplicit.ExternalTensor

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Tensor_ExternalTensorCubicChain
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

theorem hom_zero_apply_p1 {M N : ModuleCat.{u} E} (x : M) : (0 : M ⟶ N) x = 0 := rfl

end ArExplicit.ExternalTensor

end

end OAI
end


