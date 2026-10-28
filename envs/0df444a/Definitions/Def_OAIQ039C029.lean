-- Prove2me | Definitions.Def_OAIQ039C029
-- name    : OAIQ039C029
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-28T06:18:21.368295+00:00
-- url     : https://prove2.me/theorems/8fb22464-24b4-4ebe-ac3d-3d81713b4f7c
-- title:
--   Definitions bundle OAIQ039C029 of the split of OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Kadison.uniform_commutator`, carved from OpenAI's openai/math development (OpenAI, *Kadison's similarity theorem through uniform derivation estimates (result family 288)*, OpenAI Math Release, September 23, 2026, result family 288, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 47 declarations of OpenAI's Lean: 20 definitions, 1 inductive type or structure, 2 instances and 24 theorems. The definitions and types are `OAI.Kadison.MatrixTensor.representation`, `OAI.Kadison.OperatorAmplification.position`, `OAI.Kadison.OperatorFunctionals.coefficient`, `OAI.Kadison.OrbitStateHull.orbit`, `OAI.Kadison.OrbitStateHull.vector`, `OAI.Kadison.Pairing.Crosses`, `OAI.Kadison.Pairing.crossPairing`, `OAI.Kadison.Pairing.crossingEquiv`, `OAI.Kadison.PartialIsometryOrder.PartialDecomposition`, `OAI.Kadison.PartialIsometryOrder.PartialDecomposition.support`, `OAI.Kadison.PartialIsometryOrder.SquareZeroLink`, `OAI.Kadison.PositiveWOT.ProjectionContinuousAtOne`, `OAI.Kadison.RationalStarExtension.instNormedAlgebraRat_solutions_1`, `OAI.Kadison.RationalStarExtension.lift`, `OAI.Kadison.RationalStarExtension.raw`, `OAI.Kadison.RationalStarExtension.realLift`, `OAI.Kadison.SchurWeyl.cycleCard`, `OAI.Kadison.SchurWeyl.cycleCount`, `OAI.Kadison.SchurWeyl.cycleMap`, `OAI.Kadison.SchurWeyl.cycleTrace`, `OAI.Kadison.SchurWeyl.endpointPairingPerm`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis/Commutator, in whole or in part: `Commutator_CrossingPairings`, `Commutator_CycleInvariants`, `Commutator_CycleInvariants2`, `Commutator_CyclePairTrace2`, `Commutator_FiniteFunctionalFactorization`, `Commutator_MatrixTensor`, `Commutator_MultilinearTensors`, `Commutator_OrbitStateHull`, `Commutator_PartialDecomposition`, `Commutator_PolarSupport`, `Commutator_ProjectionNormalPositive`, `Commutator_RationalStarExtension`, `Commutator_RowOperator`, `Commutator_SquareZeroMaximal`, `Commutator_SquareZeroPolar`, `Commutator_TracialL2Tools`.
--
--   **Imports.** It imports the bundles `OAIQ039C001`, `OAIQ039C002`, `OAIQ039C006`, `OAIQ039C008`, `OAIQ039C009`, `OAIQ039C010`, `OAIQ039C014`, `OAIQ039C015` and `OAIQ039C017` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ039C039`, `OAIQ039C040` and `OAIQ039C041`; the statements `OAI.Kadison.PartialIsometryOrder.PartialDecomposition.countable`, `OAI.Kadison.PartialIsometryOrder.exists_partialDecomposition`, `OAI.Kadison.PositiveWOT.positive_strong_null`, `OAI.Kadison.SchurWeyl.centered_expansion_contractions`, `OAI.Kadison.SchurWeyl.centered_expansion_pairings`, `OAI.Kadison.SchurWeyl.cycleTrace_map`, `OAI.Kadison.SchurWeyl.endpoint_coefficients_vanish_of_rank_one` and `OAI.Kadison.SchurWeyl.matrix_union_expansion`; the proofs of `OAI.Kadison.CornerPolarTransfer.compressed_scalar_polar`, `OAI.Kadison.CornerPolarTransfer.defect_bound`, `OAI.Kadison.Decomposable.homomorphisms_ae_of_countable_relations`, `OAI.Kadison.FinitePatching.PartialUnitary.chain_upper_with_L2_and_membership`, `OAI.Kadison.FinitePatching.Words.momentBound_add`, `OAI.Kadison.FinitePatching.Words.momentBound_completed`, `OAI.Kadison.FinitePatching.Words.moment_limit_of_dense_coefficients`, `OAI.Kadison.FinitePatching.Words.word_perturbation_bound`, `OAI.Kadison.FinitePatching.exists_all_unitary_tests`, `OAI.Kadison.FinitePatching.exists_finite_word_patch`, `OAI.Kadison.FinitePatching.trace_centered_compression_bound`, `OAI.Kadison.MatrixGNS.row_corner_commutator_bound`, `OAI.Kadison.PartialIsometryOrder.PartialDecomposition.countable`, `OAI.Kadison.PartialIsometryOrder.exists_partialDecomposition`, `OAI.Kadison.RelativeCornerQuantization.exists_polar_cut`, `OAI.Kadison.RelativeCornerQuantization.exists_relative_centered_compression`, `OAI.Kadison.SchurWeyl.centered_expansion_pairings`, `OAI.Kadison.SchurWeyl.endpoint_coefficients_vanish_of_rank_one`, `OAI.Kadison.SchurWeyl.matrix_union_expansion` and `OAI.Kadison.WOTDistance.annihilator_bound`.
-- source:
--   OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 288; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Kadisons-similarity-theorem-through-uniform-derivation-estimates-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis/Commutator at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ039C001
import Definitions.Def_OAIQ039C002
import Definitions.Def_OAIQ039C006
import Definitions.Def_OAIQ039C008
import Definitions.Def_OAIQ039C009
import Definitions.Def_OAIQ039C010
import Definitions.Def_OAIQ039C014
import Definitions.Def_OAIQ039C015
import Definitions.Def_OAIQ039C017

section
-- module Solutions.OAIQ039_CM.Commutator_MultilinearTensors
attribute [-instance] _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ComplexOrder InnerProductSpace
open Complex ContinuousLinearMap UniformSpace Completion
open scoped InnerProductSpace
open scoped TensorProduct

namespace Kadison.PreHilbert

open Function

lemma pure_update_add (E : PreHilbert) (n : ℕ) (v : Fin n → E) (i : Fin n) (x y : E) :
    pure E n (update v i (x + y)) =
      pure E n (update v i x) + pure E n (update v i y) := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    cases i using Fin.cases with
    | zero => simp [pure_succ, Fin.tail_update_zero, TensorProduct.add_tmul]
    | succ i =>
      simp only [pure_succ, Fin.tail_update_succ, update_of_ne (Fin.succ_ne_zero i).symm]
      rw [ih, TensorProduct.tmul_add]

lemma pure_update_smul (E : PreHilbert) (n : ℕ) (v : Fin n → E) (i : Fin n) (c : ℂ) (x : E) :
    pure E n (update v i (c • x)) = c • pure E n (update v i x) := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    cases i using Fin.cases with
    | zero => simp [pure_succ, Fin.tail_update_zero, TensorProduct.smul_tmul']
    | succ i =>
      simp only [pure_succ, Fin.tail_update_succ, update_of_ne (Fin.succ_ne_zero i).symm]
      rw [ih, TensorProduct.tmul_smul]

end Kadison.PreHilbert
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_CrossingPairings
attribute [-instance] _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ComplexOrder InnerProductSpace
open Complex ContinuousLinearMap UniformSpace Completion
open scoped InnerProductSpace
open scoped TensorProduct
open scoped TensorProduct InnerProductSpace Topology
open UniformSpace Completion Filter
open scoped TensorProduct
open UniformSpace Completion
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder

namespace Kadison

namespace Pairing

def Crosses {k l : ℕ} (τ : Pairing (TailSlots k l)) : Prop :=
  (∀ a : Fin k, ∃ b : Fin l, τ (.inl a) = .inr b) ∧
  (∀ b : Fin l, ∃ a : Fin k, τ (.inr b) = .inl a)

def crossPairing {k l : ℕ} (e : Fin k ≃ Fin l) : Pairing (TailSlots k l) :=
  ⟨{ toFun := Sum.elim (fun a => .inr (e a)) (fun b => .inl (e.symm b))
     invFun := Sum.elim (fun a => .inr (e a)) (fun b => .inl (e.symm b))
     left_inv := by
       intro j
       cases j with
       | inl a => exact congrArg Sum.inl (e.symm_apply_apply a)
       | inr b => exact congrArg Sum.inr (e.apply_symm_apply b)
     right_inv := by
       intro j
       cases j with
       | inl a => exact congrArg Sum.inl (e.symm_apply_apply a)
       | inr b => exact congrArg Sum.inr (e.apply_symm_apply b) },
   by
     intro j
     cases j with
     | inl a => exact congrArg Sum.inl (e.symm_apply_apply a)
     | inr b => exact congrArg Sum.inr (e.apply_symm_apply b),
   by intro j; cases j <;> intro h <;> cases h⟩

@[simp] theorem crossPairing_inl {k l : ℕ} (e : Fin k ≃ Fin l) (a : Fin k) :
    crossPairing e (.inl a) = .inr (e a) := rfl

@[simp] theorem crossPairing_inr {k l : ℕ} (e : Fin k ≃ Fin l) (b : Fin l) :
    crossPairing e (.inr b) = .inl (e.symm b) := rfl

theorem crossPairing_crosses {k l : ℕ} (e : Fin k ≃ Fin l) :
    Crosses (crossPairing e) :=
  ⟨fun a => ⟨e a, rfl⟩, fun b => ⟨e.symm b, rfl⟩⟩

theorem crossPairing_injective {k l : ℕ} :
    Function.Injective (@crossPairing k l) := by
  intro e f h
  apply Equiv.ext
  intro a
  exact Sum.inr_injective (congrArg (fun τ : Pairing (TailSlots k l) => τ (.inl a)) h)

theorem exists_crossPairing {k l : ℕ} (τ : Pairing (TailSlots k l)) (hτ : Crosses τ) :
    ∃ e : Fin k ≃ Fin l, crossPairing e = τ := by
  let f : Fin k → Fin l := fun a => (hτ.1 a).choose
  have hf (a : Fin k) : τ (.inl a) = .inr (f a) := (hτ.1 a).choose_spec
  have hinj : Function.Injective f := by
    intro a b hab
    apply Sum.inl_injective
    apply τ.injective
    rw [hf, hf, hab]
  have hsurj : Function.Surjective f := by
    intro b
    obtain ⟨a, ha⟩ := hτ.2 b
    refine ⟨a, ?_⟩
    have hh := τ.apply_apply (.inr b)
    rw [ha, hf] at hh
    exact Sum.inr_injective hh
  let e : Fin k ≃ Fin l := Equiv.ofBijective f ⟨hinj, hsurj⟩
  refine ⟨e, ?_⟩
  apply ext
  intro j
  cases j with
  | inl a => exact (hf a).symm
  | inr b =>
    apply τ.injective
    erw [τ.apply_apply, crossPairing_inr, hf]
    change Sum.inr (e (e.symm b)) = .inr b
    rw [e.apply_symm_apply]

def crossingEquiv (k l : ℕ) : (Fin k ≃ Fin l) ≃ {τ : Pairing (TailSlots k l) // Crosses τ} :=
  Equiv.ofBijective (fun e => ⟨crossPairing e, crossPairing_crosses e⟩)
    ⟨fun _ _ h => crossPairing_injective (congrArg Subtype.val h), by
      rintro ⟨τ, hτ⟩
      obtain ⟨e, he⟩ := exists_crossPairing τ hτ
      exact ⟨e, Subtype.ext he⟩⟩

@[simp] theorem crossingEquiv_val (k l : ℕ) (e : Fin k ≃ Fin l) :
    (crossingEquiv k l e).val = crossPairing e := rfl

end Pairing

end Kadison
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_CycleInvariants
attribute [-instance] _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ComplexOrder InnerProductSpace
open Complex ContinuousLinearMap UniformSpace Completion
open scoped InnerProductSpace
open scoped TensorProduct

namespace Kadison.SchurWeyl

open Matrix

variable {𝕜 : Type*} [CommRing 𝕜]

variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

instance instFintypeCycleSet (σ : Equiv.Perm J) : Fintype (cycleSet σ) := by
  unfold cycleSet
  exact Fintype.ofFinite _

def cycleCount (σ : Equiv.Perm J) : ℕ := Fintype.card (cycleSet σ)

def cycleTrace (σ : Equiv.Perm J) (A : J → Matrix I I ℂ) : ℂ :=
  (Fintype.card I : ℂ)⁻¹ ^ cycleCount σ * rawCycleTrace σ A

end Kadison.SchurWeyl
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_CycleInvariants2
attribute [-instance] _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ComplexOrder InnerProductSpace
open Complex ContinuousLinearMap UniformSpace Completion
open scoped InnerProductSpace
open scoped TensorProduct

namespace Kadison.SchurWeyl

variable {J : Type*} [Fintype J]

instance instDecidableEqCycleSet (σ : Equiv.Perm J) : DecidableEq (cycleSet σ) := Classical.decEq _

def cycleMap (σ : Equiv.Perm J) (j : J) : cycleSet σ := Quotient.mk _ j

omit [Fintype J] in
@[simp] lemma cycleMap_apply (σ : Equiv.Perm J) (j : J) :
    cycleMap σ (σ j) = cycleMap σ j :=
  Quotient.sound (Equiv.Perm.SameCycle.refl σ j).apply_left

def cycleCard (σ : Equiv.Perm J) (q : cycleSet σ) : ℕ :=
  Fintype.card {j : J // cycleMap σ j = q}

end Kadison.SchurWeyl
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_CyclePairTrace2
attribute [-instance] _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ComplexOrder InnerProductSpace
open Complex ContinuousLinearMap UniformSpace Completion
open scoped InnerProductSpace
open scoped TensorProduct
open scoped TensorProduct InnerProductSpace Topology
open UniformSpace Completion Filter
open scoped TensorProduct
open UniformSpace Completion
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder

namespace Kadison.SchurWeyl

variable {J I : Type*} [Fintype J] [LinearOrder J] [Fintype I] [DecidableEq I]

def endpointPairingPerm (σ : Pairing J) : Equiv.Perm (Option J) := Equiv.optionCongr σ.val

omit [Fintype J] [LinearOrder J] in
@[simp] lemma endpointPairingPerm_none (σ : Pairing J) : endpointPairingPerm σ none = none := rfl

end Kadison.SchurWeyl
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_FiniteFunctionalFactorization
attribute [-instance] _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped BigOperators InnerProductSpace

namespace Kadison.OperatorFunctionals

open InnerProductSpace ContinuousLinearMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def coefficient (φ : StrongDual ℂ (H →L[ℂ] H)) : H →L[ℂ] H :=
  LinearMap.mkContinuous
    { toFun := fun b => (toDual ℂ H).symm (coefficientDual φ b)
      map_add' := by
        intro b c
        apply ext_inner_right ℂ
        intro a
        simp only [inner_add_left,toDual_symm_apply,coefficientDual_apply,
          map_add]
      map_smul' := by
        intro z b
        apply ext_inner_right ℂ
        intro a
        simp only [inner_smul_left,toDual_symm_apply,coefficientDual_apply,
          map_smulₛₗ,RingHom.id_apply,smul_eq_mul] }
    ‖φ‖ (by
      intro b
      change ‖(toDual ℂ H).symm (coefficientDual φ b)‖≤_
      rw [LinearIsometryEquiv.norm_map]
      apply opNorm_le_bound _ (mul_nonneg (norm_nonneg _) (norm_nonneg _))
      intro a
      change ‖φ (rankOne ℂ a b)‖≤_
      exact (φ.le_opNorm (rankOne ℂ a b)).trans_eq (by simp [mul_comm,mul_left_comm,mul_assoc]))

@[simp] lemma inner_coefficient (φ : StrongDual ℂ (H →L[ℂ] H)) (a b : H) :
    inner ℂ (coefficient φ b) a=φ (rankOne ℂ a b) := by
  change inner ℂ ((toDual ℂ H).symm (coefficientDual φ b)) a=_
  rw [toDual_symm_apply,coefficientDual_apply]

end Kadison.OperatorFunctionals

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_MatrixTensor
attribute [-instance] _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped BigOperators

namespace Kadison.MatrixTensor

open Matrix

variable {A I J : Type*} [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A]
  [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

variable (φ : Matrix I I ℂ →⋆ₐ[ℂ] A) (ψ : Matrix J J ℂ →⋆ₐ[ℂ] A)
  (hc : ∀ x y,Commute (φ x) (ψ y))

omit [StarModule ℂ A] in
include hc in
lemma units_mul (i j k l : I×J) :
    (φ (single i.1 j.1 1)*ψ (single i.2 j.2 1))*(φ (single k.1 l.1 1)*ψ (single k.2 l.2 1))=
      if j=k then φ (single i.1 l.1 1)*ψ (single i.2 l.2 1) else 0 := by
  have he : (φ (single i.1 j.1 1)*ψ (single i.2 j.2 1))*(φ (single k.1 l.1 1)*ψ (single k.2 l.2 1))=
      (φ (single i.1 j.1 1)*φ (single k.1 l.1 1))*(ψ (single i.2 j.2 1)*ψ (single k.2 l.2 1)) := by
    simp only [mul_assoc]
    rw [←mul_assoc (ψ (single i.2 j.2 1)),(hc (single k.1 l.1 1) (single i.2 j.2 1)).eq.symm]
    simp only [mul_assoc]
  rw [he,←map_mul,←map_mul]
  by_cases h1 : j.1=k.1 <;> by_cases h2 : j.2=k.2
  · have hjk : j=k := Prod.ext h1 h2
    subst k
    simp only [single_mul_single_same,one_mul,ite_true]
  · have hjk : j≠k := fun h => h2 (congrArg Prod.snd h)
    rw [single_mul_single_of_ne 1 i.2 j.2 k.2 h2 1,map_zero,mul_zero,ite_eq_right hjk]
  · have hjk : j≠k := fun h => h1 (congrArg Prod.fst h)
    rw [single_mul_single_of_ne 1 i.1 j.1 k.1 h1 1,map_zero,zero_mul,ite_eq_right hjk]
  · have hjk : j≠k := fun h => h1 (congrArg Prod.fst h)
    rw [single_mul_single_of_ne 1 i.1 j.1 k.1 h1 1,map_zero,zero_mul,ite_eq_right hjk]

def representation : Matrix (I×J) (I×J) ℂ →⋆ₐ[ℂ] A :=
  MatrixUnits.representation (fun i j => φ (single i.1 j.1 1)*ψ (single i.2 j.2 1))
    (units_mul φ ψ hc) (units_star φ ψ hc) (units_one φ ψ)

@[simp] lemma representation_single (i j : I×J) :
    representation φ ψ hc (single i j 1)=φ (single i.1 j.1 1)*ψ (single i.2 j.2 1) := by
  simp [representation,MatrixUnits.representation,Matrix.single_apply,ite_and]

lemma left_mem (x : Matrix I I ℂ) : φ x∈(representation φ ψ hc).range := by
  have hu (i j : I) : φ (single i j 1)∈(representation φ ψ hc).range := by
    have he : φ (single i j 1)=∑ k : J,representation φ ψ hc (single (i,k) (j,k) 1) := by
      simp only [representation_single,←Finset.mul_sum,←map_sum,sum_single_one,map_one,mul_one]
    rw [he]
    exact (representation φ ψ hc).range.sum_mem (fun k _ => ⟨single (i,k) (j,k) 1,rfl⟩)
  rw [Matrix.matrix_eq_sum_single x,map_sum]
  apply (representation φ ψ hc).range.sum_mem
  intro i hi
  rw [map_sum]
  apply (representation φ ψ hc).range.sum_mem
  intro j hj
  have he : single i j (x i j)=x i j • single i j 1 := by simp
  rw [he,map_smul]
  exact (representation φ ψ hc).range.smul_mem (hu i j) _

lemma right_mem (x : Matrix J J ℂ) : ψ x∈(representation φ ψ hc).range := by
  have hu (i j : J) : ψ (single i j 1)∈(representation φ ψ hc).range := by
    have he : ψ (single i j 1)=∑ k : I,representation φ ψ hc (single (k,i) (k,j) 1) := by
      simp only [representation_single,←Finset.sum_mul,←map_sum,sum_single_one,map_one,one_mul]
    rw [he]
    exact (representation φ ψ hc).range.sum_mem (fun k _ => ⟨single (k,i) (k,j) 1,rfl⟩)
  rw [Matrix.matrix_eq_sum_single x,map_sum]
  apply (representation φ ψ hc).range.sum_mem
  intro i hi
  rw [map_sum]
  apply (representation φ ψ hc).range.sum_mem
  intro j hj
  have he : single i j (x i j)=x i j • single i j 1 := by simp
  rw [he,map_smul]
  exact (representation φ ψ hc).range.smul_mem (hu i j) _

end Kadison.MatrixTensor

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_PolarSupport
attribute [-instance] _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped InnerProductSpace ComplexOrder Topology

namespace Kadison.Polar

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma leftSupport_mul (T : H →L[ℂ] H) : leftSupport T*T=T := by
  calc
    _=(partialIsometry T*star (partialIsometry T))*(partialIsometry T*CFC.abs T) := by
      rw [factorization]; rfl
    _=partialIsometry T*CFC.abs T := by rw [←mul_assoc,partialIsometry_triple]
    _=T := factorization T

end Kadison.Polar

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_SquareZeroPolar
attribute [-instance] _root_.OAI.Kadison.PartialIsometryOrder.instCompleteSpaceSubtypeMemSubmoduleComplexFamilySpace _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped ComplexOrder InnerProductSpace Topology

namespace Kadison.PartialIsometryOrder.Link

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable {M : VonNeumannAlgebra H} {e f : H →L[ℂ] H}

lemma initial_mul_final_eq_zero (v : Link M e f) (hv : v.val*v.val=0) :
    v.initial*v.final=0 := by
  change (star v.val*v.val)*(v.val*star v.val)=0
  calc
    _=star v.val*(v.val*v.val)*star v.val := by noncomm_ring
    _=0 := by rw [hv,mul_zero,zero_mul]

lemma initial_mul_self_eq_zero (v : Link M e f) (hv : v.val*v.val=0) :
    v.initial*v.val=0 := by
  change (star v.val*v.val)*v.val=0
  rw [mul_assoc,hv,mul_zero]

lemma self_mul_final_eq_zero (v : Link M e f) (hv : v.val*v.val=0) :
    v.val*v.final=0 := by
  change v.val*(v.val*star v.val)=0
  rw [←mul_assoc,hv,zero_mul]

end Kadison.PartialIsometryOrder.Link

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_SquareZeroMaximal
attribute [-instance] _root_.OAI.Kadison.PartialIsometryOrder.instCompleteSpaceSubtypeMemSubmoduleComplexFamilySpace _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open Filter

open scoped ComplexOrder InnerProductSpace Topology

namespace Kadison.PartialIsometryOrder

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

abbrev SquareZeroLink (M : VonNeumannAlgebra H) (e : H →L[ℂ] H) :=
  {v : Link M e e // v.val*v.val=0}

end Kadison.PartialIsometryOrder

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_PartialDecomposition
attribute [-instance] _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped ComplexOrder InnerProductSpace Topology BigOperators

open Filter

universe u

namespace Kadison.PartialIsometryOrder

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

structure PartialDecomposition (M : VonNeumannAlgebra H) (p : H →L[ℂ] H) where
  I : Type u
  v : I → Link M p 1
  nonzero : ∀ i,(v i).val≠0
  cross : ∀ i j,i≠j → star (v i).val*(v j).val=0
  strong : ∀ x : H,Tendsto (fun s : Finset I => (∑ i∈s,(v i).final) x) atTop (𝓝 x)

namespace PartialDecomposition

variable {M : VonNeumannAlgebra H} {p : H →L[ℂ] H} (D : PartialDecomposition M p)

def support (s : Finset D.I) : H →L[ℂ] H := ∑ i∈s,(D.v i).final

end PartialDecomposition

end Kadison.PartialIsometryOrder

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_OrbitStateHull
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open Filter

open scoped ComplexOrder InnerProductSpace Topology

namespace Kadison.OrbitStateHull

open PartialIsometryOrder PartialIsometryOrder.DyadicPartition

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (M : VonNeumannAlgebra H)

def vector (x : H) : StrongDual ℂ M :=
  LinearMap.mkContinuous
    { toFun := fun a => inner ℂ x ((a : H →L[ℂ] H) x)
      map_add' := by
        intro a b
        change inner ℂ x ((a : H →L[ℂ] H) x+(b : H →L[ℂ] H) x)=_
        exact inner_add_right _ _ _
      map_smul' := by
        intro c a
        change inner ℂ x (c • (a : H →L[ℂ] H) x)=c*inner ℂ x ((a : H →L[ℂ] H) x)
        exact inner_smul_right _ _ _ }
    (‖x‖*‖x‖) (by
      intro a
      calc
        _ ≤ ‖x‖*‖(a : H →L[ℂ] H) x‖ := norm_inner_le_norm _ _
        _ ≤ ‖x‖*(‖a‖*‖x‖) := mul_le_mul_of_nonneg_left ((a : H →L[ℂ] H).le_opNorm x) (norm_nonneg x)
        _ = ‖x‖*‖x‖*‖a‖ := by ring)

@[simp] lemma vector_apply (x : H) (a : M) :
    vector M x a=inner ℂ x ((a : H →L[ℂ] H) x) := rfl

lemma vector_nonneg (x : H) {a : M} (ha : 0≤a) : 0≤vector M x a :=
  ((ContinuousLinearMap.nonneg_iff_isPositive _).mp ha).inner_nonneg_right x

def orbit (x : H) : Set (WeakDual ℂ M) :=
  {f | ∃ u : unitary (H →L[ℂ] H), (u : H →L[ℂ] H)∈M ∧
    f=(vector M ((u : H →L[ℂ] H) x)).toWeakDual}

end Kadison.OrbitStateHull

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_ProjectionNormalPositive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open Filter

open scoped ComplexOrder InnerProductSpace Topology

namespace Kadison.PositiveWOT

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def ProjectionContinuousAtOne (M : VonNeumannAlgebra H) (f : M →ₚ[ℂ] ℂ) : Prop :=
  ∀ P : ℕ → M,(∀ n,IsStarProjection (P n : H →L[ℂ] H)) →
    Monotone (fun n => (P n : H →L[ℂ] H)) →
    (∀ x,Tendsto (fun n => (P n : H →L[ℂ] H) x) atTop (𝓝 x)) →
    Tendsto (fun n => f (P n)) atTop (𝓝 (f 1))

end Kadison.PositiveWOT

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_RationalStarExtension
attribute [-instance] _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped Topology

namespace Kadison.RationalStarExtension

variable {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]

attribute [local instance] OAI.Kadison.RationalStarExtension.instNormedAlgebraRat_solutions
local instance instNormedAlgebraRat_solutions_1 : NormedAlgebra ℚ B := NormedAlgebra.restrictScalars ℚ ℂ B

local instance instStarModuleRat_solutions_r951b3b_1 : StarModule ℚ A where
  star_smul r a := by
    change star ((r:ℂ) • a)=((star r:ℚ):ℂ) • star a
    simp
local instance instStarModuleRat_solutions_1 : StarModule ℚ B where
  star_smul r b := by
    change star ((r:ℂ) • b)=((star r:ℚ):ℂ) • star b
    simp

variable (S : StarSubalgebra ℚ A)
  (hd : DenseRange (fun a : S => (a:A)))
  (φ : S →⋆ₐ[ℚ] B) (hb : ∀ a : S,‖φ a‖≤‖(a:A)‖)

def raw : S →L[ℚ] B := φ.toAlgHom.toLinearMap.mkContinuous 1 (by
  intro a
  simpa using hb a)

def lift : A →L[ℚ] B := (raw S φ hb).extend S.toSubalgebra.toSubmodule.subtypeL

def realLift : A →L[ℝ] B :=
  (lift S φ hb).toLinearMap.toAddMonoidHom.toRealLinearMap (lift S φ hb).continuous

end Kadison.RationalStarExtension

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_RowOperator
attribute [-instance] _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped BigOperators InnerProductSpace

namespace Kadison.OperatorAmplification

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (ι : Type*) [Fintype ι] [DecidableEq ι]

def position (i j : ι) (a : H →L[ℂ] H) : SumSpace (H:=H) ι →L[ℂ] SumSpace (H:=H) ι :=
  (single ι i).comp (a.comp (PiLp.proj 2 (fun _ : ι => H) j))

omit [CompleteSpace H] [Fintype ι] in
@[simp] lemma position_apply (i j : ι) (a : H →L[ℂ] H) (v : SumSpace (H:=H) ι) :
    position ι i j a v=single ι i (a (v j)) := rfl

end Kadison.OperatorAmplification

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_TracialL2Tools
attribute [-instance] _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped ComplexOrder InnerProductSpace

namespace Kadison.TracialL2

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable (τ : A →ₚ[ℂ] ℂ)

@[simp] lemma norm_zero : norm τ 0=0 := by simp [norm]

end Kadison.TracialL2

end

end
end

end OAI
end


