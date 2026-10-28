-- Prove2me | Definitions.Def_OAIQ039C052
-- name    : OAIQ039C052
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-28T09:12:04.841768+00:00
-- url     : https://prove2.me/theorems/3dd506eb-d54d-44e5-83c9-993f78e6e938
-- title:
--   Definitions bundle OAIQ039C052 of the split of OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Kadison.uniform_commutator`, carved from OpenAI's openai/math development (OpenAI, *Kadison's similarity theorem through uniform derivation estimates (result family 288)*, OpenAI Math Release, September 23, 2026, result family 288, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 25 declarations of OpenAI's Lean: 14 definitions and 11 theorems. The definitions and types are `OAI.Kadison.ProjectionLifts.halfCut`, `OAI.Kadison.ProjectionLifts.roundedSequence`, `OAI.Kadison.SchurWeyl.endpointPairingCycleEquiv`, `OAI.Kadison.SchurWeyl.endpointPairingEquiv`, `OAI.Kadison.SchurWeyl.optionPairRepresentative`, `OAI.Kadison.SchurWeyl.pairingOfEndpointPerm`, `OAI.Kadison.TraceEquivGNS.unitary`, `OAI.Kadison.TracialGNS.centeredStageSet`, `OAI.Kadison.TracialGNS.centeredStageVector`, `OAI.Kadison.TracialGNS.rightStarAlgHom`, `OAI.Kadison.TracialSequence.boundedUnitary`, `OAI.Kadison.TracialSequence.rightFamily`, `OAI.Kadison.VectorGNS.subalgebraCompression`, `OAI.Kadison.coefficientMultilinear`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis/Commutator, in whole or in part: `Commutator_CoefficientForm2`, `Commutator_CyclePairTrace2`, `Commutator_CyclePairTrace3`, `Commutator_MatrixGNS`, `Commutator_ProjectionLifts`, `Commutator_StageDensity`, `Commutator_TraceEquivGNS`, `Commutator_TracialDevelopment`, `Commutator_TracialSequenceRight`, `Commutator_TracialVectorSubalgebra`, `Commutator_UnitarySequence`.
--
--   **Imports.** It imports the bundles `OAIQ039C032`, `OAIQ039C035`, `OAIQ039C037`, `OAIQ039C038`, `OAIQ039C039`, `OAIQ039C040` and `OAIQ039C041` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ039C058`, `OAIQ039C064` and `OAIQ039C065`; the statement `OAI.Kadison.TracialGNS.normalizedLetter_orthonormal`; the proofs of `OAI.Kadison.SchurWeyl.centered_expansion_contractions` and `OAI.Kadison.TracialGNS.normalizedLetter_orthonormal`.
-- source:
--   OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 288; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Kadisons-similarity-theorem-through-uniform-derivation-estimates-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis/Commutator at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ039C032
import Definitions.Def_OAIQ039C035
import Definitions.Def_OAIQ039C037
import Definitions.Def_OAIQ039C038
import Definitions.Def_OAIQ039C039
import Definitions.Def_OAIQ039C040
import Definitions.Def_OAIQ039C041

section
-- module Solutions.OAIQ039_CM.Commutator_CoefficientForm2
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.UnitaryDualAction.action _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
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

namespace Kadison

open PreHilbert Function

variable (E F : PreHilbert) (k l : ℕ)

variable {M : Type*} [AddCommGroup M] [Module ℂ M] [StarAddMonoid M] [StarModule ℂ M]

variable [DecidableEq (Option (Fin k ⊕ Fin l))]

omit [StarModule ℂ M] in
lemma coefficient_update_none_add
    (Y : wordSpace E F k →L[ℂ] wordSpace E F l) (Ω : E)
    (v₀ : M →ₗ[ℂ] E) (v₁ : M →ₗ[ℂ] F) (A : Option (Fin k ⊕ Fin l) → M) (x y : M) :
    coefficient E F k l Y Ω v₀ v₁ (update A none (x+y)) =
      coefficient E F k l Y Ω v₀ v₁ (update A none x) +
      coefficient E F k l Y Ω v₀ v₁ (update A none y) := by
  simp only [coefficient, update_self, update_of_ne (Option.some_ne_none _),
    star_add, map_add, word_add_left, inner_add_left]

lemma coefficient_update_none_smul
    (Y : wordSpace E F k →L[ℂ] wordSpace E F l) (Ω : E)
    (v₀ : M →ₗ[ℂ] E) (v₁ : M →ₗ[ℂ] F) (A : Option (Fin k ⊕ Fin l) → M) (c : ℂ) (x : M) :
    coefficient E F k l Y Ω v₀ v₁ (update A none (c • x)) =
      c • coefficient E F k l Y Ω v₀ v₁ (update A none x) := by
  simp only [coefficient, update_self, update_of_ne (Option.some_ne_none _),
    star_smul, map_smul, word_smul_left, inner_smul_left]
  simp

def coefficientMultilinear
    (Y : wordSpace E F k →L[ℂ] wordSpace E F l) (Ω : E)
    (v₀ : M →ₗ[ℂ] E) (v₁ : M →ₗ[ℂ] F) :
    MultilinearMap ℂ (fun _ : Option (Fin k ⊕ Fin l) => M) ℂ where
  toFun := coefficient E F k l Y Ω v₀ v₁
  map_update_add' := by
    intro inst A i x y
    cases i with
    | none => exact coefficient_update_none_add E F k l Y Ω v₀ v₁ A x y
    | some i =>
      cases i with
      | inl i =>
        simp only [coefficient_update_inl, map_add, word_update_add, inner_add_right]
      | inr j =>
        simp only [coefficient_update_inr, star_add, map_add, word_update_add, inner_add_left]
  map_update_smul' := by
    intro inst A i c x
    cases i with
    | none => exact coefficient_update_none_smul E F k l Y Ω v₀ v₁ A c x
    | some i =>
      cases i with
      | inl i =>
        simp only [coefficient_update_inl, map_smul, word_update_smul, inner_smul_right,
          smul_eq_mul]
      | inr j =>
        simp only [coefficient_update_inr, star_smul, map_smul, word_update_smul,
          inner_smul_left, starRingEnd_apply, star_star, smul_eq_mul]

end Kadison
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_CyclePairTrace2
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.UnitaryDualAction.action _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
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

def optionPairRepresentative (σ : Pairing J) : Option J → Option (Pairing.Representatives σ)
  | none => none
  | some j => some ⟨Pairing.repr σ j, Pairing.repr_lt_apply σ j⟩

omit [Fintype J] in
lemma optionPairRepresentative_apply (σ : Pairing J) (j : Option J) :
    optionPairRepresentative σ (endpointPairingPerm σ j) = optionPairRepresentative σ j := by
  cases j with
  | none => rfl
  | some j => simp only [endpointPairingPerm_some, optionPairRepresentative,
      Pairing.repr_apply]

def endpointPairingCycleEquiv (σ : Pairing J) :
    cycleSet (endpointPairingPerm σ) ≃ Option (Pairing.Representatives σ) where
  toFun := Quotient.lift (optionPairRepresentative σ)
    (fun _ _ h => constant_on_cycle (endpointPairingPerm σ)
      (optionPairRepresentative σ) (optionPairRepresentative_apply σ) h)
  invFun
    | none => cycleMap (endpointPairingPerm σ) none
    | some r => cycleMap (endpointPairingPerm σ) (some r.1)
  left_inv q := by
    refine Quotient.inductionOn q (fun j => ?_)
    cases j with
    | none => rfl
    | some j =>
      change cycleMap (endpointPairingPerm σ) (some (Pairing.repr σ j)) =
        cycleMap (endpointPairingPerm σ) (some j)
      rcases le_total j (σ j) with h | h
      · rw [Pairing.repr, min_eq_left h]
      · rw [Pairing.repr, min_eq_right h]
        exact cycleMap_apply (endpointPairingPerm σ) (some j)
  right_inv r := by
    cases r with
    | none => rfl
    | some r =>
      change some (⟨Pairing.repr σ r, _⟩ : Pairing.Representatives σ) = some r
      congr 1
      apply Subtype.ext
      exact Pairing.repr_representative σ r

end Kadison.SchurWeyl
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_CyclePairTrace3
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.UnitaryDualAction.action _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
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

variable {J : Type*}

def pairingOfEndpointPerm (σ : Equiv.Perm (Option J)) (hσ : IsEndpointPairing σ) : Pairing J :=
  ⟨σ.removeNone, (by
    constructor
    · intro j
      apply Option.some_injective
      rw [some_removeNone_of_fixed σ hσ.1, some_removeNone_of_fixed σ hσ.1]
      exact hσ.2.1 (some j)
    · intro j hj
      have hh : σ (some j) = some j := by
        rw [← some_removeNone_of_fixed σ hσ.1, hj]
      exact Option.some_ne_none j (hσ.2.2 (some j) hh))⟩

def endpointPairingEquiv : Pairing J ≃ {σ : Equiv.Perm (Option J) // IsEndpointPairing σ} where
  toFun τ := ⟨endpointPairingPerm τ, (by
    refine ⟨rfl, ?_, ?_⟩
    · intro j
      cases j with
      | none => rfl
      | some j => simp only [endpointPairingPerm_some, Pairing.apply_apply]
    · intro j hj
      cases j with
      | none => rfl
      | some j =>
        have hh : τ j = j := Option.some.inj hj
        exact (τ.apply_ne j hh).elim)⟩
  invFun σ := pairingOfEndpointPerm σ.1 σ.2
  left_inv τ := by
    apply Subtype.ext
    exact Equiv.removeNone_optionCongr τ.val
  right_inv σ := by
    apply Subtype.ext
    apply Equiv.ext
    intro j
    cases j with
    | none => exact σ.2.1.symm
    | some j => exact some_removeNone_of_fixed σ.1 σ.2.1 j

end Kadison.SchurWeyl
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_TracialDevelopment
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.UnitaryDualAction.action _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ComplexOrder InnerProductSpace
open Complex ContinuousLinearMap UniformSpace Completion

namespace Kadison

namespace TracialGNS

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable (τ : A →ₚ[ℂ] ℂ) (hτ : ∀ a b : A, τ (a * b) = τ (b * a))

noncomputable def rightStarAlgHom : Aᵐᵒᵖ →⋆ₐ[ℂ] (τ.GNS →L[ℂ] τ.GNS) where
  toFun a := rightMul τ hτ a.unop
  map_one' := rightMul_one τ hτ
  map_zero' := by
    ext x
    induction x using Completion.induction_on with
    | hp => apply isClosed_eq <;> fun_prop
    | ih x => simp [Completion.coe_zero]
  map_add' a b := by
    ext x
    induction x using Completion.induction_on with
    | hp => apply isClosed_eq <;> fun_prop
    | ih x => simp [mul_add, Completion.coe_add]
  map_mul' a b := rightMul_mul τ hτ b.unop a.unop
  commutes' c := by
    ext x
    induction x using Completion.induction_on with
    | hp => apply isClosed_eq <;> fun_prop
    | ih x => simp [Algebra.algebraMap_eq_smul_one, Completion.coe_smul]
  map_star' a := rightMul_star τ hτ a.unop

lemma rightMul_opNorm_le (a : A) : ‖rightMul τ hτ a‖ ≤ ‖a‖ := by
  exact NonUnitalStarAlgHom.norm_apply_le (rightStarAlgHom τ hτ) (MulOpposite.op a)

end TracialGNS

end Kadison
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_MatrixGNS
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.UnitaryDualAction.action _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ComplexOrder InnerProductSpace
open Complex ContinuousLinearMap UniformSpace Completion
open scoped InnerProductSpace

namespace Kadison.TracialGNS

open Matrix

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable (τ : A →ₚ[ℂ] ℂ) (hτ : ∀ a b : A, τ (a * b) = τ (b * a)) (h1 : τ 1 = 1)

variable {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]

variable (φ : Matrix I I ℂ →⋆ₐ[ℂ] A)

noncomputable def centeredStageVector : Matrix I I ℂ →ₗ[ℂ] centeredSpace (vacuum τ) :=
  (center (vacuum τ)).toLinearMap.comp (stageVector τ φ)

end Kadison.TracialGNS
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_ProjectionLifts
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.UnitaryDualAction.action
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

attribute [-instance] NonUnitalStarSubalgebra.nonUnitalCStarAlgebra

open scoped BoundedContinuousFunction ComplexOrder

namespace Kadison.ProjectionLifts

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (M : VonNeumannAlgebra H)

def halfCut (a : M) : M := ⟨Polar.halfCut (a : H →L[ℂ] H),Polar.halfCut_mem M a.property⟩

lemma isProjection_halfCut (a : M) : IsStarProjection (halfCut M a) := by
  constructor
  · apply Subtype.ext
    exact (Polar.isProjection_halfCut (a : H →L[ℂ] H)).isIdempotentElem.eq
  · apply Subtype.ext
    exact (Polar.isProjection_halfCut (a : H →L[ℂ] H)).isSelfAdjoint.star_eq

variable {ι : Type*} [TopologicalSpace ι] [DiscreteTopology ι]

def roundedSequence (c : ι →ᵇ M) : ι →ᵇ M :=
  BoundedContinuousFunction.ofNormedAddCommGroupDiscrete (fun i => halfCut M (c i)) 1
    (fun i => (isProjection_halfCut M (c i)).norm_le _)

@[simp] lemma roundedSequence_apply (c : ι →ᵇ M) (i : ι) :
    roundedSequence M c i=halfCut M (c i) := rfl

end Kadison.ProjectionLifts

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_StageDensity
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.UnitaryDualAction.action _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
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

namespace Kadison.TracialGNS

open Matrix

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable (τ : A →ₚ[ℂ] ℂ) (hτ : ∀ a b : A, τ (a*b) = τ (b*a)) (h1 : τ 1 = 1)

variable {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]

variable (I : ℕ → Type*) [∀ n, Fintype (I n)] [∀ n, DecidableEq (I n)]
  [∀ n, Nonempty (I n)]

variable (φ : ∀ n, Matrix (I n) (I n) ℂ →⋆ₐ[ℂ] A)

def centeredStageSet (n : ℕ) : Set (centeredSpace (vacuum τ)) :=
  {x | ∃ a : Matrix (I n) (I n) ℂ, a.trace = 0 ∧ centeredStageVector τ (φ n) a = x}

end Kadison.TracialGNS
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_TraceEquivGNS
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.UnitaryDualAction.action _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped ComplexOrder InnerProductSpace

namespace Kadison.TraceEquivGNS

open TracialGNS

variable {A B : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

variable (e : A ≃⋆ₐ[ℂ] B) (τ : A →ₚ[ℂ] ℂ) (σ : B →ₚ[ℂ] ℂ)
  (htrace : ∀ a,σ (e a)=τ a)

omit [StarOrderedRing A] in
include htrace in
lemma vector_trace (a : A) : τ a=inner ℂ (vacuum σ)
    ((σ.gnsStarAlgHom.comp e.toStarAlgHom) a (vacuum σ)) := by
  rw [←htrace a]
  change σ (e a)=inner ℂ (algebraVector σ 1) (σ.gnsStarAlgHom (e a) (vacuum σ))
  rw [left_vacuum,←algebraVector_apply,inner_algebraVector,star_one,one_mul]

omit [PartialOrder A] [StarOrderedRing A] in
lemma dense_orbit : DenseRange (fun a : A => (σ.gnsStarAlgHom.comp e.toStarAlgHom) a (vacuum σ)) := by
  apply (dense_cyclic_orbit σ).mono
  rintro y ⟨b,rfl⟩
  exact ⟨e.symm b,by simp⟩

def unitary : τ.GNS ≃ₗᵢ[ℂ] σ.GNS :=
  VectorGNS.equivalence τ (σ.gnsStarAlgHom.comp e.toStarAlgHom) (vacuum σ)
    (vector_trace e τ σ htrace) (dense_orbit e σ)

end Kadison.TraceEquivGNS

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_TracialSequenceRight
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.UnitaryDualAction.action _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped Topology InnerProductSpace BoundedContinuousFunction ComplexOrder

open Filter UniformSpace Completion

namespace Kadison.TracialSequence

open TracialGNS HilbertSequence

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable (τ : A →ₚ[ℂ] ℂ) (ω : Ultrafilter ℕ)

variable (hτ : ∀ a b : A, τ (a*b)=τ (b*a))

def rightFamily (a : ℕ →ᵇ A) : ℕ →ᵇ (τ.GNS →L[ℂ] τ.GNS) :=
  BoundedContinuousFunction.mkOfDiscrete (fun i => rightMul τ hτ (a i)) (2*‖a‖)
    (fun i j => (dist_le_norm_add_norm _ _).trans (by
      have hi := (rightMul_opNorm_le τ hτ (a i)).trans (a.norm_coe_le_norm i)
      have hj := (rightMul_opNorm_le τ hτ (a j)).trans (a.norm_coe_le_norm j)
      linarith))

@[simp] lemma rightFamily_apply (a : ℕ →ᵇ A) (i : ℕ) :
    rightFamily τ hτ a i=rightMul τ hτ (a i) := rfl

end Kadison.TracialSequence

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_TracialVectorSubalgebra
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.UnitaryDualAction.action
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

attribute [-instance] NonUnitalStarSubalgebra.nonUnitalCStarAlgebra

open scoped InnerProductSpace ComplexOrder

namespace Kadison.VectorGNS

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma subalgebraTrace_subtype (M : VonNeumannAlgebra H) (ξ : H) (a : M) :
    subalgebraTrace M ξ a=inner ℂ ξ (M.toStarSubalgebra.subtype a ξ) := rfl

abbrev subalgebraCompression (M : VonNeumannAlgebra H) (ξ : H) (T : H →L[ℂ] H) :
    (subalgebraTrace M ξ).GNS →L[ℂ] (subalgebraTrace M ξ).GNS :=
  compression (subalgebraTrace M ξ) M.toStarSubalgebra.subtype ξ
    (subalgebraTrace_subtype M ξ) T

end Kadison.VectorGNS

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_UnitarySequence
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.UnitaryDualAction.action
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

attribute [-instance] NonUnitalStarSubalgebra.nonUnitalCStarAlgebra

open scoped ComplexOrder Topology BoundedContinuousFunction

open Filter

namespace Kadison.TracialSequence

open FinitePatching FinitePatching.Words

variable {A : Type} [CStarAlgebra A]

def boundedUnitary (u : ℕ → unitary A) : unitary (ℕ →ᵇ A) :=
  ⟨BoundedContinuousFunction.ofNormedAddCommGroupDiscrete (fun n => (u n:A)) 1
    (fun n => (PartialUnitary.ofUnitary (u n)).norm_le_one),by
    constructor <;> ext n
    · exact (u n).property.1
    · exact (u n).property.2⟩

@[simp] lemma boundedUnitary_apply (u : ℕ → unitary A) (n : ℕ) :
    ((boundedUnitary u : ℕ →ᵇ A) n)=(u n:A) := rfl

end Kadison.TracialSequence

end

end OAI
end


