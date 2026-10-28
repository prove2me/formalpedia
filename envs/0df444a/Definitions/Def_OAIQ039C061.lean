-- Prove2me | Definitions.Def_OAIQ039C061
-- name    : OAIQ039C061
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-28T09:17:00.899721+00:00
-- url     : https://prove2.me/theorems/ad429d49-078a-4152-b507-b20b730a6c1d
-- title:
--   Definitions bundle OAIQ039C061 of the split of OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Kadison.uniform_commutator`, carved from OpenAI's openai/math development (OpenAI, *Kadison's similarity theorem through uniform derivation estimates (result family 288)*, OpenAI Math Release, September 23, 2026, result family 288, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 15 declarations of OpenAI's Lean: 6 definitions, 1 instance and 8 theorems. The definitions and types are `OAI.Kadison.MatrixGNS.algebraArray`, `OAI.Kadison.MatrixGNS.trace`, `OAI.Kadison.MatrixGNS.unitary`, `OAI.Kadison.MatrixGNS.vacuum`, `OAI.Kadison.MatrixTower.finiteStandardAlgebra`, `OAI.Kadison.NormalGNS.representedStages`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis/Commutator, in whole or in part: `Commutator_FiniteStandardGauge`, `Commutator_InvariantSum`, `Commutator_MatrixGNSUnitary`, `Commutator_MatrixStageGNSGeneration`, `Commutator_MatrixTowerInclusion`, `Commutator_MatrixVectorTrace`, `Commutator_NormalTraceProjection`.
--
--   **Imports.** It imports the bundles `OAIQ039C054`, `OAIQ039C056` and `OAIQ039C057` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ039C066`, `OAIQ039C067` and `OAIQ039C068`; the statements `OAI.Kadison.GeneratedMatrixBicommutant.in_represented`, `OAI.Kadison.MatrixGNS.flatBalancedUnitary_trace`, `OAI.Kadison.MatrixGNS.rowMatrix_trace`, `OAI.Kadison.MatrixGNS.trace_mul`, `OAI.Kadison.MatrixGNS.trace_one`, `OAI.Kadison.MatrixTower.finiteStandard_range`, `OAI.Kadison.MatrixTower.finite_standard_bound`, `OAI.Kadison.NormalGNS.matrix_stages_gns` and `OAI.Kadison.VectorGNS.generatedByStages_of_represented`; the proofs of `OAI.Kadison.CentralSpectral.exists_stable_center_spectral_model`, `OAI.Kadison.GeneratedMatrixBicommutant.in_represented`, `OAI.Kadison.MatrixGNS.flatBalancedUnitary_trace`, `OAI.Kadison.MatrixGNS.rowMatrix_trace`, `OAI.Kadison.MatrixGNS.trace_mul`, `OAI.Kadison.MatrixGNS.trace_one`, `OAI.Kadison.MatrixTower.finiteStandard_range`, `OAI.Kadison.NormalGNS.matrix_stages_gns`, `OAI.Kadison.NormalRepresentation.finite_standard_compression_bound` and `OAI.Kadison.VectorGNS.generatedByStages_of_represented`.
-- source:
--   OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 288; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Kadisons-similarity-theorem-through-uniform-derivation-estimates-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis/Commutator at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ039C054
import Definitions.Def_OAIQ039C056
import Definitions.Def_OAIQ039C057

section
-- module Solutions.OAIQ039_CM.Commutator_NormalTraceProjection
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.UnitaryDualAction.action
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped ComplexOrder InnerProductSpace Topology BigOperators

namespace Kadison.NormalGNS

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (M : VonNeumannAlgebra H) (τ : M →ₚ[ℂ] ℂ)

variable (hτ : ∀ a b : M, τ (a*b)=τ (b*a)) (hnormal : BoundedWOTContinuous M τ)

variable (hfaith : ∀ a : M, τ (star a*a)=0 → a=0)

include hfaith in
lemma projection_zero_of_trace_re_zero (e : M) (he : IsStarProjection e)
    (ht : (τ e).re=0) : e=0 := by
  apply hfaith
  rw [he.isSelfAdjoint.star_eq,he.isIdempotentElem.eq]
  have hn := τ.map_nonneg he.nonneg
  exact Complex.ext ht hn.2.symm

end Kadison.NormalGNS

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_MatrixVectorTrace
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.UnitaryDualAction.action _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped BigOperators InnerProductSpace ComplexOrder

open ContinuousLinearMap

namespace Kadison.MatrixGNS

variable {A ι : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [Fintype ι]

attribute [local instance] OAI.Kadison.MatrixGNS.matrixVectorTraceDecidableEq
variable (τ : A →ₚ[ℂ] ℂ)

def algebraArray (X : CStarMatrix ι ι A) : ArraySpace (ι:=ι) τ :=
  WithLp.toLp 2 (fun i => WithLp.toLp 2 (fun j => TracialGNS.algebraVector τ (X i j)))

omit [Fintype ι] in
@[simp] lemma algebraArray_apply (X : CStarMatrix ι ι A) (i j : ι) :
    algebraArray τ X i j=TracialGNS.algebraVector τ (X i j) := rfl

lemma representation_oneArray (X : CStarMatrix ι ι A) :
    representation τ X (algebraArray τ 1)=algebraArray τ X := by
  ext i j
  simp only [representation_apply,algebraArray_apply,CStarMatrix.one_apply]
  classical
  simp [apply_ite,TracialGNS.algebraVector,map_zero]

def vacuum : ArraySpace (ι:=ι) τ := scale ι • algebraArray τ 1

lemma representation_vacuum (X : CStarMatrix ι ι A) :
    representation τ X (vacuum (ι:=ι) τ)=scale ι • algebraArray τ X := by
  rw [vacuum,map_smul,representation_oneArray]

def trace : CStarMatrix ι ι A →ₚ[ℂ] ℂ where
  toLinearMap := (VectorFunctional.functional (vacuum (ι:=ι) τ)).toLinearMap.comp
    (representation τ).toLinearMap
  monotone' := by
    have hmono : Monotone (representation (ι:=ι) τ) := by
      intro first second hle
      exact (OAI.nonUnitalStarRingHomOfClass (representation (ι:=ι) τ)).map_le_map_of_map_star hle
    exact (VectorFunctional.functional (vacuum (ι:=ι) τ)).monotone.comp hmono

lemma trace_vector (X : CStarMatrix ι ι A) :
    trace (ι:=ι) τ X=inner ℂ (vacuum τ) (representation τ X (vacuum τ)) := rfl

end Kadison.MatrixGNS

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_MatrixGNSUnitary
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.UnitaryDualAction.action _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped BigOperators InnerProductSpace ComplexOrder

namespace Kadison.MatrixGNS

variable {A ι : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [Fintype ι]

attribute [local instance] OAI.Kadison.MatrixGNS.matrixGNSUnitaryDecidableEq
variable (τ : A →ₚ[ℂ] ℂ)

omit [Fintype ι] in
lemma dense_algebraArray : DenseRange (algebraArray (ι:=ι) τ) := by
  have hd₁ : DenseRange (fun a : ι → A =>
      WithLp.toLp 2 (fun i => TracialGNS.algebraVector τ (a i))) := by
    let e := (PiLp.continuousLinearEquiv 2 ℂ (fun _ : ι => τ.GNS)).symm
    exact e.surjective.denseRange.comp
      (DenseRange.piMap (fun _ : ι => TracialGNS.algebraVector_dense τ)) e.continuous
  have hd₂ : DenseRange (fun a : ι → ι → A =>
      WithLp.toLp 2 (fun i => WithLp.toLp 2
        (fun j => TracialGNS.algebraVector τ (a i j)))) := by
    let e := (PiLp.continuousLinearEquiv 2 ℂ (fun _ : ι => PiLp 2 (fun _ : ι => τ.GNS))).symm
    exact e.surjective.denseRange.comp (DenseRange.piMap (fun _ : ι => hd₁)) e.continuous
  apply hd₂.mono
  rintro y ⟨a,rfl⟩
  exact ⟨CStarMatrix.ofMatrix a,rfl⟩

lemma dense_vacuumOrbit [Nonempty ι] :
    DenseRange (fun X : CStarMatrix ι ι A => representation (ι:=ι) τ X (vacuum (ι:=ι) τ)) := by
  have hs : Function.Surjective (fun v : ArraySpace (ι:=ι) τ => scale ι • v) := by
    intro v
    exact ⟨(scale ι)⁻¹ • v,by simp only [smul_smul,mul_inv_cancel₀ (scale_ne_zero (ι:=ι)),one_smul]⟩
  have hd := hs.denseRange.comp (dense_algebraArray (ι:=ι) τ)
    (continuous_const_smul (scale ι))
  apply hd.mono
  rintro y ⟨X,rfl⟩
  exact ⟨X,representation_vacuum τ X⟩

noncomputable def unitary [Nonempty ι] :=
  VectorGNS.equivalence (A:=CStarMatrix ι ι A) (H:=ArraySpace (ι:=ι) τ)
    (trace (ι:=ι) τ) (representation (ι:=ι) τ) (vacuum (ι:=ι) τ)
    (trace_vector (ι:=ι) τ) (dense_vacuumOrbit (ι:=ι) τ)

end Kadison.MatrixGNS

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_InvariantSum
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
open scoped InnerProductSpace TensorProduct ComplexOrder
open UniformSpace
open scoped InnerProductSpace _root_.Topology
open scoped TensorProduct
open UniformSpace
open scoped TensorProduct InnerProductSpace
open scoped InnerProductSpace ENNReal
open ContinuousLinearMap
open scoped InnerProductSpace ENNReal
open scoped ComplexOrder InnerProductSpace TensorProduct
open UniformSpace ContinuousLinearMap

namespace Kadison.TracialGNS

open PreHilbert HilbertTensor

variable {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable (τ : A →ₚ[ℂ] ℂ) (hτ : ∀ a b : A, τ (a*b)=τ (b*a)) (h1 : τ 1=1)

variable (J : ℕ → Type*) [∀ k, NormedAddCommGroup (J k)]
  [∀ k, InnerProductSpace ℂ (J k)] [∀ k, CompleteSpace (J k)]

instance sumLevelNormed (k : ℕ) : NormedAddCommGroup (sumLevel τ J k) :=
  inferInstanceAs (NormedAddCommGroup (Completion (wordSpace (fullSpace τ) (zeroSpace τ) k ⊗[ℂ] J k)))

end Kadison.TracialGNS
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_MatrixStageGNSGeneration
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

open scoped ComplexOrder Matrix.Norms.L2Operator

namespace Kadison.NormalGNS

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (M : VonNeumannAlgebra H) (τ : M →ₚ[ℂ] ℂ)
  (hnormal : BoundedWOTContinuous M τ)
  (I : ℕ → Type*) [∀ n,Fintype (I n)] [∀ n,DecidableEq (I n)]
  (φ : ∀ n,Matrix (I n) (I n) ℂ →⋆ₐ[ℂ] M)

def representedStages : StarSubalgebra ℂ (H →L[ℂ] H) :=
  iSup fun n => (M.toStarSubalgebra.subtype.comp (φ n)).range

end Kadison.NormalGNS

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_FiniteStandardGauge
attribute [-instance] _root_.OAI.Kadison.UnitaryDualAction.action
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

attribute [-instance] NonUnitalStarSubalgebra.nonUnitalCStarAlgebra

open scoped InnerProductSpace ComplexOrder Matrix.Norms.L2Operator

open Filter

namespace Kadison.MatrixTower

open OperatorAmplification TracialSequence CyclicColumns HilbertPadding

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (ι κ : Type) [Fintype ι] [Nonempty ι] [Fintype κ] [Nonempty κ] (k₀ : κ)

local instance finiteStandardGaugeIndexDecidableEq_r28f465_1 : DecidableEq ι := Classical.decEq ι
attribute [local instance] OAI.Kadison.MatrixTower.finiteStandardGaugeColumnDecidableEq
local instance finiteStandardGaugeSumDecidableEq_r28f465_1 : DecidableEq (κ⊕ι) := Classical.decEq _
attribute [local instance] OAI.Kadison.MatrixTower.finiteStandardGaugeDoubledSumDecidableEq
variable (M : VonNeumannAlgebra H) [Nontrivial M] (E : ℕ → Stage M)

variable (τ : M →ₚ[ℂ] ℂ) (hnormal : NormalGNS.BoundedWOTContinuous M τ)

variable (ω : Ultrafilter ℕ) (hω : (ω : Filter ℕ) ≤ atTop)

def finiteStandardAlgebra : VonNeumannAlgebra (SumSpace (H:=τ.GNS) ι) :=
  NormalGNS.bicommutant (((diagonal (H:=τ.GNS) ι).comp τ.gnsStarAlgHom).range)

end Kadison.MatrixTower

end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_MatrixTowerInclusion
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.UnitaryDualAction.action
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped ComplexOrder

namespace Kadison.MatrixTower

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (M : VonNeumannAlgebra H) (F : ℕ → Stage M)

variable [Nontrivial M] (hF : Monotone (fun n => (F n).hom.range))

lemma stage_injective (n : ℕ) : Function.Injective (F n).hom :=
  (F n).hom.toAlgHom.toRingHom.injective

end Kadison.MatrixTower

end

end
end

end OAI
end


