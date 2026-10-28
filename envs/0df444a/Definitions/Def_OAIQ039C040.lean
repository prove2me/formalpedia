-- Prove2me | Definitions.Def_OAIQ039C040
-- name    : OAIQ039C040
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-28T09:10:50.701043+00:00
-- url     : https://prove2.me/theorems/b7e7e78a-0c5c-4665-96cc-34a52254b26a
-- title:
--   Definitions bundle OAIQ039C040 of the split of OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Kadison.uniform_commutator`, carved from OpenAI's openai/math development (OpenAI, *Kadison's similarity theorem through uniform derivation estimates (result family 288)*, OpenAI Math Release, September 23, 2026, result family 288, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 24 declarations of OpenAI's Lean: 11 definitions and 13 theorems. The definitions and types are `OAI.Kadison.NormalPredual.coefficient`, `OAI.Kadison.NormalPredual.finiteTests`, `OAI.Kadison.NormalRelativeCommutant.liftedUnitary`, `OAI.Kadison.OperatorAmplification.rangeRestriction`, `OAI.Kadison.PositiveWOT.strongFunctional`, `OAI.Kadison.PositiveWOT.threshold`, `OAI.Kadison.PreHilbert.reindexPower`, `OAI.Kadison.PreHilbert.stageWordArgs`, `OAI.Kadison.PreHilbert.wordReindex`, `OAI.Kadison.TracialGNS.fullSpace`, `OAI.Kadison.TracialGNS.stageSet`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis/Commutator, in whole or in part: `Commutator_CoefficientForm`, `Commutator_CyclePairTrace2`, `Commutator_EndpointGNS`, `Commutator_MatrixAlgebraEquiv`, `Commutator_NormalOperatorHom`, `Commutator_NormalPredual`, `Commutator_NormalRelativeCommutant`, `Commutator_PolarSupport`, `Commutator_ProjectionJoin`, `Commutator_ProjectionNormalBridge`, `Commutator_SpectralThreshold`, `Commutator_SquareZeroPolar`, `Commutator_StageDensity`, `Commutator_WordPermutations`, `Commutator_WordTopology`, `Commutator_WordTopology3`.
--
--   **Imports.** It imports the bundles `OAIQ039C022`, `OAIQ039C023`, `OAIQ039C024`, `OAIQ039C025`, `OAIQ039C026`, `OAIQ039C029` and `OAIQ039C030` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ039C049`, `OAIQ039C051` and `OAIQ039C052`; the statements `OAI.Kadison.NormalRelativeCommutant.commutes_of_fixed`, `OAI.Kadison.PositiveWOT.mem_predual`, `OAI.Kadison.PositiveWOT.threshold_exhaustion` and `OAI.Kadison.TracialGNS.word_multiplicity_both`; the proofs of `OAI.Kadison.IrreducibleTowerAveraging.scalar_mem_hull`, `OAI.Kadison.NormalRelativeCommutant.commutes_of_fixed`, `OAI.Kadison.OrbitStateHull.hull_norm_separable`, `OAI.Kadison.PositiveWOT.mem_predual`, `OAI.Kadison.PositiveWOT.positive_strong_null`, `OAI.Kadison.PositiveWOT.threshold_exhaustion`, `OAI.Kadison.PreHilbert.operator_ext_dense_stages`, `OAI.Kadison.TracialGNS.exists_corner_weak_zero` and `OAI.Kadison.TracialGNS.word_multiplicity_both`.
-- source:
--   OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 288; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Kadisons-similarity-theorem-through-uniform-derivation-estimates-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis/Commutator at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ039C022
import Definitions.Def_OAIQ039C023
import Definitions.Def_OAIQ039C024
import Definitions.Def_OAIQ039C025
import Definitions.Def_OAIQ039C026
import Definitions.Def_OAIQ039C029
import Definitions.Def_OAIQ039C030

section
-- module Solutions.OAIQ039_CM.Commutator_CoefficientForm
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

namespace Kadison.PreHilbert

open UniformSpace Function

lemma word_add_left (E F : PreHilbert) (n : ℕ) (d e : E) (x : Fin n → F) :
    word E F n (d + e) x = word E F n d x + word E F n e x := by
  simp only [word, TensorProduct.add_tmul, Completion.coe_add]

lemma word_smul_left (E F : PreHilbert) (n : ℕ) (c : ℂ) (d : E) (x : Fin n → F) :
    word E F n (c • d) x = c • word E F n d x := by
  simp only [word, ← TensorProduct.smul_tmul', Completion.coe_smul]

lemma word_update_add (E F : PreHilbert) (n : ℕ) (d : E) (v : Fin n → F)
    (i : Fin n) (x y : F) :
    word E F n d (update v i (x + y)) =
      word E F n d (update v i x) + word E F n d (update v i y) := by
  simp only [word, pure_update_add, TensorProduct.tmul_add, Completion.coe_add]

end Kadison.PreHilbert
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

omit [Fintype J] [LinearOrder J] in
@[simp] lemma endpointPairingPerm_some (σ : Pairing J) (j : J) :
    endpointPairingPerm σ (some j) = some (σ j) := rfl

end Kadison.SchurWeyl
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_EndpointGNS
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

namespace Kadison.TracialGNS

open PreHilbert

variable {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable (τ : A →ₚ[ℂ] ℂ) (hτ : ∀ a b : A, τ (a * b) = τ (b * a)) (h1 : τ 1 = 1)

abbrev fullSpace : PreHilbert := ⟨τ.GNS⟩

end Kadison.TracialGNS
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_PolarSupport
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.UnitaryDualAction.action _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
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

lemma leftSupport_mem (M : VonNeumannAlgebra H) {T : H →L[ℂ] H} (hT : T∈M) :
    leftSupport T∈M :=
  M.mul_mem (partialIsometry_mem_vonNeumann M hT) (M.star_mem' (partialIsometry_mem_vonNeumann M hT))

end Kadison.Polar

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_MatrixAlgebraEquiv
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

open scoped BigOperators InnerProductSpace

namespace Kadison.OperatorAmplification

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def rangeRestriction {B : Type*} [CStarAlgebra B]
    (P : VonNeumannAlgebra H) (φ : B →⋆ₐ[ℂ] (H →L[ℂ] H))
    (hφ : ∀ b,φ b∈P) : B →⋆ₐ[ℂ] P :=
  φ.codRestrict P.toStarSubalgebra hφ

end Kadison.OperatorAmplification

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_NormalOperatorHom
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.UnitaryDualAction.action
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

attribute [-instance] NonUnitalStarSubalgebra.nonUnitalCStarAlgebra

open scoped Topology

open Filter ContinuousLinearMapWOT

namespace Kadison.NormalOperatorHom

variable {H G : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]

variable (M : VonNeumannAlgebra H) (φ : M →⋆ₐ[ℂ] (G →L[ℂ] G))

lemma sourceBall_tendsto
    {ι : Type*} {l : Filter ι} (a : ι → M) (b : M) (C : ℝ)
    (ha : ∀ i,‖a i‖≤C) (hb : ‖b‖≤C)
    (hlim : ∀ x y,Tendsto (fun i => inner ℂ ((a i:H →L[ℂ] H) x) y) l
      (𝓝 (inner ℂ ((b:H →L[ℂ] H) x) y))) :
    Tendsto (fun i => (⟨ofCLM (a i),(a i).property,ha i⟩ :
      {T : H →WOT[ℂ] H // T.toCLM∈M ∧ ‖T.toCLM‖≤C})) l
      (𝓝 ⟨ofCLM b,b.property,hb⟩) := by
  apply tendsto_subtype_rng.mpr
  apply tendsto_iff_forall_inner_apply_tendsto.mpr
  intro u v
  simpa only [RCLike.star_def,inner_conj_symm,ofCLM_apply] using (hlim u v).star

end Kadison.NormalOperatorHom

end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_NormalPredual
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.UnitaryDualAction.action
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open Filter ContinuousLinearMapWOT

open scoped Topology InnerProductSpace

namespace Kadison.NormalPredual

open FiniteStrongTest

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def coefficient (M : VonNeumannAlgebra H) (v : ℕ → H) (N : ℕ)
    (y : PiLp 2 (fun _ : Fin N => H)) : StrongDual ℂ M :=
  (innerSL ℂ y).comp (testMap M v N)

def finiteTests (M : VonNeumannAlgebra H) (v : ℕ → H) : Set (StrongDual ℂ M) :=
  ⋃ N : ℕ,Set.range (coefficient M v N)

end Kadison.NormalPredual

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_NormalRelativeCommutant
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.UnitaryDualAction.action
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped InnerProductSpace ComplexOrder

namespace Kadison.NormalRelativeCommutant

open TracialGNS NormalGNS

variable {H D : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [CStarAlgebra D]

variable (M : VonNeumannAlgebra H) (τ : M →ₚ[ℂ] ℂ)
  (hτ : ∀ a b : M, τ (a*b)=τ (b*a)) (π : D →⋆ₐ[ℂ] M)

def liftedUnitary (u : unitary D) : unitary M := ⟨π (u:D), Unitary.map_mem π u.property⟩

end Kadison.NormalRelativeCommutant

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_SquareZeroPolar
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.UnitaryDualAction.action _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped ComplexOrder InnerProductSpace Topology

namespace Kadison.Polar

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma partialIsometry_square_zero (T : H →L[ℂ] H) (hT : T*T=0) :
    partialIsometry T*partialIsometry T=0 := by
  let K : Submodule ℂ H := LinearMap.ker T.toLinearMap
  let : CompleteSpace K := T.isClosed_ker.completeSpace_coe
  let e : H →L[ℂ] H := K.starProjection
  have he : IsStarProjection e := isStarProjection_starProjection
  have heT : e*T=T := by
    ext x
    apply Submodule.starProjection_eq_self_iff.mpr
    exact congrArg (fun R : H →L[ℂ] H => R x) hT
  have hTe : T*e=0 := by
    ext x
    exact K.starProjection_apply_mem x
  have hTcomp : T*(1-e)=T := by rw [mul_sub,mul_one,hTe,sub_zero]
  have hsource := rightSupport_le T (1-e) he.one_sub hTcomp
  have hes : e*partialIsometry T=partialIsometry T := mul_partialIsometry_of_mul T e heT
  have hP : (rightSupport T)*(1-e)=rightSupport T :=
    ((isProjection_rightSupport T).le_iff_mul_eq_left he.one_sub).mp hsource
  have hPe : rightSupport T*e=0 := by
    rw [mul_sub,mul_one] at hP
    exact sub_eq_self.mp hP
  have hse : partialIsometry T*e=0 := by
    calc
      _=(partialIsometry T*rightSupport T)*e := by rw [rightSupport,partialIsometry_mul_initial]
      _=0 := by rw [mul_assoc,hPe,mul_zero]
  calc
    _=partialIsometry T*(e*partialIsometry T) := by rw [hes]
    _=0 := by rw [←mul_assoc,hse,zero_mul]

end Kadison.Polar

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_ProjectionJoin
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.UnitaryDualAction.action
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped ComplexOrder InnerProductSpace

namespace Kadison.ProjectionJoin

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma remainder_projection (p q : H →L[ℂ] H) : IsStarProjection (remainder p q) :=
  Polar.isProjection_leftSupport _

lemma remainder_mem (M : VonNeumannAlgebra H) {p q : H →L[ℂ] H} (hp : p∈M) (hq : q∈M) :
    remainder p q∈M := Polar.leftSupport_mem M (M.mul_mem (M.sub_mem M.one_mem hp) hq)

open PartialIsometryOrder PartialIsometryOrder.DyadicPartition

end Kadison.ProjectionJoin

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_SpectralThreshold
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.UnitaryDualAction.action _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
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

def threshold (B : H →L[ℂ] H) (r : ℝ) : H →L[ℂ] H :=
  Polar.rightSupport (B-r • (1:H →L[ℂ] H))⁺

end Kadison.PositiveWOT

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_ProjectionNormalBridge
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.UnitaryDualAction.action
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open Filter

open scoped ComplexOrder Topology

namespace Kadison.PositiveWOT

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def strongFunctional (M : VonNeumannAlgebra H) (f : M →ₚ[ℂ] ℂ) : StrongDual ℂ M where
  toLinearMap := f.toLinearMap
  cont := map_continuous f

end Kadison.PositiveWOT

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

def stageSet (n : ℕ) : Set τ.GNS := Set.range (stageVector τ (φ n))

end Kadison.TracialGNS
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_WordPermutations
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

namespace Kadison.PreHilbert

open UniformSpace

open scoped TensorProduct

def reindexPower (F : PreHilbert) {k l : ℕ} (b : Fin k ≃ Fin l) :
    power F k ≃ₗᵢ[ℂ] power F l :=
  gramEquiv (pure F k) (fun x => pure F l (x ∘ b.symm)) (span_pure F k)
    (by
      have hr : Set.range (fun x => pure F l (x ∘ b.symm)) = Set.range (pure F l) := by
        ext z
        constructor
        · rintro ⟨x, rfl⟩; exact ⟨x ∘ b.symm, rfl⟩
        · rintro ⟨y, rfl⟩
          refine ⟨y ∘ b, ?_⟩
          exact congrArg (pure F l) (funext fun i => by simp)
      rw [hr, span_pure])
    (by
      intro x y
      simp only [inner_pure, Function.comp_apply]
      exact Equiv.prod_comp b.symm (fun i => inner ℂ (x i) (y i)))

@[simp] lemma reindexPower_pure (F : PreHilbert) {k l : ℕ} (b : Fin k ≃ Fin l)
    (x : Fin k → F) : reindexPower F b (pure F k x) = pure F l (x ∘ b.symm) :=
  gramEquiv_apply _ _ _ _ _ _

def wordReindex (E F : PreHilbert) {k l : ℕ} (b : Fin k ≃ Fin l) :
    wordSpace E F k →ₗᵢ[ℂ] wordSpace E F l :=
  completionIsometry (TensorProduct.mapIsometry (LinearIsometry.id : E →ₗᵢ[ℂ] E)
    (reindexPower F b).toLinearIsometry)

@[simp] lemma wordReindex_word (E F : PreHilbert) {k l : ℕ} (b : Fin k ≃ Fin l)
    (d : E) (x : Fin k → F) :
    wordReindex E F b (word E F k d x) = word E F l d (x ∘ b.symm) := by
  simp only [wordReindex, word, completionIsometry_coe, TensorProduct.mapIsometry_apply, TensorProduct.map_tmul,
    LinearIsometry.coe_toLinearMap, LinearIsometry.id_apply, LinearIsometryEquiv.coe_toLinearIsometry, reindexPower_pure]

end Kadison.PreHilbert
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_WordTopology
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

namespace Kadison.PreHilbert

open UniformSpace TensorProduct

@[fun_prop] lemma continuous_pure (E : PreHilbert) (n : ℕ) :
    Continuous (pure E n) := by
  induction n with
  | zero => exact continuous_const
  | succ n ih =>
    change Continuous (fun x : Fin (n+1) → E => x 0 ⊗ₜ[ℂ] pure E n (Fin.tail x))
    have ht : Continuous (fun x : Fin (n+1) → E => Fin.tail x) :=
      continuous_pi (fun i => continuous_apply i.succ)
    exact (TensorProduct.continuous_tmul (𝕜 := ℂ) (E := E) (F := power E n)).comp
      ((continuous_apply (0 : Fin (n+1))).prodMk (ih.comp ht))

@[fun_prop] lemma continuous_word (E F : PreHilbert) (n : ℕ) :
    Continuous (fun z : E × (Fin n → F) => word E F n z.1 z.2) := by
  unfold word
  exact (Completion.continuous_coe (E ⊗[ℂ] power F n)).comp
    ((TensorProduct.continuous_tmul (𝕜 := ℂ) (E := E) (F := power F n)).comp
    (continuous_fst.prodMk ((continuous_pure F n).comp continuous_snd)))

end Kadison.PreHilbert
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_WordTopology3
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

namespace Kadison.PreHilbert

def stageWordArgs (E F : PreHilbert) (S : ℕ → Set E) (R : ℕ → Set F)
    (j n : ℕ) : Set (E × (Fin j → F)) := S n ×ˢ Set.pi Set.univ (fun _ => R n)

end Kadison.PreHilbert
end

end OAI
end


