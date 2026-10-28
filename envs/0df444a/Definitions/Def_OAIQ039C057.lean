-- Prove2me | Definitions.Def_OAIQ039C057
-- name    : OAIQ039C057
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-28T09:13:59.540792+00:00
-- url     : https://prove2.me/theorems/bfa25184-00f5-4013-ac76-081fa332c897
-- title:
--   Definitions bundle OAIQ039C057 of the split of OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Kadison.uniform_commutator`, carved from OpenAI's openai/math development (OpenAI, *Kadison's similarity theorem through uniform derivation estimates (result family 288)*, OpenAI Math Release, September 23, 2026, result family 288, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 8 declarations of OpenAI's Lean: 3 definitions and 5 theorems. The definitions and types are `OAI.Kadison.MatrixCornerImplementation.cornerEmbedding`, `OAI.Kadison.OperatorAmplification.matrixHom`, `OAI.Kadison.TracialGNS.sumLevel`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis/Commutator, in whole or in part: `Commutator_CornerCyclicImplementation`, `Commutator_CountableProjectionJoin`, `Commutator_InvariantSum`, `Commutator_MatrixAlgebraEquiv`, `Commutator_NormalBiprodGNS`, `Commutator_ProjectionJoin`.
--
--   **Imports.** It imports the bundles `OAIQ039C042`, `OAIQ039C048`, `OAIQ039C049`, `OAIQ039C050` and `OAIQ039C051` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ039C059`, `OAIQ039C061`, `OAIQ039C062` and `OAIQ039C063`; the statement `OAI.Kadison.MatrixCornerImplementation.cornerEmbedding_intertwines`; the proofs of `OAI.Kadison.MatrixCornerImplementation.cornerEmbedding_intertwines`, `OAI.Kadison.MatrixCornerImplementation.exists_matrix_corner_intertwiner` and `OAI.Kadison.ProjectionJoin.dimension_finiteJoin_le`.
-- source:
--   OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 288; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Kadisons-similarity-theorem-through-uniform-derivation-estimates-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis/Commutator at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ039C042
import Definitions.Def_OAIQ039C048
import Definitions.Def_OAIQ039C049
import Definitions.Def_OAIQ039C050
import Definitions.Def_OAIQ039C051

section
-- module Solutions.OAIQ039_CM.Commutator_CornerCyclicImplementation
attribute [-instance] _root_.OAI.Kadison.UnitaryDualAction.action _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped InnerProductSpace

open ContinuousLinearMap

namespace Kadison.MatrixCornerImplementation

open MatrixCornerHilbert ReducingRepresentation ConcreteCorner MatrixCornerExtension

variable {H K ι : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  [Fintype ι] [DecidableEq ι]

variable (M : VonNeumannAlgebra H)
  (σ : Algebra M →⋆ₐ[ℂ] (K →L[ℂ] K)) (j : K →ₗᵢ[ℂ] H)
  (hj : ∀ a x, j (σ a x)=inclusion M a (j x))

variable {p : Algebra M} (hp : IsStarProjection p)

def cornerEmbedding : fixedSpace (σ p) →ₗᵢ[ℂ] Space hp where
  toFun x := ⟨j (x:K),by
    rw [mem_fixedSpace,←hj,MatrixCornerHilbert.fixed_apply]⟩
  map_add' x y := Subtype.ext (map_add j (x:K) (y:K))
  map_smul' z x := Subtype.ext (map_smul j z (x:K))
  norm_map' x := j.norm_map (x:K)

end Kadison.MatrixCornerImplementation

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

lemma left_le {p : H →L[ℂ] H} (hp : IsStarProjection p) (q : H →L[ℂ] H) : p≤join p q := by
  apply (hp.le_iff_mul_eq_left (join_projection hp q)).mpr
  change p*(p+remainder p q)=p
  rw [mul_add,hp.isIdempotentElem.eq,mul_remainder hp q,add_zero]

open PartialIsometryOrder PartialIsometryOrder.DyadicPartition

end Kadison.ProjectionJoin

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_CountableProjectionJoin
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

open scoped ComplexOrder InnerProductSpace Topology BigOperators

namespace Kadison.ProjectionJoin

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma finiteJoin_mem (M : VonNeumannAlgebra H) (P : ℕ → H →L[ℂ] H) (hP : ∀ n,P n∈M) (n : ℕ) :
    finiteJoin P n∈M := by
  induction n with
  | zero => exact M.zero_mem
  | succ n ih => exact join_mem M ih (hP n)

open PartialIsometryOrder PartialIsometryOrder.DyadicPartition

end Kadison.ProjectionJoin

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

abbrev sumLevel (k : ℕ) := Completion (wordSpace (fullSpace τ) (zeroSpace τ) k ⊗[ℂ] J k)

end Kadison.TracialGNS
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

variable (ι : Type*) [Fintype ι] (i₀ : ι) (M : VonNeumannAlgebra H)

attribute [local instance] OAI.Kadison.OperatorAmplification.instDecidableEq_solutions
def matrixHom : CStarMatrix ι ι M →⋆ₐ[ℂ] matrixVonNeumann ι i₀ M :=
  rangeRestriction (matrixVonNeumann ι i₀ M)
    (CyclicColumns.matrixRepresentation (A:=M) (H:=H) M.toStarSubalgebra.subtype)
    (matrix_representation_mem ι i₀ M)

lemma coe_matrixHom (X : CStarMatrix ι ι M) :
    (matrixHom ι i₀ M X:SumSpace (H:=H) ι →L[ℂ] SumSpace (H:=H) ι)=
      CyclicColumns.matrixRepresentation (A:=M) (H:=H) M.toStarSubalgebra.subtype X := rfl

lemma matrixHom_bijective : Function.Bijective (matrixHom ι i₀ M) := by
  constructor
  · intro X Y h
    apply CStarMatrix.ext
    intro i j
    apply Subtype.ext
    have he := congrArg (fun T : matrixVonNeumann ι i₀ M =>
      entry ι (T:SumSpace (H:=H) ι →L[ℂ] SumSpace (H:=H) ι) i j) h
    simpa only [coe_matrixHom,entry_matrixRepresentation] using he
  · intro T
    obtain ⟨X,hX⟩ := matrixVonNeumann_is_range ι i₀ M T T.property
    exact ⟨X,Subtype.ext hX⟩

end Kadison.OperatorAmplification

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_NormalBiprodGNS
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

open scoped Topology ComplexOrder NNReal

open Filter ContinuousLinearMapWOT

namespace Kadison.NormalOperatorHom

variable {H G : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]

variable (M : VonNeumannAlgebra H)

lemma gns_normal (τ : M →ₚ[ℂ] ℂ) (hτ : NormalGNS.BoundedWOTContinuous M τ) :
    BoundedNormal M τ.gnsStarAlgHom := by
  intro C x y
  apply continuous_iff_continuousAt.mpr
  intro a
  let C' : ℝ≥0 := ⟨max C 0,le_max_right _ _⟩
  let f : {T : H →WOT[ℂ] H // T.toCLM∈M ∧ ‖T.toCLM‖≤C} → M :=
    fun b => ⟨b.val.toCLM,b.property.1⟩
  have hf : ∀ b,‖f b‖≤C' := fun b => b.property.2.trans (le_max_left _ _)
  apply NormalGNS.tendsto_gns M τ hτ f (f a) C' hf (hf a)
  intro u v
  have hc := (ContinuousLinearMapWOT.continuous_inner_apply continuous_subtype_val u v).tendsto a
  simpa only [f,RCLike.star_def,inner_conj_symm,coe_toCLM] using hc.star

end Kadison.NormalOperatorHom

end

end
end

end OAI
end


