-- Prove2me | Definitions.Def_OAIQ039C030
-- name    : OAIQ039C030
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-28T09:09:12.826979+00:00
-- url     : https://prove2.me/theorems/441dac10-5c83-41e4-b0e6-5bdd60efef40
-- title:
--   Definitions bundle OAIQ039C030 of the split of OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Kadison.uniform_commutator`, carved from OpenAI's openai/math development (OpenAI, *Kadison's similarity theorem through uniform derivation estimates (result family 288)*, OpenAI Math Release, September 23, 2026, result family 288, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 23 declarations of OpenAI's Lean: 12 definitions, 3 instances and 8 theorems. The definitions and types are `OAI.Kadison.RectangularColumn.triangularHom`, `OAI.Kadison.SchurWeyl.fixedLabelEquiv`, `OAI.Kadison.SeparableTest.SeparableBound`, `OAI.Kadison.SeparableTest.entries`, `OAI.Kadison.SeparableTest.representation`, `OAI.Kadison.SeparableTest.restrictedY`, `OAI.Kadison.SeparableTest.vector`, `OAI.Kadison.TracialSequence.cutSequence`, `OAI.Kadison.UnitaryOrbit.hull`, `OAI.Kadison.center`, `OAI.Kadison.centeredIsometry`, `OAI.Kadison.innerDerivation`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis/Commutator, in whole or in part: `Commutator_CenteredSpace`, `Commutator_CycleInvariants`, `Commutator_HilbertTensors`, `Commutator_MainMatrix`, `Commutator_RectangularColumn`, `Commutator_SeparableBoundTransfer`, `Commutator_SeparableTestGeometry`, `Commutator_TracialSequenceTrace`, `Commutator_TracialSmallCorners`, `Commutator_UnitaryHaar`, `Commutator_UnitaryOrbitHull`.
--
--   **Imports.** It imports the published bundle `Def_UniformCommutator`; the bundles `OAIQ039C002`, `OAIQ039C004`, `OAIQ039C005`, `OAIQ039C007`, `OAIQ039C008`, `OAIQ039C010`, `OAIQ039C014`, `OAIQ039C016`, `OAIQ039C017` and `OAIQ039C018` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ039C040` and `OAIQ039C048`; the statements `OAI.Kadison.CentralAverage.exists_finite_average`, `OAI.Kadison.CentralSpectral.separable_uniform_bound`, `OAI.Kadison.SeparableTest.bound_of_separable_bound` and `OAI.Kadison.SeparableTest.seminorm_bound`; the proofs of `OAI.Kadison.CentralAverage.exists_finite_average`, `OAI.Kadison.CentralSpectral.separable_uniform_bound`, `OAI.Kadison.RectangularColumn.column_bound`, `OAI.Kadison.RepresentedTower.exists_tower_average`, `OAI.Kadison.SeparableTest.bound_of_separable_bound`, `OAI.Kadison.SeparableTest.seminorm_bound`, `OAI.Kadison.commutator_column_bound`, `OAI.Kadison.isometry_column_error_bound`, `OAI.Kadison.uniform_commutator`, `OAI.Kadison.uniform_commutator_atomic_factor` and `OAI.Kadison.uniform_commutator_finiteDimensional`.
-- source:
--   OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 288; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Kadisons-similarity-theorem-through-uniform-derivation-estimates-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis/Commutator at commit adc7f12

import Mathlib
import Definitions.Def_UniformCommutator
import Definitions.Def_OAIQ039C002
import Definitions.Def_OAIQ039C004
import Definitions.Def_OAIQ039C005
import Definitions.Def_OAIQ039C007
import Definitions.Def_OAIQ039C008
import Definitions.Def_OAIQ039C010
import Definitions.Def_OAIQ039C014
import Definitions.Def_OAIQ039C016
import Definitions.Def_OAIQ039C017
import Definitions.Def_OAIQ039C018

section
-- module Solutions.OAIQ039_CM.Commutator_CenteredSpace
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.UnitaryDualAction.action _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ComplexOrder InnerProductSpace
open Complex ContinuousLinearMap UniformSpace Completion
open scoped InnerProductSpace

namespace Kadison

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

def center (Ω : E) : E →L[ℂ] centeredSpace Ω :=
  (centeredSpace Ω).orthogonalProjectionOnto

def centeredIsometry (Ω : E) (U : E →ₗᵢ[ℂ] E) (hU : U Ω = Ω) :
    centeredSpace Ω →ₗᵢ[ℂ] centeredSpace Ω :=
  { U.toLinearMap.domRestrict (centeredSpace Ω) |>.codRestrict (centeredSpace Ω)
      (fun x => by
        change U (x : E) ∈ (ℂ ∙ Ω)ᗮ
        rw [Submodule.mem_orthogonal_singleton_iff_inner_right]
        have h := U.inner_map_map Ω (x : E)
        rw [hU] at h
        rw [h]
        exact Submodule.mem_orthogonal_singleton_iff_inner_right.mp x.property) with
    norm_map' := fun x => U.norm_map x }

@[simp] lemma centeredIsometry_apply (Ω : E) (U : E →ₗᵢ[ℂ] E) (hU : U Ω = Ω)
    (x : centeredSpace Ω) : (centeredIsometry Ω U hU x : E) = U (x : E) := rfl

end Kadison
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_CycleInvariants
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.UnitaryDualAction.action _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass
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

def fixedLabelEquiv (R : Type*) (σ : Equiv.Perm J) :
    {f : J → R // ∀ j, f (σ j) = f j} ≃ (cycleSet σ → R) where
  toFun f := Quotient.lift f.val (fun _ _ h => constant_on_cycle σ f.val f.property h)
  invFun f := ⟨fun j => f (Quotient.mk _ j), fun j => congrArg f (Quotient.sound (by
    exact (Equiv.Perm.SameCycle.refl σ j).apply_left))⟩
  left_inv f := by rfl
  right_inv f := by ext q; refine Quotient.inductionOn q (fun j => ?_); rfl

end Kadison.SchurWeyl
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_HilbertTensors
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.UnitaryDualAction.action _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass
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

attribute [instance] PreHilbert.normed PreHilbert.ipSpace

namespace PreHilbert

theorem span_pure (E : PreHilbert) (n : ℕ) :
    Submodule.span ℂ (Set.range (pure E n)) = ⊤ := by
  induction n with
  | zero =>
    apply Submodule.eq_top_iff'.mpr
    intro z
    have h : (1 : ℂ) ∈ Submodule.span ℂ (Set.range (pure E 0)) :=
      Submodule.subset_span ⟨Fin.elim0, rfl⟩
    simpa using (Submodule.span ℂ (Set.range (pure E 0))).smul_mem z h
  | succ n ih =>
    apply Submodule.eq_top_iff'.mpr
    intro z
    induction z using OAI.tensorInductionOn with
    | add x y hx hy => exact Submodule.add_mem _ hx hy
    | tmul x y =>
      have hy : y ∈ Submodule.span ℂ (Set.range (pure E n)) := by rw [ih]; trivial
      induction hy using Submodule.span_induction with
      | mem y hy =>
        obtain ⟨v, rfl⟩ := hy
        apply Submodule.subset_span
        exact ⟨Fin.cons x v, by simp [pure]⟩
      | zero => simp only [TensorProduct.tmul_zero, Submodule.zero_mem]
      | add y z _ _ hy hz =>
        simpa only [TensorProduct.tmul_add] using
          (Submodule.span ℂ (Set.range (pure E (n+1)))).add_mem hy hz
      | smul c y _ hy =>
        simpa only [TensorProduct.tmul_smul] using
          (Submodule.span ℂ (Set.range (pure E (n+1)))).smul_mem c hy

end PreHilbert

end Kadison
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_MainMatrix
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.UnitaryDualAction.action
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

universe u

open scoped InnerProductSpace BigOperators ComplexOrder

namespace Kadison

variable {K : Type u} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

def innerDerivation (P : VonNeumannAlgebra K) (Y : K →L[ℂ] K) :
    P →L[ℂ] (K →L[ℂ] K) :=
  ({ toFun := fun a => Y*(a:K →L[ℂ] K)-(a:K →L[ℂ] K)*Y
     map_add' := by
       intro a b
       change Y*((a:K →L[ℂ] K)+b)-((a:K →L[ℂ] K)+b)*Y=
         (Y*a-(a:K →L[ℂ] K)*Y)+(Y*b-(b:K →L[ℂ] K)*Y)
       noncomm_ring
     map_smul' := by
       intro c a
       change Y*(c • (a:K →L[ℂ] K))-(c • (a:K →L[ℂ] K))*Y=c • (Y*a-(a:K →L[ℂ] K)*Y)
       simp only [mul_smul_comm,smul_mul_assoc,smul_sub] } :
    P →ₗ[ℂ] (K →L[ℂ] K)).mkContinuous (commutatorSeminorm P Y)
      (fun a => commutator_bound P Y a.property)

@[simp] lemma innerDerivation_apply (P : VonNeumannAlgebra K) (Y : K →L[ℂ] K) (a : P) :
    innerDerivation P Y a=Y*(a:K →L[ℂ] K)-(a:K →L[ℂ] K)*Y := rfl

end Kadison

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_RectangularColumn
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.UnitaryDualAction.action _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped InnerProductSpace BigOperators

namespace Kadison.RectangularColumn

variable {A K F : Type*} [CStarAlgebra A]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

def triangularHom (σ : A →⋆ₐ[ℂ] (K →L[ℂ] K))
    (lam : A →⋆ₐ[ℂ] (F →L[ℂ] F)) (D : A →L[ℂ] (K →L[ℂ] F))
    (hD : ∀ a b, D (a*b)=(D a).comp (σ b)+(lam a).comp (D b)) :
    A →ₐ[ℂ] (SumHilbert F K →L[ℂ] SumHilbert F K) where
  toFun := triangularMap σ lam D
  map_one' := by
    ext x
    apply (WithLp.equiv 2 (F × K)).injective
    apply Prod.ext <;> simp [derivation_one σ lam D hD]
  map_mul' a b := by
    ext x
    apply (WithLp.equiv 2 (F × K)).injective
    apply Prod.ext
    · simp [hD,mul_apply_eq_comp,map_add]
      abel
    · simp [mul_apply_eq_comp]
  map_zero' := by
    ext x
    apply (WithLp.equiv 2 (F × K)).injective
    apply Prod.ext <;> simp
  map_add' a b := by
    ext x
    apply (WithLp.equiv 2 (F × K)).injective
    apply Prod.ext <;> simp [add_add_add_comm]
  commutes' z := by
    ext x
    apply (WithLp.equiv 2 (F × K)).injective
    apply Prod.ext <;> simp [Algebra.algebraMap_eq_smul_one,
      derivation_one σ lam D hD]

@[simp] lemma triangularHom_apply (σ : A →⋆ₐ[ℂ] (K →L[ℂ] K))
    (lam : A →⋆ₐ[ℂ] (F →L[ℂ] F)) (D : A →L[ℂ] (K →L[ℂ] F)) hD
    (a : A) : triangularHom σ lam D hD a=triangularMap σ lam D a := rfl

end Kadison.RectangularColumn

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_TracialSequenceTrace
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.UnitaryDualAction.action _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass
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

namespace Kadison

namespace VectorFunctional

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma functional_star_mul (x : H) (T : H →L[ℂ] H) :
    functional x (star T*T)=inner ℂ (T x) (T x) := by
  rw [functional_apply,mul_apply_eq_comp,ContinuousLinearMap.star_eq_adjoint,
    ContinuousLinearMap.adjoint_inner_right]

end VectorFunctional

end Kadison

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_SeparableTestGeometry
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.UnitaryDualAction.action
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped InnerProductSpace BigOperators

namespace Kadison.SeparableTest

open SeparableReducingHull ReducingRepresentation

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (h : ℕ) (X : Matrix (Fin h) (Fin h) (H →L[ℂ] H)) (Y : H →L[ℂ] H)

instance space_complete (ξ : PiLp 2 (fun _ : Fin h => H)) : CompleteSpace (space h X Y ξ) :=
  SeparableReducingHull.hull_complete _ _

instance space_separable (ξ : PiLp 2 (fun _ : Fin h => H)) : TopologicalSpace.SeparableSpace (space h X Y ξ) :=
  SeparableReducingHull.hull_separable _ _

lemma entry_mem (i j : Fin h) : X i j∈algebra h X :=
  StarSubalgebra.le_topologicalClosure _ (StarAlgebra.subset_adjoin ℂ _ (Set.mem_range_self (i,j)))

def entries : Matrix (Fin h) (Fin h) (algebra h X) := fun i j => ⟨X i j,entry_mem h X i j⟩

variable (ξ : PiLp 2 (fun _ : Fin h => H))

lemma algebra_invariant (a : algebra h X) (x : H) (hx : x∈space h X Y ξ) :
    (a:H →L[ℂ] H) x∈space h X Y ξ := (algebra_reduces h X Y ξ a.property).1 x hx

def representation : algebra h X →⋆ₐ[ℂ] (space h X Y ξ →L[ℂ] space h X Y ξ) :=
  restrict (algebra h X).subtype _ (algebra_invariant h X Y ξ)

def restrictedY : space h X Y ξ →L[ℂ] space h X Y ξ := Y.restrict (Y_invariant h X Y ξ)

def vector : PiLp 2 (fun _ : Fin h => space h X Y ξ) :=
  WithLp.toLp 2 (fun i => ⟨ξ i,vector_mem _ _ i⟩)

end Kadison.SeparableTest

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_SeparableBoundTransfer
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.UnitaryDualAction.action
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped InnerProductSpace BigOperators

universe u

namespace Kadison.SeparableTest

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (P : VonNeumannAlgebra H) (Y : H →L[ℂ] H) (h : ℕ)
  (X : Matrix (Fin h) (Fin h) (H →L[ℂ] H)) (hX : ∀ i j,X i j∈P)

include hX

def SeparableBound (c : ℝ) : Prop :=
  ∀ (K : Type u) [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    [CompleteSpace K] [TopologicalSpace.SeparableSpace K]
    (P : VonNeumannAlgebra K) (Y : K →L[ℂ] K) (h : ℕ),1≤h →
    ∀ X : Matrix (Fin h) (Fin h) (K →L[ℂ] K), (∀ i j,X i j∈P) →
    ‖diagonalAmplification h Y*matrixOperator h X-matrixOperator h X*diagonalAmplification h Y‖≤
      c*commutatorSeminorm P Y*‖matrixOperator h X‖

end Kadison.SeparableTest

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_TracialSmallCorners
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.UnitaryDualAction.action
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

attribute [local instance] Classical.propDecidable

open scoped Topology InnerProductSpace BoundedContinuousFunction ComplexOrder

open Filter UniformSpace Completion

namespace Kadison.TracialSequence

open TracialGNS

variable {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]

variable [PartialOrder A] [StarOrderedRing A]

variable (τ : A →ₚ[ℂ] ℂ) (ω : Ultrafilter ℕ)

variable (hτ : ∀ a b : A, τ (a*b)=τ (b*a))

def cutSequence {G : Type*} [NormedAddCommGroup G] [InnerProductSpace ℂ G]
    [CompleteSpace G] (N : VonNeumannAlgebra G) (q : ℕ →ᵇ N)
    (good : ℕ → Prop) : ℕ →ᵇ N :=
  BoundedContinuousFunction.ofNormedAddCommGroupDiscrete
    (fun i => if good i then q i else 0) ‖q‖ (fun i => by
      split_ifs
      · exact q.norm_coe_le_norm i
      · simpa only [norm_zero] using norm_nonneg q)

@[simp] lemma cutSequence_apply {G : Type*} [NormedAddCommGroup G] [InnerProductSpace ℂ G]
    [CompleteSpace G] (N : VonNeumannAlgebra G) (q : ℕ →ᵇ N)
    (good : ℕ → Prop) (i : ℕ) :
    cutSequence N q good i=if good i then q i else 0 := rfl

end Kadison.TracialSequence

end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_UnitaryHaar
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.UnitaryDualAction.action _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open MeasureTheory MeasureTheory.Measure TopologicalSpace

namespace Kadison.UnitaryHaar

variable (A : Type*) [CStarAlgebra A] [FiniteDimensional ℂ A] [Nontrivial A]

variable (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [MeasurableSpace G] [BorelSpace G]

instance instIsProbabilityMeasureProbability : IsProbabilityMeasure (probability G) where
  measure_univ := haarMeasure_self

end Kadison.UnitaryHaar

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_UnitaryOrbitHull
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.UnitaryDualAction.action
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped InnerProductSpace

namespace Kadison.UnitaryOrbit

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (M : VonNeumannAlgebra H)

def hull (Y : H →L[ℂ] H) : Set (H →L[ℂ] H) :=
  convexHull ℝ (Set.range (fun v : unitary M => conjugate M v Y))

end Kadison.UnitaryOrbit

end

end
end

end OAI
end


