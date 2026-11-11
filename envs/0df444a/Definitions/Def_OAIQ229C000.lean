-- Prove2me | Definitions.Def_OAIQ229C000
-- name    : OAIQ229C000
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-11T05:27:45.606465+00:00
-- url     : https://prove2.me/theorems/3c7bcb92-f2bf-45a3-8d64-e01b80dda523
-- title:
--   Definitions bundle OAIQ229C000 of the split of OpenAI, A counterexample to the coarse Novikov conjecture (result family 307)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.CoarseAssembly.bounded_geometry_graph_counterexample_unconditional`, carved from OpenAI's openai/math development (OpenAI, *A counterexample to the coarse Novikov conjecture (result family 307)*, OpenAI Math Release, September 23, 2026, result family 307, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 128 declarations of OpenAI's Lean: 27 definitions, 1 inductive type or structure, 3 instances and 97 theorems. The definitions and types are `OAI.CoarseAssembly.Analytic.CircleSequence`, `OAI.CoarseAssembly.Analytic.Coarsening.of`, `OAI.CoarseAssembly.Analytic.CoarseningMorphism.homologyMap`, `OAI.CoarseAssembly.Analytic.CompactContraction`, `OAI.CoarseAssembly.Analytic.CompatibleIndexFamily.mapTarget`, `OAI.CoarseAssembly.Analytic.HilbertSum`, `OAI.CoarseAssembly.Analytic.OddCycle.IsDirectSum.block`, `OAI.CoarseAssembly.Analytic.OddHomotopy.bounded`, `OAI.CoarseAssembly.Analytic.OddHomotopy.regularize`, `OAI.CoarseAssembly.Analytic.OddHomotopy.unitalSelfAdjoint`, `OAI.CoarseAssembly.Analytic.bilateralShift`, `OAI.CoarseAssembly.Analytic.bilateralShiftEquiv`, `OAI.CoarseAssembly.Analytic.binaryBlock`, `OAI.CoarseAssembly.Analytic.binaryFlip`, `OAI.CoarseAssembly.Analytic.binaryHilbertSpace`, `OAI.CoarseAssembly.Analytic.binaryLeft`, `OAI.CoarseAssembly.Analytic.binaryRight`, `OAI.CoarseAssembly.Analytic.circleSequenceSpace`, `OAI.CoarseAssembly.Analytic.countableHilbertSpace`, `OAI.CoarseAssembly.Analytic.cycleHilbertFamily`, `OAI.CoarseAssembly.Analytic.projectionSwap`, `OAI.CoarseAssembly.Analytic.projectionSwapUnitary`, `OAI.CoarseAssembly.Analytic.reindexSequence`, `OAI.CoarseAssembly.Analytic.reindexSequenceEquiv`, `OAI.CoarseAssembly.Analytic.sigmaFunctionRestriction`, `OAI.CoarseAssembly.Analytic.sigmaRepresentationOperator`, `OAI.CoarseAssembly.Analytic.summandIsometry`, `OAI.CoarseAssembly.FiberBits`.
--
--   **Sources.** They come from these modules of lean/OAI/Topology, in whole or in part: `CoarseAssembly_AnalyticKHomology`, `CoarseAssembly_Assembly`, `CoarseAssembly_BilateralShift`, `CoarseAssembly_BinaryHilbertSum`, `CoarseAssembly_BlockOperators`, `CoarseAssembly_BoundedCycleTransform`, `CoarseAssembly_BoundedTransform`, `CoarseAssembly_BoundedTransformCompact`, `CoarseAssembly_CayleyBoundary`, `CoarseAssembly_CayleyContinuity`, `CoarseAssembly_CharacterExtension`, `CoarseAssembly_Conjugation`, `CoarseAssembly_ContinuousUnitalization`, `CoarseAssembly_CountableHilbertSum`, `CoarseAssembly_CycleIndex`, `CoarseAssembly_DegenerateRegularization`, `CoarseAssembly_ExplicitCutDown`, `CoarseAssembly_FiberDegree`, `CoarseAssembly_FredholmModule`, `CoarseAssembly_HilbertSum`, `CoarseAssembly_HomotopyFilling`, `CoarseAssembly_IndexFamilyTransport`, `CoarseAssembly_LocallyFinite`, `CoarseAssembly_NonUnitalK1`, `CoarseAssembly_OrthogonalBlock`, `CoarseAssembly_ProjectionSwap`, `CoarseAssembly_RegularizedCycle`, `CoarseAssembly_RepresentedCutDown`, `CoarseAssembly_ScalarCutDown`, `CoarseAssembly_SigmaCycleRepresentation`, `CoarseAssembly_SigmaFunctionNorms`, `CoarseAssembly_TopologicalK1`.
--
--   **Imports.** It imports the published bundle `Def_CoarseAssembly`; the published statements `Theorems.Thm_FredholmBanach_index_comp`, `Theorems.Thm_FredholmBanach_index_eq_zero_tfae` and `Theorems.Thm_FredholmBanach_isFredholm_comp`.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ229C009`, `OAIQ229C010`, `OAIQ229C011`, `OAIQ229C012` and `OAIQ229C015`.
-- source:
--   OpenAI, A counterexample to the coarse Novikov conjecture (result family 307), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 307; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/CoarseAssembly.lean; Apache License 2.0); definitions carved from lean/OAI/Topology at commit adc7f12

import Mathlib
import Mathlib.Algebra.AlgebraicCard
import Mathlib.Algebra.Colimit.Module
import Mathlib.Algebra.Group.Commute.Units
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Group.MinMax
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Star.StarProjection
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Range
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.CStarAlgebra.ContinuousMap
import Mathlib.Analysis.CStarAlgebra.Spectrum
import Mathlib.Analysis.CStarAlgebra.Unitization
import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.Convex.PathConnected
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Analysis.Normed.Operator.Compact.Basic
import Mathlib.Analysis.Normed.Operator.Compact.FiniteDimension
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.Normed.Ring.Lemmas
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Combinatorics.SimpleGraph.Walk.Decomp
import Mathlib.Data.Finset.Union
import Mathlib.Data.Finsupp.Basic
import Mathlib.Data.Int.Interval
import Mathlib.Data.List.Basic
import Mathlib.Data.Matrix.Block
import Mathlib.Data.Set.Card
import Mathlib.Data.Set.Finite.Lattice
import Mathlib.GroupTheory.FreeAbelianGroup
import Mathlib.GroupTheory.QuotientGroup.Defs
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.RingTheory.Algebraic.Basic
import Mathlib.RingTheory.TwoSidedIdeal.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Group
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Module
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.Algebra.Module.PerfectSpace
import Mathlib.Topology.Algebra.NonUnitalStarAlgebra
import Mathlib.Topology.Algebra.Ring.Basic
import Mathlib.Topology.Algebra.Support
import Mathlib.Topology.Baire.CompleteMetrizable
import Mathlib.Topology.Connected.TotallyDisconnected
import Mathlib.Topology.Constructions
import Mathlib.Topology.DenseEmbedding
import Mathlib.Topology.Homotopy.Basic
import Mathlib.Topology.Instances.AddCircle.Defs
import Mathlib.Topology.Instances.AddCircle.Real
import Mathlib.Topology.Instances.Matrix
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.MetricSpace.ProperSpace
import Definitions.Def_CoarseAssembly
import Theorems.Thm_FredholmBanach_index_comp
import Theorems.Thm_FredholmBanach_index_eq_zero_tfae
import Theorems.Thm_FredholmBanach_isFredholm_comp

section
-- module Solutions.Q229_CA.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem ite_eq_left {α : Sort _} {c : Prop} {_ : Decidable c} {a b : α} (h : c) :
    (if c then a else b) = a := if_pos h
end OAICompat434

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_Conjugation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Conjugation by an isometry

The spatial operator homomorphism and exact boundary factorization used in
§§5--6 of the coarse Novikov manuscript. Restriction of this homomorphism to
the Roe algebras is a separate range-membership obligation.
-/

namespace CoarseAssembly

variable {E F H : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem operatorConjugation_star (V : E →ₗᵢ[ℂ] F) (T : E →L[ℂ] E) :
    operatorConjugation V (star T) = star (operatorConjugation V T) := by
  simp [operatorConjugation, ContinuousLinearMap.star_eq_adjoint,
    ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.comp_assoc]

end CoarseAssembly

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_FredholmModule
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Odd analytic Fredholm modules

These are the actual operator cycles for `KK₁(A, ℂ)`: a separable Hilbert
space, a star representation of `A`, and an operator whose commutator,
self-adjointness defect and square defect are locally compact. We keep
degenerate cycles, unitary equivalence, direct sum and norm homotopy explicit
so that the analytic group can be formed as a quotient, rather than supplied
as an arbitrary abelian group.
-/

noncomputable section

namespace CoarseAssembly.Analytic

universe u

attribute [instance] HilbertSpace.normed HilbertSpace.inner
  HilbertSpace.complete HilbertSpace.secondCountable

variable (A : Type u) [NonUnitalCStarAlgebra A]

variable {A} {B : Type u} [NonUnitalCStarAlgebra B]

namespace OddCycle

theorem Degenerate.precomp {c : OddCycle A} (hc : c.Degenerate)
    (φ : B →⋆ₙₐ[ℂ] A) : (c.precomp φ).Degenerate :=
  ⟨fun b => hc.1 (φ b), fun b => hc.2.1 (φ b), fun b => hc.2.2 (φ b)⟩

@[simp] theorem precomp_id (c : OddCycle A) :
    c.precomp (NonUnitalStarAlgHom.id ℂ A) = c := by cases c; rfl

@[simp] theorem precomp_comp {C : Type u} [NonUnitalCStarAlgebra C]
    (c : OddCycle A) (φ : B →⋆ₙₐ[ℂ] A) (ψ : C →⋆ₙₐ[ℂ] B) :
    (c.precomp φ).precomp ψ = c.precomp (φ.comp ψ) := rfl

end OddCycle

namespace OddHomotopy

@[simp] theorem precomp_eval (h : OddHomotopy A) (φ : B →⋆ₙₐ[ℂ] A) (t : Interval) :
    (h.precomp φ).eval t = (h.eval t).precomp φ := rfl

end OddHomotopy

end CoarseAssembly.Analytic

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_AnalyticKHomology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The odd Fredholm-module group

The group is formed from actual analytic cycles, modulo degeneracy, unitary
equivalence, orthogonal direct sum and norm homotopy. Pullback of star
representations descends to this quotient. This gives the analytic domain
needed for the subsequent geometric construction; no assembly or nonzero
class is postulated here.
-/

noncomputable section

namespace CoarseAssembly.Analytic

universe u

variable (A : Type u) [NonUnitalCStarAlgebra A]

variable {A}

variable {B C : Type u} [NonUnitalCStarAlgebra B] [NonUnitalCStarAlgebra C]

@[simp] theorem precomp_cycleClass (φ : B →⋆ₙₐ[ℂ] A) (c : OddCycle A) :
    precomp φ (cycleClass A c) = cycleClass B (c.precomp φ) := by
  exact FreeAbelianGroup.lift_apply_of _ _

theorem hom_ext {D : Type*} [AddCommGroup D] (f g : OddK A →+ D)
    (h : ∀ c, f (cycleClass A c) = g (cycleClass A c)) : f = g := by
  apply QuotientAddGroup.addMonoidHom_ext
  exact FreeAbelianGroup.lift_ext _ _ h

@[simp] theorem precomp_id : precomp (NonUnitalStarAlgHom.id ℂ A) = AddMonoidHom.id (OddK A) := by
  apply hom_ext
  intro c
  simp

theorem precomp_comp (φ : B →⋆ₙₐ[ℂ] A) (ψ : C →⋆ₙₐ[ℂ] B) :
    precomp (φ.comp ψ) = (precomp ψ).comp (precomp φ) := by
  apply hom_ext
  intro c
  simp

end CoarseAssembly.Analytic

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_TopologicalK1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Topological K₁ from stable invertible matrices

The unital group is presented by invertible finite matrices, with the actual
matrix-product, stabilization and continuous-path relations. The nonunital
group will be the kernel of the scalar-quotient map on the unitization.
These definitions keep the analytic assembly target tied to its algebra.
-/

noncomputable section

namespace CoarseAssembly.TopologicalK1

open CoarseAssembly.Analytic (Interval start finish)

universe u v w

variable (R : Type u) [Ring R] [TopologicalSpace R]

variable {R}

theorem relation_zero {z : FreeAbelianGroup (StableGL R)} (h : Relation R z) :
    (QuotientAddGroup.mk z : Group R) = 0 :=
  (QuotientAddGroup.eq_zero_iff z).2 (AddSubgroup.subset_closure h)

theorem matrixClass_mul {n : ℕ} (g h : InvertibleMatrix R n) :
    matrixClass R (g * h) = matrixClass R g + matrixClass R h := by
  apply sub_eq_zero.mp
  simpa only [matrixClass, QuotientAddGroup.mk_sub, QuotientAddGroup.mk_add] using
    relation_zero (.mul g h)

@[simp] theorem matrixClass_one (n : ℕ) : matrixClass R (1 : InvertibleMatrix R n) = 0 := by
  have h := matrixClass_mul (1 : InvertibleMatrix R n) 1
  simp only [one_mul] at h
  exact (add_left_cancel ((add_zero _).trans h)).symm

variable {S : Type v} {T : Type w} [Ring S] [TopologicalSpace S] [Ring T] [TopologicalSpace T]

@[simp] theorem map_matrixClass (φ : R →+* S) (hφ : Continuous φ) {n : ℕ} (g : InvertibleMatrix R n) :
    map φ hφ (matrixClass R g) = matrixClass S (mapGL φ n g) :=
  FreeAbelianGroup.lift_apply_of _ _

theorem hom_ext {D : Type*} [AddCommGroup D] (f g : Group R →+ D)
    (h : ∀ n (a : InvertibleMatrix R n), f (matrixClass R a) = g (matrixClass R a)) : f = g := by
  apply QuotientAddGroup.addMonoidHom_ext
  apply FreeAbelianGroup.lift_ext
  rintro ⟨n, a⟩
  exact h n a

omit [TopologicalSpace R] in
@[simp] theorem mapGL_id {n : ℕ} (g : InvertibleMatrix R n) : mapGL (RingHom.id R) n g = g := by
  apply Units.ext
  rfl

@[simp] theorem map_id : map (RingHom.id R) continuous_id = AddMonoidHom.id (Group R) := by
  apply hom_ext
  intro n a
  simp

end CoarseAssembly.TopologicalK1

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_NonUnitalK1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# K₁ of nonunital C*-algebras

The group is the kernel of the scalar projection from the unitization.
Nonunital star homomorphisms induce actual maps of these kernels, preserving
composition. This is the target functor for the reduced Roe assembly map.
-/

noncomputable section

namespace CoarseAssembly.OperatorKTheory

open scoped CStarAlgebra

universe u v w

variable (A : Type u) [NonUnitalCStarAlgebra A]

variable {A} {B : Type v} [NonUnitalCStarAlgebra B]
variable {C : Type w} [NonUnitalCStarAlgebra C]

@[simp] theorem scalarMap_matrixClass {n : ℕ}
    (g : TopologicalK1.InvertibleMatrix (Unitization ℂ A) n) :
    scalarMap A (TopologicalK1.matrixClass (Unitization ℂ A) g) =
      TopologicalK1.matrixClass ℂ
        (TopologicalK1.mapGL (Unitization.fstHom ℂ A).toRingHom n g) :=
  TopologicalK1.map_matrixClass _ _ _

@[simp] theorem unitizationMap_matrixClass (φ : A →⋆ₙₐ[ℂ] B) {n : ℕ}
    (g : TopologicalK1.InvertibleMatrix (Unitization ℂ A) n) :
    unitizationMap φ (TopologicalK1.matrixClass (Unitization ℂ A) g) =
      TopologicalK1.matrixClass (Unitization ℂ B)
        (TopologicalK1.mapGL (Unitization.starMap φ).toRingHom n g) :=
  TopologicalK1.map_matrixClass _ _ _

@[simp] theorem map_coe (φ : A →⋆ₙₐ[ℂ] B) (x : K1 A) :
    (map φ x : TopologicalK1.Group (Unitization ℂ B)) = unitizationMap φ x := rfl

@[simp] theorem unitizationMap_id :
    unitizationMap (NonUnitalStarAlgHom.id ℂ A) =
      AddMonoidHom.id (TopologicalK1.Group (Unitization ℂ A)) := by
  apply TopologicalK1.hom_ext
  intro n g
  simp only [unitizationMap_matrixClass, AddMonoidHom.id_apply]
  congr 1
  apply Units.ext
  apply Matrix.ext
  intro i j
  change Unitization.starMap (NonUnitalStarAlgHom.id ℂ A) ((g : Matrix (Fin n) (Fin n) (Unitization ℂ A)) i j) = _
  simp

@[simp] theorem map_id : map (NonUnitalStarAlgHom.id ℂ A) = AddMonoidHom.id (K1 A) := by
  apply AddMonoidHom.ext
  intro x
  apply Subtype.ext
  exact DFunLike.congr_fun (unitizationMap_id (A := A)) (x : TopologicalK1.Group (Unitization ℂ A))

end CoarseAssembly.OperatorKTheory

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_LocallyFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Locally finite analytic K-homology and coarsening

The domain is the odd Fredholm-module group of the actual algebra `C₀(Y, ℂ)`.
A proper continuous map acts by pulling back functions and representations.
The coarsening limit is an actual algebraic direct limit of those groups.
-/

noncomputable section

namespace CoarseAssembly.Analytic

open scoped ZeroAtInfty

universe u

variable {X Y Z : Type u} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

@[simp] theorem pullback_apply (f : CocompactMap X Y) (a : C₀(Y, ℂ)) (x : X) :
    pullback f a x = a (f x) := rfl

theorem pullback_comp (f : CocompactMap X Y) (g : CocompactMap Y Z) :
    pullback (g.comp f) = (pullback f).comp (pullback g) := by
  ext a x
  rfl

@[simp] theorem pullback_id : pullback (CocompactMap.id X) = NonUnitalStarAlgHom.id ℂ C₀(X, ℂ) := by
  ext a x
  rfl

theorem pushforward_comp (f : CocompactMap X Y) (g : CocompactMap Y Z) :
    pushforward (g.comp f) = (pushforward g).comp (pushforward f) := by
  rw [pushforward, pullback_comp, precomp_comp]
  rfl

@[simp] theorem pushforward_id : pushforward (CocompactMap.id X) = AddMonoidHom.id _ := by
  simp only [pushforward, pullback_id, precomp_id]

attribute [instance] Coarsening.topology

namespace Coarsening

instance instDirectedSystemNatLocallyFiniteK1SpaceCoeAddMonoidHomMap (C : Coarsening) :
    DirectedSystem (fun r => LocallyFiniteK1 (C.space r)) (fun r s h => C.map r s h) where
  map_self r x := by simp [map, C.inclusion_self]
  map_map t s r hrs hst x := by
    change (pushforward (C.inclusion s t hst)) ((pushforward (C.inclusion r s hrs)) x) = _
    rw [← AddMonoidHom.comp_apply, ← pushforward_comp, ← C.inclusion_comp]
    rfl

def of (C : Coarsening) (r : ℕ) : LocallyFiniteK1 (C.space r) →+ C.Homology :=
  AddCommGroup.DirectLimit.of (fun n => LocallyFiniteK1 (C.space n))
    (fun n m h => C.map n m h) r

end Coarsening

end CoarseAssembly.Analytic

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_Assembly
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Compatible analytic indices and their coarsening limit

The scale-index homomorphisms and their compatibility are the precise
published input from Willett--Yu, *Higher Index Theory*, §§5.1, 6.7, 7.1--7.2
(with errata 30--31). Their source is the Fredholm-module group of the actual
C₀ algebra; their target is the topological K₁ of the actual nonunital algebra.
The induced coarse map is constructed here by the universal property of the
direct limit. No geometric detection, filling or transfer conclusion is part
of this input.
-/

noncomputable section

namespace CoarseAssembly.Analytic

universe u v

namespace CoarseningMorphism

variable {C D : Coarsening.{u}}

theorem pushforward_compatible (f : CoarseningMorphism C D) (r s : ℕ) (h : r ≤ s) :
    (pushforward (f.atScale s)).comp (C.map r s h) =
      (D.map r s h).comp (pushforward (f.atScale r)) := by
  change (pushforward (f.atScale s)).comp (pushforward (C.inclusion r s h)) =
    (pushforward (D.inclusion r s h)).comp (pushforward (f.atScale r))
  rw [← pushforward_comp, ← pushforward_comp, f.compatible]

def homologyMap (f : CoarseningMorphism C D) : C.Homology →+ D.Homology :=
  AddCommGroup.DirectLimit.map (fun r => pushforward (f.atScale r))
    f.pushforward_compatible

@[simp] theorem homologyMap_of (f : CoarseningMorphism C D) (r : ℕ)
    (a : LocallyFiniteK1 (C.space r)) :
    f.homologyMap (C.of r a) = D.of r (pushforward (f.atScale r) a) :=
  AddCommGroup.DirectLimit.map_apply_of _ _ _

end CoarseningMorphism

namespace CompatibleIndexFamily

variable {C D : Coarsening.{u}} {A B : Type v}
variable [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]

@[simp] theorem assembly_of (I : CompatibleIndexFamily C A) (r : ℕ)
    (a : LocallyFiniteK1 (C.space r)) : I.assembly (C.of r a) = I.atScale r a :=
  AddCommGroup.DirectLimit.lift_of _ _ _ _ _

end CompatibleIndexFamily

end CoarseAssembly.Analytic

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_BlockOperators
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform block operators on Hilbert sums

The averaging operators used in the transfer act separately on finite
fibers. A uniform norm bound, rather than finiteness of the set of fibers,
makes their direct sum a bounded operator. The resulting operator admits the uniform approximation needed for the
fiber projection.
-/

noncomputable section

namespace CoarseAssembly

open Filter
open scoped Topology

variable {ι : Type*} {E F : ι → Type*}
variable [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℂ (E i)]
variable [∀ i, NormedAddCommGroup (F i)] [∀ i, NormedSpace ℂ (F i)]

@[simp] theorem blockOperator_apply (A : ∀ i, E i →L[ℂ] F i) (C : ℝ) (hC : 0 ≤ C)
    (hA : ∀ i, ‖A i‖ ≤ C) (x : lp E 2) (i : ι) :
    blockOperator A C hC hA x i = A i (x i) := rfl

end CoarseAssembly

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_HilbertSum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Flattening the Hilbert sum of the finite fibers

The transfer is naturally constructed as a block operator. Flattening its
Hilbert sum identifies it isometrically with the ordinary Roe module on
the sigma type of vertices. Both directions and the norm identity are
constructed from summability of squared norms.
-/

noncomputable section

namespace CoarseAssembly

variable {ι : Type*} {Q : ι → Type*} {H : Type*}
variable [NormedAddCommGroup H] [NormedSpace ℂ H]

theorem l2_norm_sq {J : Type*} {E : J → Type*} [∀ j, NormedAddCommGroup (E j)]
    (x : lp E 2) : ‖x‖ ^ 2 = ∑' j, ‖x j‖ ^ 2 := by
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
    lp.norm_rpow_eq_tsum (p := 2) (by norm_num) x

theorem l2_summable_sq {J : Type*} {E : J → Type*} [∀ j, NormedAddCommGroup (E j)]
    (x : lp E 2) : Summable (fun j => ‖x j‖ ^ 2) := by
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
    (lp.memℓp x).summable (by norm_num : 0 < (2 : ENNReal).toReal)

end CoarseAssembly

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_BilateralShift
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The separable Hilbert space and bilateral shift for the circle cycle -/

noncomputable section

namespace CoarseAssembly.Analytic

open TopologicalSpace

abbrev CircleSequence := lp (fun _ : ℤ => ℂ) 2

instance circleSequence_secondCountable : SecondCountableTopology CircleSequence := by
  let b : HilbertBasis ℤ ℂ CircleSequence := default
  have hs := ((Set.countable_range b).isSeparable.span (R := ℂ)).closure
  change TopologicalSpace.IsSeparable
    ((Submodule.span ℂ (Set.range b)).topologicalClosure : Set CircleSequence) at hs
  rw [b.dense_span] at hs
  have : SeparableSpace CircleSequence := TopologicalSpace.isSeparable_univ_iff.mp hs
  infer_instance

abbrev circleSequenceSpace : HilbertSpace where
  Carrier := CircleSequence
  normed := inferInstance
  inner := inferInstance
  complete := inferInstance
  secondCountable := inferInstance

/-- Reindex square-summable integer sequences by a permutation. -/
def reindexSequence (e : ℤ ≃ ℤ) (x : CircleSequence) : CircleSequence :=
  ⟨fun n => x (e.symm n), by
    apply memℓp_gen
    simp only [ENNReal.toReal_ofNat, Real.rpow_two]
    exact e.symm.summable_iff.mpr (CoarseAssembly.l2_summable_sq x)⟩

theorem reindexSequence_norm (e : ℤ ≃ ℤ) (x : CircleSequence) : ‖reindexSequence e x‖ = ‖x‖ := by
  have he : ‖reindexSequence e x‖ ^ 2 = ‖x‖ ^ 2 := by
    rw [CoarseAssembly.l2_norm_sq, CoarseAssembly.l2_norm_sq]
    exact e.symm.tsum_eq (fun n => ‖x n‖ ^ 2)
  nlinarith [norm_nonneg x, norm_nonneg (reindexSequence e x)]

def reindexSequenceEquiv (e : ℤ ≃ ℤ) : CircleSequence ≃ₗᵢ[ℂ] CircleSequence where
  toFun := reindexSequence e
  invFun := reindexSequence e.symm
  left_inv x := by apply lp.ext; funext n; simp [reindexSequence]
  right_inv x := by apply lp.ext; funext n; simp [reindexSequence]
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  norm_map' := reindexSequence_norm e

/-- The shift sends the basis vector at `n` to the basis vector at `n+1`. -/
def bilateralShiftEquiv : CircleSequence ≃ₗᵢ[ℂ] CircleSequence :=
  reindexSequenceEquiv (Equiv.addRight 1)

def bilateralShift : End circleSequenceSpace := (bilateralShiftEquiv : CircleSequence →L[ℂ] CircleSequence)

@[simp] theorem bilateralShift_apply (x : CircleSequence) (n : ℤ) :
    bilateralShift x n = x (n - 1) := rfl

end CoarseAssembly.Analytic

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_BinaryHilbertSum
attribute [-simp] _root_.OAI.CoarseAssembly.Analytic.bilateralShift_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Concrete binary sums of the Hilbert spaces of analytic cycles -/

noncomputable section

namespace CoarseAssembly.Analytic

universe u

abbrev binaryHilbertSpace (H K : HilbertSpace.{u}) : HilbertSpace.{u} where
  Carrier := WithLp 2 (H × K)
  normed := inferInstance
  inner := inferInstance
  complete := inferInstance
  secondCountable := inferInstance

variable (H K : HilbertSpace.{u})

def binaryLeft : H →ₗᵢ[ℂ] binaryHilbertSpace H K where
  toFun x := WithLp.toLp 2 (x, 0)
  map_add' _ _ := by simp [← WithLp.toLp_add]
  map_smul' _ _ := by simp [← WithLp.toLp_smul]
  norm_map' x := WithLp.norm_toLp_fst 2 H K x

def binaryRight : K →ₗᵢ[ℂ] binaryHilbertSpace H K where
  toFun x := WithLp.toLp 2 (0, x)
  map_add' _ _ := by simp [← WithLp.toLp_add]
  map_smul' _ _ := by simp [← WithLp.toLp_smul]
  norm_map' x := WithLp.norm_toLp_snd 2 H K x

@[simp] theorem binaryLeft_adjoint :
    (binaryLeft H K).toContinuousLinearMap.adjoint = WithLp.fstL 2 ℂ H K := by
  apply ContinuousLinearMap.ext
  intro x
  apply ext_inner_left ℂ
  intro y
  rw [ContinuousLinearMap.adjoint_inner_right]
  simp [binaryLeft, WithLp.prod_inner_apply]

@[simp] theorem binaryRight_adjoint :
    (binaryRight H K).toContinuousLinearMap.adjoint = WithLp.sndL 2 ℂ H K := by
  apply ContinuousLinearMap.ext
  intro x
  apply ext_inner_left ℂ
  intro y
  rw [ContinuousLinearMap.adjoint_inner_right]
  simp [binaryRight, WithLp.prod_inner_apply]

/-- Block diagonal operators, on the actual Hilbert sum. -/
def binaryBlock (T : End H) (S : End K) : End (binaryHilbertSpace H K) :=
  operatorConjugation (binaryLeft H K) T + operatorConjugation (binaryRight H K) S

@[simp] theorem binaryBlock_apply (T : End H) (S : End K)
    (x : binaryHilbertSpace H K) :
    binaryBlock H K T S x = WithLp.toLp 2 (T x.fst, S x.snd) := by
  unfold binaryBlock operatorConjugation
  rw [binaryLeft_adjoint, binaryRight_adjoint]
  apply (WithLp.ofLp_injective 2)
  simp [binaryLeft, binaryRight]

@[simp] theorem binaryBlock_one : binaryBlock H K 1 1 = 1 := by
  ext x
  rw [binaryBlock_apply H K]
  rfl

@[simp] theorem binaryBlock_zero : binaryBlock H K 0 0 = 0 := by
  ext x
  rw [binaryBlock_apply H K]
  rfl

theorem binaryBlock_star (T : End H) (S : End K) :
    binaryBlock H K (star T) (star S) = star (binaryBlock H K T S) := by
  simp only [binaryBlock, star_add, ← operatorConjugation_star]

end CoarseAssembly.Analytic

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_CayleyBoundary
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A rational representative of the odd analytic boundary

For a self-adjoint `F`, the square of its Cayley transform, with a minus sign,
equals one modulo the square defect `F² - 1`. This construction will be applied
to the Roe ideal in the controlled pseudolocal algebra.
-/

noncomputable section

namespace CoarseAssembly.Analytic

variable {A : Type*} [CStarAlgebra A]

theorem selfAdjoint_add_I_isUnit (F : A) (hF : IsSelfAdjoint F) :
    IsUnit (F + algebraMap ℂ A Complex.I) := by
  have hn : -Complex.I ∉ spectrum ℂ F := by
    intro h
    have hi := hF.im_eq_zero_of_mem_spectrum h
    simp at hi
  have hu : IsUnit (algebraMap ℂ A (-Complex.I) - F) :=
    not_not.mp (fun h => hn (spectrum.mem_iff.mpr h))
  convert hu.neg using 1
  all_goals try with_reducible_and_instances rfl
  simp only [map_neg, neg_sub, sub_neg_eq_add]

@[simp] theorem cayleyDenominator_val (F : A) (hF : IsSelfAdjoint F) :
    (cayleyDenominator F hF : A) = F + algebraMap ℂ A Complex.I :=
  (selfAdjoint_add_I_isUnit F hF).unit_spec

theorem cayleyDenominator_star (F : A) (hF : IsSelfAdjoint F) :
    star (cayleyDenominator F hF : A) = F - algebraMap ℂ A Complex.I := by
  rw [cayleyDenominator_val, star_add, hF.star_eq]
  simp only [← algebraMap_star_comm, Complex.star_def, Complex.conj_I, map_neg,
    sub_eq_add_neg]

theorem cayleyDenominator_normal (F : A) (hF : IsSelfAdjoint F) :
    Commute (star (cayleyDenominator F hF : A)) (cayleyDenominator F hF : A) := by
  rw [cayleyDenominator_star, cayleyDenominator_val]
  have hc : Commute (algebraMap ℂ A Complex.I) F := Algebra.commutes _ _
  exact ((Commute.refl F).sub_left hc).add_right
    (hc.symm.sub_left (Commute.refl _))

@[simp] theorem cayleyUnitary_val (F : A) (hF : IsSelfAdjoint F) :
    (cayleyUnitary F hF : A) =
      star (cayleyDenominator F hF : A) * (↑(cayleyDenominator F hF)⁻¹ : A) := rfl

end CoarseAssembly.Analytic

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_CayleyContinuity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Norm continuity of the rational boundary representative -/

noncomputable section

namespace CoarseAssembly.Analytic

variable {A P : Type*} [CStarAlgebra A] [TopologicalSpace P]

theorem continuous_cayleyDenominator (F : P → A) (hF : ∀ p, IsSelfAdjoint (F p))
    (hcont : Continuous F) : Continuous (fun p => cayleyDenominator (F p) (hF p)) := by
  apply (Units.isOpenEmbedding_val (R := A)).isEmbedding.continuous_iff.mpr
  simp only [Function.comp_def, cayleyDenominator_val]
  convert! hcont.add (continuous_const : Continuous (fun _ : P => algebraMap ℂ A Complex.I))

theorem continuous_cayleyUnitary (F : P → A) (hF : ∀ p, IsSelfAdjoint (F p))
    (hcont : Continuous F) : Continuous (fun p => (cayleyUnitary (F p) (hF p) : A)) := by
  have hb := continuous_cayleyDenominator F hF hcont
  simp only [cayleyUnitary_val]
  exact (Units.continuous_val.comp hb).star.mul (Units.continuous_coe_inv.comp hb)

end CoarseAssembly.Analytic

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_BoundedTransform
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A continuous bounded transform of self-adjoint Fredholm operators

The imaginary part of the Cayley transform is the rational function
`2x / (1 + x²)`. It is contractive and varies continuously even when the
original family has no uniform norm bound.
-/

noncomputable section

namespace CoarseAssembly.Analytic

variable {A : Type*} [CStarAlgebra A]

theorem continuous_boundedTransform {T : Type*} [TopologicalSpace T]
    (F : T → A) (hF : ∀ t, IsSelfAdjoint (F t)) (hc : Continuous F) :
    Continuous (fun t => boundedTransform (F t) (hF t)) := by
  have hu := continuous_cayleyUnitary F hF hc
  exact continuous_const.smul (hu.sub hu.star)

end CoarseAssembly.Analytic

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_BoundedTransformCompact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The bounded transform changes a unital Fredholm operator compactly -/

noncomputable section

namespace CoarseAssembly.Analytic

variable {A : Type*} [CStarAlgebra A]

theorem cayleyDenominator_normSquare (F : A) (hF : IsSelfAdjoint F) :
    (cayleyDenominator F hF : A) * star (cayleyDenominator F hF : A) = F * F + 1 := by
  rw [cayleyDenominator_star, cayleyDenominator_val]
  have hi : algebraMap ℂ A Complex.I * algebraMap ℂ A Complex.I = -1 := by
    rw [← map_mul, Complex.I_mul_I, map_neg, map_one]
  have hc := Algebra.commutes (R := ℂ) (A := A) Complex.I F
  noncomm_ring [hc, hi]

theorem cayleyUnitary_mul_normSquare (F : A) (hF : IsSelfAdjoint F) :
    (cayleyUnitary F hF : A) *
      ((cayleyDenominator F hF : A) * star (cayleyDenominator F hF : A)) =
      star (cayleyDenominator F hF : A) * star (cayleyDenominator F hF : A) := by
  rw [cayleyUnitary_val]
  calc
    _ = star (cayleyDenominator F hF : A) *
        (((↑(cayleyDenominator F hF)⁻¹ : A) * (cayleyDenominator F hF : A)) *
          star (cayleyDenominator F hF : A)) := by noncomm_ring
    _ = _ := by rw [Units.inv_mul, one_mul]

theorem star_cayleyUnitary_mul_normSquare (F : A) (hF : IsSelfAdjoint F) :
    star (cayleyUnitary F hF : A) *
      ((cayleyDenominator F hF : A) * star (cayleyDenominator F hF : A)) =
      (cayleyDenominator F hF : A) * (cayleyDenominator F hF : A) := by
  let b := cayleyDenominator F hF
  have hc : Commute (b : A) (star (b : A)) := (cayleyDenominator_normal F hF).symm
  rw [cayleyUnitary_val, star_mul, star_star, ← Units.coe_star_inv]
  change ((↑(star b)⁻¹ : A) * (b : A)) * ((b : A) * star (b : A)) = (b : A) * (b : A)
  calc
    _ = (↑(star b)⁻¹ : A) * ((b : A) * ((b : A) * star (b : A))) := by noncomm_ring
    _ = (↑(star b)⁻¹ : A) * ((b : A) * (star (b : A) * (b : A))) := by rw [hc.eq]
    _ = (↑(star b)⁻¹ : A) * (((b : A) * star (b : A)) * (b : A)) := by noncomm_ring
    _ = (↑(star b)⁻¹ : A) * ((star (b : A) * (b : A)) * (b : A)) := by rw [hc.eq]
    _ = ((↑(star b)⁻¹ : A) * star (b : A)) * ((b : A) * (b : A)) := by noncomm_ring
    _ = _ := by rw [← Units.coe_star, Units.inv_mul, one_mul]

theorem boundedTransform_mul_normSquare (F : A) (hF : IsSelfAdjoint F) :
    boundedTransform F hF *
      ((cayleyDenominator F hF : A) * star (cayleyDenominator F hF : A)) = (2 : ℂ) • F := by
  unfold boundedTransform
  rw [smul_mul_assoc, sub_mul, cayleyUnitary_mul_normSquare, star_cayleyUnitary_mul_normSquare]
  have hp : star (cayleyDenominator F hF : A) * star (cayleyDenominator F hF : A) -
      (cayleyDenominator F hF : A) * (cayleyDenominator F hF : A) =
      (-4 * Complex.I : ℂ) • F := by
    rw [cayleyDenominator_star, cayleyDenominator_val, Algebra.smul_def]
    simp only [map_mul, map_neg, map_ofNat]
    have hc := Algebra.commutes (R := ℂ) (A := A) Complex.I F
    noncomm_ring [hc]
  rw [hp, smul_smul]
  have hs : (Complex.I / 2) * (-4 * Complex.I) = (2 : ℂ) := by
    calc
      _ = -2 * (Complex.I * Complex.I) := by ring
      _ = 2 := by rw [Complex.I_mul_I]; norm_num
  rw [hs]

theorem boundedTransform_eq_of_involution (F : A) (hF : IsSelfAdjoint F) (hsq : F * F = 1) :
    boundedTransform F hF = F := by
  have hh := boundedTransform_mul_normSquare F hF
  rw [cayleyDenominator_normSquare, hsq, mul_add, mul_one] at hh
  have he : (2 : ℂ) • boundedTransform F hF = (2 : ℂ) • F := by
    simpa only [two_smul] using hh
  exact (smul_right_injective A (by norm_num : (2 : ℂ) ≠ 0)) he

end CoarseAssembly.Analytic

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_BoundedCycleTransform
attribute [-instance] _root_.OAI.CoarseAssembly.Analytic.Coarsening.instDirectedSystemNatLocallyFiniteK1SpaceCoeAddMonoidHomMap
attribute [-simp] _root_.OAI.CoarseAssembly.Analytic.CoarseningMorphism.homologyMap_of _root_.OAI.CoarseAssembly.Analytic.CompatibleIndexFamily.assembly_of _root_.OAI.CoarseAssembly.Analytic.bilateralShift_apply _root_.OAI.CoarseAssembly.Analytic.binaryBlock_apply _root_.OAI.CoarseAssembly.Analytic.binaryBlock_one _root_.OAI.CoarseAssembly.Analytic.binaryBlock_zero _root_.OAI.CoarseAssembly.Analytic.binaryLeft_adjoint _root_.OAI.CoarseAssembly.Analytic.binaryRight_adjoint _root_.OAI.CoarseAssembly.Analytic.pushforward_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Rational normalization of unital self-adjoint cycles and homotopies -/

noncomputable section

namespace CoarseAssembly.Analytic

variable {A : Type} [CStarAlgebra A]

def OddHomotopy.bounded (h : OddHomotopy A)
    (hπ : ∀ t, h.representation t 1 = 1) (hs : ∀ t, IsSelfAdjoint (h.operator t)) :
    OddHomotopy A where
  space := h.space
  representation := h.representation
  operator t := boundedTransform (h.operator t) (hs t)
  continuous_representation := h.continuous_representation
  continuous_operator := continuous_boundedTransform h.operator hs h.continuous_operator
  commutator_compact t a := ((h.eval t).bounded (hπ t) (hs t)).commutator_compact a
  square_compact t a := ((h.eval t).bounded (hπ t) (hs t)).square_compact a
  adjoint_compact t a := ((h.eval t).bounded (hπ t) (hs t)).adjoint_compact a

@[simp] theorem OddHomotopy.bounded_eval (h : OddHomotopy A)
    (hπ : ∀ t, h.representation t 1 = 1) (hs : ∀ t, IsSelfAdjoint (h.operator t)) (t : Interval) :
    (h.bounded hπ hs).eval t = (h.eval t).bounded (hπ t) (hs t) := rfl

end CoarseAssembly.Analytic

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_ScalarCutDown
attribute [-instance] _root_.OAI.CoarseAssembly.Analytic.Coarsening.instDirectedSystemNatLocallyFiniteK1SpaceCoeAddMonoidHomMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Cutting a scalar Fredholm operator down to its represented subspace -/

noncomputable section

namespace CoarseAssembly.Analytic

variable {H : HilbertSpace}

theorem symmetricCutDown_selfAdjoint (P F : End H) (hP : IsSelfAdjoint P) :
    IsSelfAdjoint (symmetricCutDown P F) := by
  change star ((1 / 2 : ℝ) • (P * F * P + star (P * F * P)) + (1 - P)) = _
  rw [star_add, star_smul, star_trivial, star_add, star_star, star_sub, star_one, hP.star_eq]
  rw [add_comm (star (P * F * P))]
  rfl

theorem symmetricCutDown_complement (P F : End H) (hP : IsSelfAdjoint P)
    (hPP : P * P = P) : symmetricCutDown P F * (1 - P) = 1 - P := by
  have hzero : ∀ T : End H, P * T * P * (1 - P) = 0 := by
    intro T
    rw [mul_sub, mul_one, mul_assoc (P * T) P P, hPP, sub_self]
  have hQ : (1 - P) * (1 - P) = 1 - P := by
    calc
      (1 - P) * (1 - P) = 1 - P - P + P * P := by noncomm_ring
      _ = 1 - P := by rw [hPP]; abel
  unfold symmetricCutDown
  rw [add_mul, smul_mul_assoc, add_mul, hzero F,
    star_mul, star_mul, hP.star_eq, ← mul_assoc, hzero (star F), add_zero, smul_zero, zero_add, hQ]

theorem supported_square_compact (c : OddCycle ℂ)
    (hQ : c.operator * (1 - c.representation 1) = 1 - c.representation 1) :
    IsCompactOperator (c.operator * c.operator - 1 : End c.space) := by
  have hz : (c.operator * c.operator - 1) * (1 - c.representation 1) = 0 := by
    calc
      _ = c.operator * (c.operator * (1 - c.representation 1)) -
          (1 - c.representation 1) := by noncomm_ring
      _ = 0 := by rw [hQ, hQ, sub_self]
  have he : c.operator * c.operator - 1 =
      (c.operator * c.operator - 1) * c.representation 1 := by
    exact sub_eq_zero.mp (by simpa only [mul_sub, mul_one] using hz)
  rw [he]
  exact c.square_compact 1

end CoarseAssembly.Analytic

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_RepresentedCutDown
attribute [-instance] _root_.OAI.CoarseAssembly.Analytic.Coarsening.instDirectedSystemNatLocallyFiniteK1SpaceCoeAddMonoidHomMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Cutting down arbitrary cycles over the unital coefficient algebras

The compact-source algebras used by the circle pairing are unital, although
the Fredholm representations themselves may be nonunital. Restriction to
scalar coefficients gives precisely the local estimates needed for the
represented-subspace cut-down.
-/

noncomputable section

namespace CoarseAssembly.Analytic

variable {A : Type} [CStarAlgebra A]

theorem representation_unit_selfAdjoint (c : OddCycle A) :
    IsSelfAdjoint (c.representation 1) := by
  change star (c.representation 1) = c.representation 1
  rw [← map_star, star_one]

theorem representation_unit_sq (c : OddCycle A) :
    c.representation 1 * c.representation 1 = c.representation 1 := by
  rw [← map_mul, one_mul]

theorem represented_square_compact (c : OddCycle A)
    (hQ : c.operator * (1 - c.representation 1) = 1 - c.representation 1) :
    IsCompactOperator (c.operator * c.operator - 1 : End c.space) := by
  apply supported_square_compact c.scalarRestriction
  change c.operator * (1 - c.representation (algebraMap ℂ A 1)) =
    1 - c.representation (algebraMap ℂ A 1)
  simpa only [map_one] using hQ

end CoarseAssembly.Analytic

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_ExplicitCutDown
attribute [-instance] _root_.OAI.CoarseAssembly.Analytic.Coarsening.instDirectedSystemNatLocallyFiniteK1SpaceCoeAddMonoidHomMap
attribute [-simp] _root_.OAI.CoarseAssembly.Analytic.CoarseningMorphism.homologyMap_of _root_.OAI.CoarseAssembly.Analytic.CompatibleIndexFamily.assembly_of _root_.OAI.CoarseAssembly.Analytic.OddHomotopy.bounded_eval _root_.OAI.CoarseAssembly.Analytic.bilateralShift_apply _root_.OAI.CoarseAssembly.Analytic.binaryBlock_apply _root_.OAI.CoarseAssembly.Analytic.binaryBlock_one _root_.OAI.CoarseAssembly.Analytic.binaryBlock_zero _root_.OAI.CoarseAssembly.Analytic.binaryLeft_adjoint _root_.OAI.CoarseAssembly.Analytic.binaryRight_adjoint _root_.OAI.CoarseAssembly.Analytic.pushforward_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The explicit represented-subspace cut-down cycle -/

noncomputable section

namespace CoarseAssembly.Analytic

variable {A : Type} [CStarAlgebra A]

theorem OddCycle.cutDown_operator (c : OddCycle A) :
    c.cutDown.operator = symmetricCutDown (c.representation 1) c.operator := by
  change c.operator + (symmetricCutDown (c.representation 1) c.operator - c.operator) = _
  abel

@[simp] theorem OddCycle.cutDown_representation (c : OddCycle A) :
    c.cutDown.representation = c.representation := rfl

theorem cutDown_selfAdjoint (c : OddCycle A) : IsSelfAdjoint c.cutDown.operator := by
  rw [c.cutDown_operator]
  exact symmetricCutDown_selfAdjoint _ _ (representation_unit_selfAdjoint c)

theorem cutDown_complement (c : OddCycle A) :
    c.cutDown.operator * (1 - c.cutDown.representation 1) = 1 - c.cutDown.representation 1 := by
  change (c.operator + representedCorrection c) * (1 - c.representation 1) = 1 - c.representation 1
  have he : c.operator + representedCorrection c =
      symmetricCutDown (c.representation 1) c.operator := by unfold representedCorrection; abel
  rw [he]
  exact symmetricCutDown_complement _ _ (representation_unit_selfAdjoint c) (representation_unit_sq c)

theorem cutDown_square_compact (c : OddCycle A) :
    IsCompactOperator (c.cutDown.operator * c.cutDown.operator - 1 : End c.cutDown.space) :=
  represented_square_compact c.cutDown (cutDown_complement c)

end CoarseAssembly.Analytic

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_CharacterExtension
attribute [-instance] _root_.OAI.CoarseAssembly.Analytic.Coarsening.instDirectedSystemNatLocallyFiniteK1SpaceCoeAddMonoidHomMap
attribute [-simp] _root_.OAI.CoarseAssembly.Analytic.CoarseningMorphism.homologyMap_of _root_.OAI.CoarseAssembly.Analytic.CompatibleIndexFamily.assembly_of _root_.OAI.CoarseAssembly.Analytic.OddHomotopy.bounded_eval _root_.OAI.CoarseAssembly.Analytic.bilateralShift_apply _root_.OAI.CoarseAssembly.Analytic.binaryBlock_apply _root_.OAI.CoarseAssembly.Analytic.binaryBlock_one _root_.OAI.CoarseAssembly.Analytic.binaryBlock_zero _root_.OAI.CoarseAssembly.Analytic.binaryLeft_adjoint _root_.OAI.CoarseAssembly.Analytic.binaryRight_adjoint _root_.OAI.CoarseAssembly.Analytic.pushforward_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Completing a represented subspace using a character

For a unital coefficient algebra with a character, the complement of the
represented subspace can carry that character. The cut-down operator acts
as the identity there, so this completion preserves the Fredholm defects.
-/

noncomputable section

namespace CoarseAssembly.Analytic

variable {A : Type} [CStarAlgebra A] {H : HilbertSpace}

@[simp] theorem completedRepresentation_apply (c : OddCycle A) (χ : A →⋆ₐ[ℂ] ℂ) (a : A) :
    completedRepresentation c χ a = c.representation a + χ a • (1 - c.representation 1) := rfl

theorem completedRepresentation_one (c : OddCycle A) (χ : A →⋆ₐ[ℂ] ℂ) :
    completedRepresentation c χ 1 = 1 := by
  simp only [completedRepresentation_apply, map_one, one_smul]
  abel

theorem characterExtension_unital (c : OddCycle A) (χ : A →⋆ₐ[ℂ] ℂ)
    (hF : IsSelfAdjoint c.operator)
    (hQ : c.operator * (1 - c.representation 1) = 1 - c.representation 1)
    (hsq : IsCompactOperator (c.operator * c.operator - 1 : End c.space)) :
    (c.characterExtension χ hF hQ hsq).representation 1 = 1 :=
  completedRepresentation_one c χ

end CoarseAssembly.Analytic

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_ProjectionSwap
attribute [-simp] _root_.OAI.CoarseAssembly.Analytic.OddCycle.cutDown_representation _root_.OAI.CoarseAssembly.Analytic.OddHomotopy.bounded_eval _root_.OAI.CoarseAssembly.Analytic.bilateralShift_apply _root_.OAI.CoarseAssembly.Analytic.completedRepresentation_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The unitary which exchanges complementary represented subspaces -/

noncomputable section

namespace CoarseAssembly.Analytic

variable (H : HilbertSpace)

def binaryFlip : End (binaryHilbertSpace H H) :=
  (LinearIsometryEquiv.withLpProdComm 2 ℂ H H).toContinuousLinearEquiv.toContinuousLinearMap

@[simp] theorem binaryFlip_apply (x : binaryHilbertSpace H H) :
    binaryFlip H x = WithLp.toLp 2 (x.snd, x.fst) := rfl

theorem binaryFlip_selfAdjoint : IsSelfAdjoint (binaryFlip H) := by
  change ContinuousLinearMap.adjoint
    (LinearIsometryEquiv.withLpProdComm 2 ℂ H H).toContinuousLinearEquiv.toContinuousLinearMap = _
  rw [LinearIsometryEquiv.adjoint_eq_symm]
  rfl

theorem binaryFlip_block (T : End H) :
    binaryFlip H * binaryBlock H H T T = binaryBlock H H T T * binaryFlip H := by
  apply ContinuousLinearMap.ext
  intro x
  change binaryFlip H (binaryBlock H H T T x) = binaryBlock H H T T (binaryFlip H x)
  rw [binaryBlock_apply H H, binaryFlip_apply, binaryFlip_apply, binaryBlock_apply H H]
  rfl

def projectionSwap (P : End H) : End (binaryHilbertSpace H H) :=
  binaryBlock H H P P + binaryBlock H H (1 - P) (1 - P) * binaryFlip H

@[simp] theorem projectionSwap_apply (P : End H) (x : binaryHilbertSpace H H) :
    projectionSwap H P x =
      WithLp.toLp 2 (P x.fst + (1 - P) x.snd, (1 - P) x.fst + P x.snd) := by
  change binaryBlock H H P P x + binaryBlock H H (1 - P) (1 - P) (binaryFlip H x) = _
  rw [binaryBlock_apply H H, binaryFlip_apply, binaryBlock_apply H H]
  apply (WithLp.ofLp_injective 2)
  change (P x.fst + (1 - P) x.snd, P x.snd + (1 - P) x.fst) = _
  rw [add_comm (P x.snd)]

theorem projectionSwap_selfAdjoint (P : End H) (hP : IsSelfAdjoint P) :
    IsSelfAdjoint (projectionSwap H P) := by
  change star (projectionSwap H P) = projectionSwap H P
  unfold projectionSwap
  rw [star_add, star_mul, ← binaryBlock_star, ← binaryBlock_star,
    hP.star_eq, star_sub, star_one, hP.star_eq, (binaryFlip_selfAdjoint H).star_eq,
    binaryFlip_block]

theorem projectionSwap_sq (P : End H) (hPP : P * P = P) :
    projectionSwap H P * projectionSwap H P = 1 := by
  apply ContinuousLinearMap.ext
  intro x
  change projectionSwap H P (projectionSwap H P x) = x
  rw [projectionSwap_apply H, projectionSwap_apply H]
  apply (WithLp.ofLp_injective 2)
  have hp (y : H) : P (P y) = P y := DFunLike.congr_fun hPP y
  change
    (P (P x.fst + (1 - P) x.snd) + (1 - P) ((1 - P) x.fst + P x.snd),
     (1 - P) (P x.fst + (1 - P) x.snd) + P ((1 - P) x.fst + P x.snd)) = (x.fst, x.snd)
  simp only [map_add, sub_apply, one_apply_eq_self, map_sub, hp]
  ext <;> abel_nf

def projectionSwapUnitary (P : End H) (hP : IsStarProjection P) :
    binaryHilbertSpace H H ≃ₗᵢ[ℂ] binaryHilbertSpace H H :=
  Unitary.linearIsometryEquiv ⟨projectionSwap H P, by
    rw [Unitary.mem_iff, (projectionSwap_selfAdjoint H P hP.isSelfAdjoint).star_eq]
    exact ⟨projectionSwap_sq H P hP.isIdempotentElem,
      projectionSwap_sq H P hP.isIdempotentElem⟩⟩

@[simp] theorem projectionSwapUnitary_clm (P : End H) (hP : IsStarProjection P) :
    (projectionSwapUnitary H P hP).toLinearIsometry.toContinuousLinearMap = projectionSwap H P := rfl

end CoarseAssembly.Analytic

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_CountableHilbertSum
attribute [-simp] _root_.OAI.CoarseAssembly.Analytic.OddCycle.cutDown_representation _root_.OAI.CoarseAssembly.Analytic.OddHomotopy.bounded_eval _root_.OAI.CoarseAssembly.Analytic.binaryBlock_apply _root_.OAI.CoarseAssembly.Analytic.binaryBlock_one _root_.OAI.CoarseAssembly.Analytic.binaryBlock_zero _root_.OAI.CoarseAssembly.Analytic.binaryFlip_apply _root_.OAI.CoarseAssembly.Analytic.binaryLeft_adjoint _root_.OAI.CoarseAssembly.Analytic.binaryRight_adjoint _root_.OAI.CoarseAssembly.Analytic.completedRepresentation_apply _root_.OAI.CoarseAssembly.Analytic.projectionSwapUnitary_clm _root_.OAI.CoarseAssembly.Analytic.projectionSwap_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Separable countable sums of the Hilbert spaces in analytic cycles -/

noncomputable section

namespace CoarseAssembly.Analytic

open TopologicalSpace

variable (H : ℕ → HilbertSpace)

abbrev HilbertSum := lp (fun j => H j) 2

instance hilbertSum_secondCountable : SecondCountableTopology (HilbertSum H) := by
  let v : ℕ × ℕ → HilbertSum H := fun p => lp.single 2 p.1 (denseSeq (H p.1) p.2)
  let P : Submodule ℂ (HilbertSum H) := (Submodule.span ℂ (Set.range v)).topologicalClosure
  have hc : IsClosed (P : Set (HilbertSum H)) := Submodule.isClosed_topologicalClosure _
  have hsingle (j : ℕ) (x : H j) : lp.single 2 j x ∈ P := by
    refine (denseRange_denseSeq (H j)).induction_on x
      (hc.preimage (lp.singleContinuousLinearMap ℂ (fun j => H j) 2 j).continuous) ?_
    intro n
    apply Submodule.le_topologicalClosure
    exact Submodule.subset_span ⟨(j, n), rfl⟩
  have htop : P = ⊤ := by
    apply top_unique
    intro x _
    apply hc.mem_of_tendsto (lp.hasSum_single ENNReal.ofNat_ne_top x)
    exact Filter.Eventually.of_forall (fun s => Submodule.sum_mem P (fun j _ => hsingle j (x j)))
  have hs := ((Set.countable_range v).isSeparable.span (R := ℂ)).closure
  change IsSeparable (P : Set (HilbertSum H)) at hs
  rw [htop] at hs
  have : SeparableSpace (HilbertSum H) := isSeparable_univ_iff.mp hs
  infer_instance

abbrev countableHilbertSpace : HilbertSpace where
  Carrier := HilbertSum H
  normed := inferInstance
  inner := inferInstance
  complete := inferInstance
  secondCountable := inferInstance

/-- The inclusion of an individual Hilbert summand. -/
def summandIsometry (j : ℕ) : H j →ₗᵢ[ℂ] countableHilbertSpace H where
  toFun x := lp.single (E := fun j => H j) 2 j x
  map_add' x y := lp.single_add (E := fun j => H j) 2 j x y
  map_smul' z x := by
    simpa only [RingHom.id_apply] using
      (lp.single_smul (𝕜 := ℂ) (E := fun j => H j) 2 j z x)
  norm_map' x := lp.norm_single (E := fun j => H j) (by norm_num : (0 : ENNReal) < 2) j x

@[simp] theorem summandIsometry_apply (j : ℕ) (x : H j) :
    summandIsometry H j x = lp.single (E := fun j => H j) 2 j x := rfl

end CoarseAssembly.Analytic

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_SigmaFunctionNorms
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Decay of compact-component norms for functions vanishing at infinity -/

noncomputable section

namespace CoarseAssembly.Analytic

open Topology Filter
open scoped ZeroAtInfty

variable (Y : ℕ → Type) [∀ j, TopologicalSpace (Y j)] [∀ j, CompactSpace (Y j)]

def sigmaFunctionRestriction (j : ℕ) : C₀(Sigma Y, ℂ) →⋆ₙₐ[ℂ] C(Y j, ℂ) where
  toFun f := ⟨fun x => f ⟨j, x⟩, f.continuous.comp continuous_sigmaMk⟩
  map_zero' := by ext x; rfl
  map_add' _ _ := by ext x; rfl
  map_mul' _ _ := by ext x; rfl
  map_smul' _ _ := by ext x; rfl
  map_star' _ := by ext x; rfl

omit [∀ j, CompactSpace (Y j)] in
@[simp] theorem sigmaFunctionRestriction_apply (j : ℕ) (f : C₀(Sigma Y, ℂ)) (x : Y j) :
    sigmaFunctionRestriction Y j f x = f ⟨j, x⟩ := rfl

theorem sigmaFunctionRestriction_norm_le (j : ℕ) (f : C₀(Sigma Y, ℂ)) :
    ‖sigmaFunctionRestriction Y j f‖ ≤ ‖f‖ := by
  apply (ContinuousMap.norm_le _ (norm_nonneg f)).mpr
  intro x
  exact f.toBCF.norm_coe_le_norm ⟨j, x⟩

end CoarseAssembly.Analytic

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_SigmaCycleRepresentation
attribute [-simp] _root_.OAI.CoarseAssembly.Analytic.CoarseningMorphism.homologyMap_of _root_.OAI.CoarseAssembly.Analytic.CompatibleIndexFamily.assembly_of _root_.OAI.CoarseAssembly.Analytic.OddCycle.cutDown_representation _root_.OAI.CoarseAssembly.Analytic.OddHomotopy.bounded_eval _root_.OAI.CoarseAssembly.Analytic.binaryBlock_apply _root_.OAI.CoarseAssembly.Analytic.binaryBlock_one _root_.OAI.CoarseAssembly.Analytic.binaryBlock_zero _root_.OAI.CoarseAssembly.Analytic.binaryFlip_apply _root_.OAI.CoarseAssembly.Analytic.binaryLeft_adjoint _root_.OAI.CoarseAssembly.Analytic.binaryRight_adjoint _root_.OAI.CoarseAssembly.Analytic.completedRepresentation_apply _root_.OAI.CoarseAssembly.Analytic.projectionSwapUnitary_clm _root_.OAI.CoarseAssembly.Analytic.projectionSwap_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Block representations of a countable compact family -/

noncomputable section

namespace CoarseAssembly.Analytic

open scoped ZeroAtInfty CStarAlgebra

variable (Y : ℕ → Type) [∀ j, TopologicalSpace (Y j)] [∀ j, CompactSpace (Y j)]
variable (c : ∀ j, OddCycle C(Y j, ℂ))

abbrev cycleHilbertFamily (j : ℕ) : HilbertSpace := (c j).space

theorem sigmaRepresentation_block_bound (f : C₀(Sigma Y, ℂ)) (j : ℕ) :
    ‖(c j).representation (sigmaFunctionRestriction Y j f)‖ ≤ ‖f‖ :=
  (NonUnitalStarAlgHom.norm_apply_le _ _).trans (sigmaFunctionRestriction_norm_le Y j f)

def sigmaRepresentationOperator (f : C₀(Sigma Y, ℂ)) :
    End (countableHilbertSpace (cycleHilbertFamily Y c)) :=
  CoarseAssembly.blockOperator (fun j => (c j).representation (sigmaFunctionRestriction Y j f))
    ‖f‖ (norm_nonneg f) (sigmaRepresentation_block_bound Y c f)

@[simp] theorem sigmaRepresentationOperator_apply (f : C₀(Sigma Y, ℂ))
    (x : HilbertSum (cycleHilbertFamily Y c)) (j : ℕ) :
    sigmaRepresentationOperator Y c f x j = (c j).representation (sigmaFunctionRestriction Y j f) (x j) := rfl

end CoarseAssembly.Analytic

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_ContinuousUnitalization
attribute [-simp] _root_.OAI.CoarseAssembly.Analytic.CoarseningMorphism.homologyMap_of _root_.OAI.CoarseAssembly.Analytic.CompatibleIndexFamily.assembly_of
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A path-compatible unital self-adjoint representative -/

noncomputable section

namespace CoarseAssembly.Analytic

variable {A : Type} [CStarAlgebra A]

theorem OddCycle.unitalSelfAdjoint_unital (c : OddCycle A) (χ : A →⋆ₐ[ℂ] ℂ) :
    (c.unitalSelfAdjoint χ).representation 1 = 1 :=
  characterExtension_unital c.cutDown χ (cutDown_selfAdjoint c) (cutDown_complement c)
    (cutDown_square_compact c)

theorem OddCycle.unitalSelfAdjoint_selfAdjoint (c : OddCycle A) (χ : A →⋆ₐ[ℂ] ℂ) :
    IsSelfAdjoint (c.unitalSelfAdjoint χ).operator := cutDown_selfAdjoint c

theorem OddCycle.unitalSelfAdjoint_operator (c : OddCycle A) (χ : A →⋆ₐ[ℂ] ℂ) :
    (c.unitalSelfAdjoint χ).operator = symmetricCutDown (c.representation 1) c.operator :=
  c.cutDown_operator

variable {T : Type*} [TopologicalSpace T] {H : HilbertSpace}

theorem continuous_symmetricCutDown (P F : T → End H)
    (hP : Continuous P) (hF : Continuous F) :
    Continuous (fun t => symmetricCutDown (P t) (F t)) := by
  unfold symmetricCutDown
  fun_prop

def OddHomotopy.unitalSelfAdjoint (h : OddHomotopy A) (χ : A →⋆ₐ[ℂ] ℂ) : OddHomotopy A where
  space := h.space
  representation t := ((h.eval t).unitalSelfAdjoint χ).representation
  operator t := ((h.eval t).unitalSelfAdjoint χ).operator
  continuous_representation a := by
    change Continuous (fun t => h.representation t a + χ a • (1 - h.representation t 1))
    have hp : Continuous (fun t => (1 : End h.space) - h.representation t 1) :=
      continuous_const.sub (h.continuous_representation 1)
    exact (h.continuous_representation a).add
      ((continuous_const : Continuous (fun _ : Interval => χ a)).smul hp)
  continuous_operator := by
    have hc := continuous_symmetricCutDown (fun t => h.representation t 1) h.operator
      (h.continuous_representation 1) h.continuous_operator
    exact hc.congr (fun t => ((h.eval t).unitalSelfAdjoint_operator χ).symm)
  commutator_compact t a := ((h.eval t).unitalSelfAdjoint χ).commutator_compact a
  square_compact t a := ((h.eval t).unitalSelfAdjoint χ).square_compact a
  adjoint_compact t a := ((h.eval t).unitalSelfAdjoint χ).adjoint_compact a

@[simp] theorem OddHomotopy.unitalSelfAdjoint_eval (h : OddHomotopy A) (χ : A →⋆ₐ[ℂ] ℂ)
    (t : Interval) : (h.unitalSelfAdjoint χ).eval t = (h.eval t).unitalSelfAdjoint χ := rfl

end CoarseAssembly.Analytic

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_CycleIndex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The scalar-unitary index of normalized odd cycles

This constructs the Fredholm operator and its integer index. Descent to the
cycle quotient and the explicit circle-generator calculation are separate
steps; neither is assumed by these declarations.
-/

noncomputable section

theorem _root_.ContinuousLinearEquiv.isFredholm {𝕜 E F : Type*} [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F] (e : E ≃L[𝕜] F) :
    (e : E →L[𝕜] F).IsFredholm :=
  by
  have h := (FredholmBanach.index_eq_zero_tfae (e : E →L[𝕜] F)).out 1 0
  exact (h.1 ⟨e, by rw [sub_self, ContinuousLinearMap.toLinearMap_zero, LinearMap.range_zero]; infer_instance⟩).1

theorem _root_.ContinuousLinearMap.IsFredholm.comp {𝕜 E F G : Type*} [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F]
    [NormedAddCommGroup G] [NormedSpace 𝕜 G] [CompleteSpace G]
    {u : E →L[𝕜] F} {v : F →L[𝕜] G} (hu : v.IsFredholm) (hv : u.IsFredholm) :
    (v.comp u).IsFredholm := FredholmBanach.isFredholm_comp hv hu

theorem _root_.ContinuousLinearMap.IsFredholm.index_comp {𝕜 E F G : Type*} [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F]
    [NormedAddCommGroup G] [NormedSpace 𝕜 G] [CompleteSpace G]
    {u : E →L[𝕜] F} {v : F →L[𝕜] G} (hv : v.IsFredholm) (hu : u.IsFredholm) :
    (v.comp u).toLinearMap.index = v.toLinearMap.index + u.toLinearMap.index :=
  FredholmBanach.index_comp hu hv

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_RegularizedCycle
attribute [-simp] _root_.OAI.CoarseAssembly.Analytic.CoarseningMorphism.homologyMap_of _root_.OAI.CoarseAssembly.Analytic.CompatibleIndexFamily.assembly_of
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Explicit norm-one representatives compatible with analytic homotopies -/

noncomputable section

namespace CoarseAssembly.Analytic

variable {A : Type} [CStarAlgebra A]

def OddHomotopy.regularize (h : OddHomotopy A) (χ : A →⋆ₐ[ℂ] ℂ) : OddHomotopy A :=
  (h.unitalSelfAdjoint χ).bounded
    (fun t => (h.eval t).unitalSelfAdjoint_unital χ)
    (fun t => (h.eval t).unitalSelfAdjoint_selfAdjoint χ)

@[simp] theorem OddHomotopy.regularize_eval (h : OddHomotopy A) (χ : A →⋆ₐ[ℂ] ℂ) (t : Interval) :
    (h.regularize χ).eval t = (h.eval t).regularize χ := rfl

end CoarseAssembly.Analytic

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_DegenerateRegularization
attribute [-simp] _root_.OAI.CoarseAssembly.Analytic.CoarseningMorphism.homologyMap_of _root_.OAI.CoarseAssembly.Analytic.CompatibleIndexFamily.assembly_of
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The explicit cut-down of a degenerate cycle remains degenerate -/

noncomputable section

namespace CoarseAssembly.Analytic

variable {A : Type} [CStarAlgebra A] {c : OddCycle A}

theorem OddCycle.Degenerate.cutDown_operator (hc : c.Degenerate) :
    (show End c.space from c.cutDown.operator) = c.operator * c.representation 1 + (1 - c.representation 1) := by
  let P := c.representation 1
  let F := c.operator
  have hP : star P = P := (representation_unit_selfAdjoint c).star_eq
  have hPP : P * P = P := representation_unit_sq c
  have hFP : F * P = P * F := sub_eq_zero.mp (hc.1 1)
  have hstar : star F * P = F * P := by
    have hs := hc.2.2 1
    rw [sub_mul] at hs
    exact sub_eq_zero.mp hs
  have hcut : P * F * P = F * P := by rw [← hFP, mul_assoc, hPP]
  have hcuts : star (P * F * P) = F * P := by
    rw [star_mul, star_mul, hP, hstar, ← mul_assoc, hcut]
  rw [c.cutDown_operator]
  change (1 / 2 : ℝ) • (P * F * P + star (P * F * P)) + (1 - P) = F * P + (1 - P)
  rw [hcuts, hcut]
  module

theorem OddCycle.Degenerate.cutDown_square (hc : c.Degenerate) :
    c.cutDown.operator * c.cutDown.operator = 1 := by
  let P := c.representation 1
  let F := c.operator
  have hPP : P * P = P := representation_unit_sq c
  have hFP : F * P = P * F := sub_eq_zero.mp (hc.1 1)
  have hF2P : F * F * P = P := by
    have hh := hc.2.1 1
    rw [sub_mul, one_mul] at hh
    exact sub_eq_zero.mp hh
  have hcut : P * F * P = F * P := by rw [← hFP, mul_assoc, hPP]
  have hsq : (F * P) * (F * P) = P := by
    calc
      _ = F * (P * F) * P := by noncomm_ring
      _ = F * (F * P) * P := by rw [← hFP]
      _ = (F * F) * (P * P) := by noncomm_ring
      _ = P := by rw [hPP, hF2P]
  have hright : F * P * (1 - P) = 0 := by rw [mul_sub, mul_one, mul_assoc, hPP, sub_self]
  have hleft : (1 - P) * (F * P) = 0 := by rw [sub_mul, one_mul, ← mul_assoc, hcut, sub_self]
  let G : End c.space := c.cutDown.operator
  have hG : G = F * P + (1 - P) := hc.cutDown_operator
  change G * G = 1
  rw [hG]
  rw [add_mul, mul_add, mul_add, hsq, hright, hleft]
  noncomm_ring [hPP]

theorem OddCycle.Degenerate.cutDown_commutator (hc : c.Degenerate) (a : A) :
    (show End c.space from c.cutDown.operator) * c.representation a -
      c.representation a * (show End c.space from c.cutDown.operator) = 0 := by
  let P := c.representation 1
  let F := c.operator
  let R := c.representation a
  let G : End c.space := c.cutDown.operator
  have hG : G = F * P + (1 - P) := hc.cutDown_operator
  have hPR : P * R = R := by dsimp [P, R]; rw [← map_mul, one_mul]
  have hRP : R * P = R := by dsimp [P, R]; rw [← map_mul, mul_one]
  have hFR : F * R = R * F := sub_eq_zero.mp (hc.1 a)
  have hleft : (F * P + (1 - P)) * R = F * R := by
    rw [add_mul, mul_assoc, hPR, sub_mul, one_mul, hPR, sub_self, add_zero]
  have hright : R * (F * P + (1 - P)) = F * R := by
    rw [mul_add, ← mul_assoc, ← hFR, mul_assoc, hRP, mul_sub, mul_one, hRP,
      sub_self, add_zero]
  change G * R - R * G = 0
  rw [hG, hleft, hright, sub_self]

theorem OddCycle.Degenerate.unitalSelfAdjoint (hc : c.Degenerate) (χ : A →⋆ₐ[ℂ] ℂ) :
    (c.unitalSelfAdjoint χ).Degenerate := by
  let G : End c.space := c.cutDown.operator
  let ρ : A →⋆ₙₐ[ℂ] End c.space := (c.unitalSelfAdjoint χ).representation
  have hG : IsSelfAdjoint G := cutDown_selfAdjoint c
  have hQ : G * (1 - c.representation 1) = 1 - c.representation 1 := cutDown_complement c
  have hQ' : (1 - c.representation 1) * G = 1 - c.representation 1 := by
    have hh := congrArg star hQ
    simpa only [star_mul, star_sub, star_one, hG.star_eq,
      (representation_unit_selfAdjoint c).star_eq] using hh
  change (∀ a, G * ρ a - ρ a * G = 0) ∧
    (∀ a, (G * G - 1) * ρ a = 0) ∧ (∀ a, (star G - G) * ρ a = 0)
  refine ⟨?_, ?_, ?_⟩
  · intro a
    change G * (c.representation a + χ a • (1 - c.representation 1)) -
      (c.representation a + χ a • (1 - c.representation 1)) * G = 0
    rw [mul_add, add_mul, mul_smul_comm, smul_mul_assoc, hQ, hQ', add_sub_add_right_eq_sub]
    exact hc.cutDown_commutator a
  · intro a
    have hsq : G * G = 1 := hc.cutDown_square
    rw [hsq, sub_self, zero_mul]
  · intro a
    rw [hG.star_eq, sub_self, zero_mul]

theorem OddCycle.Degenerate.bounded (hc : c.Degenerate)
    (hπ : c.representation 1 = 1) (hs : IsSelfAdjoint c.operator) :
    (c.bounded hπ hs).Degenerate := by
  have hsq : c.operator * c.operator = 1 := by
    have hh := hc.2.1 1
    rw [hπ, mul_one] at hh
    exact sub_eq_zero.mp hh
  change (∀ a, boundedTransform c.operator hs * c.representation a -
      c.representation a * boundedTransform c.operator hs = 0) ∧
    (∀ a, (boundedTransform c.operator hs * boundedTransform c.operator hs - 1) * c.representation a = 0) ∧
    (∀ a, (star (boundedTransform c.operator hs) - boundedTransform c.operator hs) * c.representation a = 0)
  rw [boundedTransform_eq_of_involution c.operator hs hsq]
  exact hc

theorem OddCycle.Degenerate.regularize (hc : c.Degenerate) (χ : A →⋆ₐ[ℂ] ℂ) :
    (c.regularize χ).Degenerate :=
  (hc.unitalSelfAdjoint χ).bounded (c.unitalSelfAdjoint_unital χ)
    (c.unitalSelfAdjoint_selfAdjoint χ)

end CoarseAssembly.Analytic

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_FiberDegree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A uniform degree bound for the finite fibered graphs

A neighbor is encoded by its base vertex, one integral left move, and nine
binary digits. The digits distinguish children in a successive congruence
fiber; at equal or smaller depth the reduced equation already determines
the target. The resulting bound is independent of the disc radius.
-/

noncomputable section

namespace CoarseAssembly

open Congruence

abbrev FiberBits := Fin 3 → Fin 3 → Fin 2

end CoarseAssembly

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_HomotopyFilling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The precise homotopy and odd-coefficient inputs for filling

Blackadar, *K-Theory for Operator Algebras*, 2nd ed. (1998), Proposition
17.9.1 and §19.8.3 give homotopy invariance in the first variable and
`KK₁(ℂ, ℂ) = 0`. Their required specializations are explicit below.
Vanishing for a compact contractible space, and then for its countable
family, is derived rather than assumed.
-/

noncomputable section

namespace CoarseAssembly.Analytic

open unitInterval

/-- Actual continuous contraction data; this contains no K-theory assertion. -/
structure CompactContraction (X : Type) [TopologicalSpace X] where
  center : X
  homotopy : (ContinuousMap.id X).Homotopy (ContinuousMap.const X center)

end CoarseAssembly.Analytic

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_IndexFamilyTransport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Transport of a proved compatible analytic index family -/

noncomputable section

namespace CoarseAssembly.Analytic.CompatibleIndexFamily

universe u v

variable {C D : Coarsening.{u}} {A B : Type v}
  [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]

/-- Apply an actual homomorphism to the target of every scale index. -/
def mapTarget (I : CompatibleIndexFamily C A) (φ : A →⋆ₙₐ[ℂ] B) :
    CompatibleIndexFamily C B where
  atScale r := (OperatorKTheory.map φ).comp (I.atScale r)
  compatible r s hrs a := by
    change OperatorKTheory.map φ (I.atScale s (C.map r s hrs a)) = _
    rw [I.compatible]
    rfl

end CoarseAssembly.Analytic.CompatibleIndexFamily

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_OrthogonalBlock
attribute [-instance] _root_.OAI.CoarseAssembly.Analytic.Coarsening.instDirectedSystemNatLocallyFiniteK1SpaceCoeAddMonoidHomMap _root_.OAI.CoarseAssembly.Analytic.hilbertSum_secondCountable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The operator algebra of an orthogonal direct sum -/

noncomputable section

namespace CoarseAssembly.Analytic

variable {A : Type} [NonUnitalCStarAlgebra A] {c d e : OddCycle A}

def OddCycle.IsDirectSum.block (h : c.IsDirectSum d e) (T : End c.space) (S : End d.space) :
    End e.space := operatorConjugation h.left T + operatorConjugation h.right S

theorem OddCycle.IsDirectSum.cross_left (h : c.IsDirectSum d e) (T : End c.space) (S : End d.space) :
    operatorConjugation h.left T * operatorConjugation h.right S = 0 := by
  apply ContinuousLinearMap.ext
  intro x
  change h.left (T (h.left.toContinuousLinearMap.adjoint
    (h.right (S (h.right.toContinuousLinearMap.adjoint x))))) = 0
  have hz := DFunLike.congr_fun h.orthogonal (S (h.right.toContinuousLinearMap.adjoint x))
  change h.left.toContinuousLinearMap.adjoint (h.right (S (h.right.toContinuousLinearMap.adjoint x))) = 0 at hz
  rw [hz, map_zero, map_zero]

end CoarseAssembly.Analytic

end

end OAI
end


