-- Prove2me | Definitions.Def_OAIQ229C037
-- name    : OAIQ229C037
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-11T16:27:09.196124+00:00
-- url     : https://prove2.me/theorems/a4722f90-1b48-4ac1-b4c0-f41f346b712f
-- title:
--   Definitions bundle OAIQ229C037 of the split of OpenAI, A counterexample to the coarse Novikov conjecture (result family 307)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.CoarseAssembly.bounded_geometry_graph_counterexample_unconditional`, carved from OpenAI's openai/math development (OpenAI, *A counterexample to the coarse Novikov conjecture (result family 307)*, OpenAI Math Release, September 23, 2026, result family 307, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 10 declarations of OpenAI's Lean: 7 definitions and 3 theorems. The definitions and types are `OAI.CoarseAssembly.elementaryLaplacian`, `OAI.CoarseAssembly.elementaryReduction`, `OAI.CoarseAssembly.elementaryRegular`, `OAI.NuclearUltrapower.Elementary.elementaryTransvection`, `OAI.NuclearUltrapower.Elementary.transvectionHom`, `OAI.NuclearUltrapower.SOS.ElementarySpectral.deltaOp`, `OAI.NuclearUltrapower.SOS.ElementarySpectral.gramOp`.
--
--   **Sources.** They come from these modules of lean/OAI/Topology, in whole or in part: [`CoarseAssembly_CongruenceSpectral`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Topology/CoarseAssembly/CongruenceSpectral.lean), [`CoarseAssembly_RegularizedRipsFamily`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Topology/CoarseAssembly/RegularizedRipsFamily.lean), `NuclearUltrapower_IntegralCertificate`, `NuclearUltrapower_Kazhdan`.
--
--   **Imports.** It imports the published bundle `Def_CoarseAssembly`; the bundle `OAIQ229C035` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ229C038`; the statements `OAI.CoarseAssembly.elementaryKernel_projection_ca`, `OAI.CoarseAssembly.publishedKazhdanInput_of_elementaryReduction_ca`, `OAI.NuclearUltrapower.SOS.ElementarySpectral.deltaOp_certificate_ca`, `OAI.NuclearUltrapower.SOS.ElementarySpectral.deltaOp_energy_ca` and `OAI.NuclearUltrapower.SOS.ElementarySpectral.deltaOp_nonneg_ca`; the proofs of `OAI.CoarseAssembly.elementaryKernel_projection_ca`, `OAI.CoarseAssembly.publishedKazhdanInput_of_elementaryReduction_ca`, `OAI.NuclearUltrapower.SOS.ElementarySpectral.deltaOp_certificate_ca`, `OAI.NuclearUltrapower.SOS.ElementarySpectral.deltaOp_energy_ca` and `OAI.NuclearUltrapower.SOS.ElementarySpectral.deltaOp_nonneg_ca`.
-- source:
--   OpenAI, A counterexample to the coarse Novikov conjecture (result family 307), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 307; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/CoarseAssembly.lean; Apache License 2.0); definitions carved from lean/OAI/Topology at commit adc7f12

import Mathlib
import Mathlib.Algebra.AlgebraicCard
import Mathlib.Algebra.Colimit.Module
import Mathlib.Algebra.Group.Commute.Units
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Order.Group.MinMax
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Star.BigOperators
import Mathlib.Algebra.Star.StarProjection
import Mathlib.Analysis.CStarAlgebra.Basic
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Range
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.CStarAlgebra.ContinuousMap
import Mathlib.Analysis.CStarAlgebra.Spectrum
import Mathlib.Analysis.CStarAlgebra.Unitization
import Mathlib.Analysis.Convex.PathConnected
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.InnerProductSpace.TensorProduct
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Analysis.Normed.Operator.Compact.Basic
import Mathlib.Analysis.Normed.Operator.Compact.FiniteDimension
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.Normed.Ring.Lemmas
import Mathlib.Analysis.Normed.Ring.Units
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Combinatorics.SimpleGraph.Walk.Decomp
import Mathlib.Data.Finset.Sigma
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
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
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
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.Algebra.Module.PerfectSpace
import Mathlib.Topology.Algebra.NonUnitalStarAlgebra
import Mathlib.Topology.Algebra.Ring.Basic
import Mathlib.Topology.Algebra.Support
import Mathlib.Topology.Baire.CompleteMetrizable
import Mathlib.Topology.Bases
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Connected.TotallyDisconnected
import Mathlib.Topology.Constructions
import Mathlib.Topology.DenseEmbedding
import Mathlib.Topology.Instances.AddCircle.Defs
import Mathlib.Topology.Instances.AddCircle.Real
import Mathlib.Topology.Instances.Matrix
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.MetricSpace.TransferInstance
import Mathlib.Topology.UniformSpace.HeineCantor
import Definitions.Def_CoarseAssembly
import Definitions.Def_OAIQ229C035

section
-- module Solutions.Q229_CA.NuclearUltrapower_IntegralCertificate
attribute [-instance] _root_.OAI.CoarseAssembly.baseUnionDecidableEq _root_.OAI.CoarseAssembly.instFintypeFiberVertex _root_.OAI.CoarseAssembly.vertexUnionDecidableEq _root_.OAI.NuclearUltrapower.strongDualInner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped InnerProductSpace ComplexOrder
namespace NuclearUltrapower.SOS.ElementarySpectral

section Hilbert
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def deltaOp (ρ : E →* (H ≃ₗᵢ[ℂ] H)) : H →L[ℂ] H :=
  eval (value (A := H →L[ℂ] H) (unitaryRep ρ)) delta

def gramOp (ρ : E →* (H ≃ₗᵢ[ℂ] H)) : H →L[ℂ] H :=
  (10 : ℤ) • gramValue (value (A := H →L[ℂ] H) (unitaryRep ρ))

end Hilbert
end NuclearUltrapower.SOS.ElementarySpectral
end
end

end OAI
end

section
-- module Solutions.Q229_CA.NuclearUltrapower_Kazhdan
attribute [-instance] _root_.OAI.CoarseAssembly.baseUnionDecidableEq _root_.OAI.CoarseAssembly.instFintypeFiberVertex _root_.OAI.CoarseAssembly.vertexUnionDecidableEq
attribute [-simp] _root_.OAI.CoarseAssembly.adjoint_apply_isometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace NuclearUltrapower.Elementary
open SOS

theorem transvection_one_mem : ∀ (i j : Fin 3) (h : i ≠ j),
    Matrix.SpecialLinearGroup.transvection h (1 : ℤ) ∈ SOS.genSet := by
  decide +kernel

def transvectionHom {i j : Fin 3} (h : i ≠ j) : Multiplicative ℤ →* SL3Z where
  toFun z := Matrix.SpecialLinearGroup.transvection h z.toAdd
  map_one' := by simp
  map_mul' a b := Matrix.SpecialLinearGroup.transvection_add h a.toAdd b.toAdd

theorem transvection_mem {i j : Fin 3} (h : i ≠ j) (k : ℤ) :
    Matrix.SpecialLinearGroup.transvection h k ∈ SOS.elementary := by
  have he : Matrix.SpecialLinearGroup.transvection h k =
      (Matrix.SpecialLinearGroup.transvection h (1:ℤ)) ^ k := by
    have hz := (transvectionHom h).map_zpow (Multiplicative.ofAdd (1:ℤ)) k
    simpa only [transvectionHom, MonoidHom.coe_mk, OneHom.coe_mk,
      toAdd_zpow, toAdd_ofAdd, zsmul_eq_mul,
      mul_one, Int.cast_id] using hz
  rw [he]
  exact SOS.elementary.zpow_mem (Subgroup.subset_closure (transvection_one_mem i j h)) k

def elementaryTransvection {i j : Fin 3} (h : i ≠ j) (k : ℤ) : SOS.E :=
  ⟨Matrix.SpecialLinearGroup.transvection h k, transvection_mem h k⟩

end NuclearUltrapower.Elementary
end
end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_CongruenceSpectral
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Applying the integral spectral certificate to the finite congruence fibers

The required gap follows from surjectivity of elementary reduction.
-/

noncomputable section

namespace CoarseAssembly

open Congruence
open NuclearUltrapower

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def elementaryReduction (k : ℕ) : SOS.E →* Congruence.Quotient k :=
  (reduce k).comp SOS.elementary.subtype

def elementaryRegular (k : ℕ) : SOS.E →*
    (lp (fun _ : Congruence.Quotient k => H) 2 ≃ₗᵢ[ℂ]
      lp (fun _ : Congruence.Quotient k => H) 2) :=
  (leftTranslationHom (H := H) (Congruence.Quotient k)).comp (elementaryReduction k)

def elementaryLaplacian (k : ℕ) :
    lp (fun _ : Congruence.Quotient k => H) 2 →L[ℂ] lp (fun _ : Congruence.Quotient k => H) 2 :=
  SOS.ElementarySpectral.deltaOp (elementaryRegular (H := H) k)

end CoarseAssembly

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_RegularizedRipsFamily
attribute [-instance] _root_.OAI.NuclearUltrapower.strongDualInner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Whole-union Roe boundaries of arbitrary families of analytic cycles -/

noncomputable section

namespace CoarseAssembly.Rips

open Analytic DiscreteRoe

variable {Q : ℕ → Type} [∀ i, MetricSpace (Q i)] [∀ i, Fintype (Q i)]
  [∀ i, DecidableEq (Q i)] {r : ℝ}

theorem regularizedFamily_homotopy
    (h : ∀ i, OddHomotopy C(Point (Q i) r, ℂ))
    (χ : ∀ i, C(Point (Q i) r, ℂ) →⋆ₐ[ℂ] ℂ)
    (o : ∀ i, Q i) (hr : 0 ≤ r) :
    (regularizedFamily (fun i => (h i).eval start) χ).boundary o hr =
      (regularizedFamily (fun i => (h i).eval finish) χ).boundary o hr := by
  let H : BoundedFamilyHomotopy Q r := {
    homotopy := fun i => (h i).regularize (χ i)
    unital := fun t i => ((h i).eval t).regularize_unital (χ i)
    selfAdjoint := fun t i => ((h i).eval t).regularize_selfAdjoint (χ i)
    bound := 1
    one_le_bound := le_rfl
    norm_le := fun t i => ((h i).eval t).regularize_norm_le (χ i) }
  exact H.endpoint_boundary_eq χ o hr

end CoarseAssembly.Rips

end

end OAI
end


