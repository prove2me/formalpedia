-- Prove2me | Definitions.Def_OAIQ229C036
-- name    : OAIQ229C036
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-11T18:07:09.210848+00:00
-- url     : https://prove2.me/theorems/b2cffab4-ddd4-4f72-9a53-6196eb8f6890
-- title:
--   Definitions bundle OAIQ229C036 of the split of OpenAI, A counterexample to the coarse Novikov conjecture (result family 307)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.CoarseAssembly.bounded_geometry_graph_counterexample_unconditional`, carved from OpenAI's openai/math development (OpenAI, *A counterexample to the coarse Novikov conjecture (result family 307)*, OpenAI Math Release, September 23, 2026, result family 307, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 4 declarations of OpenAI's Lean: 3 definitions and 1 theorem. The definitions and types are `OAI.NuclearUltrapower.SOS.ElementarySpectral.residualInE`, `OAI.NuclearUltrapower.SOS.ElementarySpectral.vectorStabilizer`, `OAI.NuclearUltrapower.SOS.basisWords`.
--
--   **Sources.** They come from these modules of lean/OAI/Topology, in whole or in part: [`CoarseAssembly_RipsFamilyInclusion`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Topology/CoarseAssembly/RipsFamilyInclusion.lean), `NuclearUltrapower_IntegerMatrices`, `NuclearUltrapower_IntegralCertificate`, `NuclearUltrapower_Kazhdan`.
--
--   **Imports.** It imports the published bundle `Def_CoarseAssembly`; the bundles `OAIQ229C032`, `OAIQ229C033` and `OAIQ229C034` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ229C044`; the statement `OAI.NuclearUltrapower.SOS.ElementarySpectral.deltaOp_certificate_ca`; the proofs of `OAI.CoarseAssembly.elementaryKernel_projection_ca`, `OAI.CoarseAssembly.publishedKazhdanInput_of_elementaryReduction_ca`, `OAI.NuclearUltrapower.SOS.ElementarySpectral.deltaOp_certificate_ca` and `OAI.NuclearUltrapower.SOS.basis_good_ca`.
-- source:
--   OpenAI, A counterexample to the coarse Novikov conjecture (result family 307), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 307; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/CoarseAssembly.lean; Apache License 2.0); definitions carved from lean/OAI/Topology at commit adc7f12

import Mathlib
import Mathlib.Algebra.Colimit.Module
import Mathlib.Algebra.Group.Commute.Units
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Floor.Semiring
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
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Analysis.Normed.Operator.Compact.Basic
import Mathlib.Analysis.Normed.Operator.Compact.FiniteDimension
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.Normed.Ring.Lemmas
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Data.Finsupp.Basic
import Mathlib.Data.Matrix.Block
import Mathlib.GroupTheory.FreeAbelianGroup
import Mathlib.GroupTheory.QuotientGroup.Defs
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.RingTheory.TwoSidedIdeal.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Module
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.Algebra.NonUnitalStarAlgebra
import Mathlib.Topology.Algebra.Ring.Basic
import Mathlib.Topology.Algebra.Support
import Mathlib.Topology.Bases
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Connected.TotallyDisconnected
import Mathlib.Topology.Constructions
import Mathlib.Topology.Instances.AddCircle.Defs
import Mathlib.Topology.Instances.AddCircle.Real
import Mathlib.Topology.Instances.Matrix
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.MetricSpace.ProperSpace
import Definitions.Def_CoarseAssembly
import Definitions.Def_OAIQ229C032
import Definitions.Def_OAIQ229C033
import Definitions.Def_OAIQ229C034

section
-- module Solutions.Q229_CA.CoarseAssembly_RipsFamilyInclusion
attribute [-instance] _root_.OAI.CoarseAssembly.Analytic.hilbertSum_secondCountable _root_.OAI.CoarseAssembly.Analytic.summandComplement_complete _root_.OAI.NuclearUltrapower.strongDualInner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Naturality of the controlled Rips boundary under component inclusions -/

noncomputable section

namespace CoarseAssembly.Rips

open Analytic DiscreteRoe

variable {Q P : ℕ → Type} [∀ i, MetricSpace (Q i)] [∀ i, MetricSpace (P i)]
  [∀ i, Fintype (Q i)] [∀ i, Fintype (P i)]
  [∀ i, DecidableEq (Q i)] [∀ i, DecidableEq (P i)] {r : ℝ}

theorem ControlledCycleFamily.boundary_included (c : ControlledCycleFamily Q r)
    (o : ∀ i, Q i) (p : ∀ i, P i) (hr : 0 ≤ r)
    (e : ∀ i, Q i ↪ P i) (hei : ∀ i x y, dist (e i x) (e i y) ≤ dist x y)
    (he : letI := separatedMetric o; letI := separatedMetric p
      ∀ x y, dist (componentEmbedding e x) (componentEmbedding e y) ≤ dist x y) :
    letI := separatedMetric o
    letI := separatedMetric p
    OperatorKTheory.map (inclusionHom (X := Sigma Q) (Y := Sigma P) (H := lp (fun _ : ℕ => ℂ) 2)
      (componentEmbedding e) he) (c.boundary o hr) =
      (c.included e hei).boundary p hr := by
  let := separatedMetric o
  let := separatedMetric p
  let d := c.included e hei
  exact separatedFamilyBoundary_inclusion o p e he
    (fun i => ampleRipsOperator r (c.cycle i) (c.unital i))
    (fun i => ampleRipsOperator r (d.cycle i) (d.unital i))
    (c.bound + 4) (d.bound + 4) (by linarith [c.bound_nonneg]) (by linarith [d.bound_nonneg])
    (fun i => (ampleRipsOperator_norm_le r (c.cycle i) (c.unital i)).trans
      (by linarith [c.norm_le i]))
    (fun i => (ampleRipsOperator_norm_le r (d.cycle i) (d.unital i)).trans
      (by linarith [d.norm_le i]))
    (r + r) (r + r) (add_nonneg hr hr) (add_nonneg hr hr)
    (fun i => ampleRipsOperator_propagation r hr (c.cycle i) (c.unital i))
    (fun i => ampleRipsOperator_propagation r hr (d.cycle i) (d.unital i))
    (fun i => ampleRipsOperator_selfAdjoint r (c.cycle i) (c.unital i) (c.selfAdjoint i))
    (fun i => ampleRipsOperator_selfAdjoint r (d.cycle i) (d.unital i) (d.selfAdjoint i))
    (fun i => ampleRipsOperator_square_compact r (c.cycle i) (c.unital i) (c.selfAdjoint i))
    (fun i => ampleRipsOperator_square_compact r (d.cycle i) (d.unital i) (d.selfAdjoint i))
    (fun i => ampleRipsOperator_inclusion r (e i) (hei i) (c.cycle i) (c.unital i))

end CoarseAssembly.Rips

end

end OAI
end

section
-- module Solutions.Q229_CA.NuclearUltrapower_IntegerMatrices
attribute [-instance] _root_.OAI.NuclearUltrapower.strongDualInner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace NuclearUltrapower.SOS

def basisWords : List (List Mat3) := [[generator0, generator5], [generator2, generator9], [generator3, generator8], [generator1, generator4], [generator0, generator0], [generator0, generator2], [generator2, generator11], [generator0, generator7], [generator4, generator0], [generator6, generator0], [generator0, generator8], [generator8, generator0], [generator0, generator10], [generator0], [generator0, generator11], [generator9, generator0], [generator0, generator9], [generator7, generator0], [generator5, generator0], [generator0, generator6], [generator3, generator10], [generator0, generator3], [generator2, generator2], [generator2, generator4], [generator4, generator2], [generator2, generator6], [generator8, generator2], [generator10, generator2], [generator2], [generator11, generator2], [generator9, generator2], [generator2, generator7], [generator5, generator2], [generator2, generator5], [generator4, generator4], [generator4, generator6], [generator6, generator9], [generator4, generator8], [generator11, generator4], [generator4, generator10], [generator4], [generator4, generator11], [generator10, generator4], [generator4, generator9], [generator7, generator8], [generator4, generator7], [generator6, generator11], [generator7, generator10], [generator6, generator6], [generator8, generator6], [generator10, generator6], [generator6], [generator11, generator6], [generator9, generator6], [generator8, generator8], [generator8, generator10], [generator8], [generator8, generator11], [generator10, generator10], [generator10], [], [generator11], [generator11, generator11], [generator9, generator10], [generator9], [generator9, generator11], [generator9, generator9], [generator8, generator7], [generator10, generator7], [generator7], [generator11, generator7], [generator9, generator7], [generator7, generator7], [generator6, generator10], [generator7, generator11], [generator6, generator8], [generator5, generator6], [generator10, generator5], [generator5, generator8], [generator5, generator10], [generator5], [generator5, generator11], [generator5, generator9], [generator11, generator5], [generator5, generator7], [generator7, generator9], [generator5, generator5], [generator4, generator3], [generator3, generator4], [generator3, generator6], [generator8, generator3], [generator10, generator3], [generator3], [generator11, generator3], [generator9, generator3], [generator3, generator7], [generator3, generator5], [generator5, generator3], [generator3, generator3], [generator1, generator6], [generator2, generator10], [generator1, generator2], [generator4, generator1], [generator6, generator1], [generator8, generator1], [generator1, generator8], [generator1, generator10], [generator1], [generator1, generator11], [generator1, generator9], [generator9, generator1], [generator7, generator1], [generator5, generator1], [generator1, generator3], [generator3, generator11], [generator1, generator7], [generator1, generator1], [generator0, generator4], [generator2, generator8], [generator3, generator9], [generator1, generator5]]

end NuclearUltrapower.SOS
end
end

end OAI
end

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

def residualInE : List (E × ℤ) := residual.map (fun p => (eInterpret p.1, p.2))

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
open scoped InnerProductSpace
namespace NuclearUltrapower.SOS.ElementarySpectral
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def vectorStabilizer (ρ : E →* (H ≃ₗᵢ[ℂ] H)) (x : H) : Subgroup E where
  carrier := {g | ρ g x = x}
  one_mem' := by simp
  mul_mem' ha hb := by
    change ρ _ x = x at ha hb ⊢
    simpa only [map_mul, LinearIsometryEquiv.coe_mul, Function.comp_apply, hb] using ha
  inv_mem' {g} hg := by
    change ρ g⁻¹ x = x
    apply (ρ g).injective
    change (ρ g * ρ g⁻¹) x = ρ g x
    rw [← map_mul, mul_inv_cancel, map_one]
    exact hg.symm

end NuclearUltrapower.SOS.ElementarySpectral
end
end

end OAI
end


