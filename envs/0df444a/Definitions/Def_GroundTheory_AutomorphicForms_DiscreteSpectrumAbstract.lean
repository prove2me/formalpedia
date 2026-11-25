-- Prove2me | Definitions.Def_GroundTheory_AutomorphicForms_DiscreteSpectrumAbstract
-- name    : GroundTheory_AutomorphicForms_DiscreteSpectrumAbstract
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-25T00:24:32.099204+00:00
-- url     : https://prove2.me/theorems/649322d6-48a9-48b0-adf6-992e9308278a
-- title:
--   Discrete Spectrum Abstract
-- statement:
--   Definitions and structural lemmas for Discrete Spectrum Abstract, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/DiscreteSpectrumAbstract.lean

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_UnitaryRepresentations
import Theorems.Thm_GroundTheory_Automorphic_UnitaryRep_IsInvariant_topologicalClosure

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace GroundTheory.Automorphic
namespace UnitaryRep
open MeasureTheory Filter Topology Module End
open scoped InnerProductSpace ComplexConjugate
open ContinuousLinearMap
noncomputable section
variable {G : Type*} [Group G] [TopologicalSpace G] [MeasurableSpace G] [OpensMeasurableSpace G]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
def ccToL1 (μ : Measure G) [IsFiniteMeasureOnCompacts μ]
    (f : CompactlySupportedContinuousMap G ℂ) : G →₁[μ] ℂ :=
  (f.continuous.memLp_of_hasCompactSupport (μ := μ) (p := 1) f.hasCompactSupport).toLp f
def absSqOp (π : UnitaryRep G H) (μ : Measure G) (f : G →₁[μ] ℂ) : H →L[ℂ] H :=
  adjoint (π.integrated μ f) ∘L π.integrated μ f
variable (π : UnitaryRep G H) (μ : Measure G)
theorem IsCompactOperator.absSqOp {f : G →₁[μ] ℂ} (hf : IsCompactOperator (π.integrated μ f)) :
    IsCompactOperator (π.absSqOp μ f) :=
  hf.clm_comp (adjoint (π.integrated μ f))
variable {π μ}
def IsMinimal (π : UnitaryRep G H) (V : Submodule ℂ H) : Prop :=
  IsClosed (V : Set H) ∧ π.IsInvariant V ∧ V ≠ ⊥ ∧
    ∀ U : Submodule ℂ H, IsClosed (U : Set H) → π.IsInvariant U → U ≤ V → U = ⊥ ∨ U = V
def cyclicSubspace (π : UnitaryRep G H) (v : H) : Submodule ℂ H :=
  (Submodule.span ℂ (Set.range fun g => π g v)).topologicalClosure
section decomposition
variable [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G]
  [IsFiniteMeasureOnCompacts μ] [μ.IsOpenPosMeasure]
end decomposition
end
end UnitaryRep
end GroundTheory.Automorphic


