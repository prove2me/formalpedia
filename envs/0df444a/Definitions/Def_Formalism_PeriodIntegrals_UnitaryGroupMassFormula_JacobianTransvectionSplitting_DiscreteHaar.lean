-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_JacobianTransvectionSplitting_DiscreteHaar
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_JacobianTransvectionSplitting_DiscreteHaar
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T01:16:46.467974+00:00
-- url     : https://prove2.me/theorems/e5d59d6b-58d1-48ef-85f3-a8b03a13ba7f
-- title:
--   Discrete Haar
-- statement:
--   Definitions and structural lemmas for Discrete Haar, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/JacobianTransvectionSplitting/DiscreteHaar.lean

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_BridgeNGLQ
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Matrix
open scoped ENNReal NNReal
namespace PI.NglqJacSplitW
open Classical in

def modF (F : Type) [Field F] [TopologicalSpace F] [IsTopologicalDivisionRing F]
    [LocallyCompactSpace F] (a : F) : ℝ≥0∞ :=
  if h : a = 0 then 0 else ((distribHaarChar F (Units.mk0 a h) : ℝ≥0) : ℝ≥0∞)
def SecCount : Prop :=
  ∀ (F : Type) [Field F] [TopologicalSpace F] [IsTopologicalDivisionRing F] [T2Space F]
    [LocallyCompactSpace F], ¬ DiscreteTopology F → SecondCountableTopology F
def DiscreteHaar : Prop :=
  ∀ (V : Type) [AddCommGroup V] [TopologicalSpace V] [DiscreteTopology V] [MeasurableSpace V]
    [BorelSpace V] (ν : Measure V), ν.IsAddHaarMeasure →
    ∀ f : V → V, Function.Injective f → ∀ S : Set V, MeasurableSet S → ν (f '' S) = ν S
def LinModulus : Prop :=
  ∀ (F : Type) [Field F] [TopologicalSpace F] [IsTopologicalDivisionRing F] [T2Space F]
    [LocallyCompactSpace F] [SecondCountableTopology F] (ι : Type) [Fintype ι] [DecidableEq ι]
    [MeasurableSpace (ι → F)] [BorelSpace (ι → F)] (M : Matrix ι ι F), M.det ≠ 0 →
    ∀ ν : Measure (ι → F), ν.IsAddHaarMeasure → ∀ S : Set (ι → F), MeasurableSet S →
      ν ((fun x => M *ᵥ x) '' S) = modF F M.det * ν S
def LinModulusV : Prop :=
  ∀ (F : Type) [Field F] [TopologicalSpace F] [IsTopologicalDivisionRing F] [T2Space F]
    [LocallyCompactSpace F] [SecondCountableTopology F]
    (V : Type) [AddCommGroup V] [Module F V] [TopologicalSpace V] [MeasurableSpace V]
    [BorelSpace V] (ι : Type) [Fintype ι] [DecidableEq ι], Nonempty (V ≃L[F] (ι → F)) →
    ∀ f : V →ₗ[F] V, LinearMap.det f ≠ 0 →
    ∀ ν : Measure V, ν.IsAddHaarMeasure → ∀ S : Set V, MeasurableSet S →
      ν (f '' S) = modF F (LinearMap.det f) * ν S
def ModOfHyp : Prop :=
  ∀ (F : Type) [Field F] [TopologicalSpace F] [IsTopologicalDivisionRing F] [T2Space F]
    [LocallyCompactSpace F] [SecondCountableTopology F] [MeasurableSpace F] [BorelSpace F]
    (a : F) (c : ℝ≥0∞), a ≠ 0 →
    (∃ μ : Measure F, μ.IsAddHaarMeasure ∧ ∀ T : Set F, MeasurableSet T →
        μ ((fun y => a * y) '' T) = c * μ T) → c = modF F a
def DiagOne : Prop :=
  ∀ (F : Type) [Field F] [TopologicalSpace F] [IsTopologicalDivisionRing F] [T2Space F]
    [LocallyCompactSpace F] [SecondCountableTopology F] (ι : Type) [Fintype ι] [DecidableEq ι]
    [MeasurableSpace (ι → F)] [BorelSpace (ι → F)] (i : ι) (a : F), a ≠ 0 →
    ∀ ν : Measure (ι → F), ν.IsAddHaarMeasure → ∀ S : Set (ι → F), MeasurableSet S →
      ν ((fun x => Function.update x i (a * x i)) '' S) = modF F a * ν S
end PI.NglqJacSplitW


