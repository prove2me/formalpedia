-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GaugeLatticeShifts_QuotIndepStmt
-- name    : Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GaugeLatticeShifts_QuotIndepStmt
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T06:24:30.044805+00:00
-- url     : https://prove2.me/theorems/d72b4776-4945-4035-97da-3828ab5f81f5
-- title:
--   Quot Indep Stmt
-- statement:
--   Definitions and structural lemmas for Quot Indep Stmt, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/ClosedLocalOrbits/GaugeLatticeShifts/QuotIndepStmt.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Measure
open scoped ENNReal
set_option linter.dupNamespace false
namespace Formalism.L2.SG.Pf.QuotIndep
def QuotIndep : Prop :=
  ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (S : Subgroup G), IsClosed (S : Set G) →
    ∀ (μS : Measure S) [μS.IsMulLeftInvariant] [μS.IsMulRightInvariant] [IsFiniteMeasureOnCompacts μS]
      [IsOpenPosMeasure μS] [SFinite μS] (μ ν₁ ν₂ : Measure G),
      (∀ f : G → ℝ≥0∞, Measurable f → ∫⁻ x, f x ∂μ = ∫⁻ x, ∫⁻ s, f ((s : G) * x) ∂μS ∂ν₁) →
      (∀ f : G → ℝ≥0∞, Measurable f → ∫⁻ x, f x ∂μ = ∫⁻ x, ∫⁻ s, f ((s : G) * x) ∂μS ∂ν₂) →
      ∀ f : G → ℝ≥0∞, Measurable f → (∀ (s : S) (x : G), f ((s : G) * x) = f x) →
        ∫⁻ x, f x ∂ν₁ = ∫⁻ x, f x ∂ν₂
end Formalism.L2.SG.Pf.QuotIndep


