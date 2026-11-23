-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IdempotentTransfer_DegTop
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IdempotentTransfer_DegTop
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T04:55:21.148749+00:00
-- url     : https://prove2.me/theorems/4ec3dd4f-3e36-4e69-aa8b-a00b2cc88482
-- title:
--   Deg Top
-- statement:
--   Definitions and structural lemmas for Deg Top, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/IdempotentTransfer/DegTop.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_DivisionRowsRationalLattice
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IdempotentTransfer_TraceFormulaOfRankDegree
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PI.Dv.Tr
open PI.Dv
def SplitBound : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [NumberField.IsTotallyComplex K]
    (G : Type) [Group G] [Fintype G] (T : GoodSet K G) (P0 P : Pair K G), M1 T P0 →
    ∀ (A : Formalism.BasicNotions.HLat K) (ρ : Representation K G A.V), IsGLat A ρ →
      |degL A (cut A ρ (eps P * eG T) A.L) - ∑ s, degL A (cut A ρ (eps P * eS T s) A.L)| ≤
        5 * laG G * (rkT T P0 P A ρ : ℝ)
def PerSBound : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [NumberField.IsTotallyComplex K]
    (G : Type) [Group G] [Fintype G] (T : GoodSet K G) (P0 P : Pair K G), M1 T P0 →
    ∀ (A : Formalism.BasicNotions.HLat K) (ρ : Representation K G A.V), IsGLat A ρ → ∀ s : T.S,
      |degL A (cut A ρ (eps P * eS T s) A.L) - (nS T P s : ℝ) * degL A (cut A ρ (eps P0 * eS T s) A.L)| ≤
        5 * laG G * ((nS T P s * rS T P0 A ρ s : ℕ) : ℝ)
end PI.Dv.Tr


