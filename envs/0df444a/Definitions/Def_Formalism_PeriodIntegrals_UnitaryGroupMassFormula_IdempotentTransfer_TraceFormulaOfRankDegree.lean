-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IdempotentTransfer_TraceFormulaOfRankDegree
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IdempotentTransfer_TraceFormulaOfRankDegree
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T04:45:41.755872+00:00
-- url     : https://prove2.me/theorems/e8f3a622-6187-4fb5-a9a1-57d4695ca868
-- title:
--   Trace Formula Of Rank Degree
-- statement:
--   Definitions and structural lemmas for Trace Formula Of Rank Degree, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/IdempotentTransfer/TraceFormulaOfRankDegree.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_DivisionRowsRationalLattice
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
def RankPart : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [NumberField.IsTotallyComplex K]
    (G : Type) [Group G] [Fintype G] (T : GoodSet K G) (P0 P : Pair K G), M1 T P0 →
    ∀ (A : Formalism.BasicNotions.HLat K) (ρ : Representation K G A.V), IsGLat A ρ →
      rkL A (cut A ρ (eps P * eG T) A.L) = rkT T P0 P A ρ
def DegPart : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [NumberField.IsTotallyComplex K]
    (G : Type) [Group G] [Fintype G] (T : GoodSet K G) (P0 P : Pair K G), M1 T P0 →
    ∀ (A : Formalism.BasicNotions.HLat K) (ρ : Representation K G A.V), IsGLat A ρ →
      |degL A (cut A ρ (eps P * eG T) A.L) -
          ∑ s, (nS T P s : ℝ) * degL A (cut A ρ (eps P0 * eS T s) A.L)| ≤
        10 * laG G * (rkT T P0 P A ρ : ℝ)
def MuPart : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [NumberField.IsTotallyComplex K]
    (G : Type) [Group G] [Fintype G] (T : GoodSet K G) (P0 P : Pair K G), M1 T P0 →
    ∀ (A : Formalism.BasicNotions.HLat K) (ρ : Representation K G A.V), IsGLat A ρ →
      (0 < rkT T P0 P A ρ →
        muMaxL A (cut A ρ (eps P * eG T) A.L) ≤ muMaxL A (cut A ρ (eps P0 * eG T) A.L) + 10 * laG G)
end PI.Dv.Tr


