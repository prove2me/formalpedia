-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ParahoricIndexCount_Development
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ParahoricIndexCount_Development
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T04:53:43.507013+00:00
-- url     : https://prove2.me/theorems/463d4ad9-4db7-44b2-8c64-9db4f09f8cf5
-- title:
--   Development
-- statement:
--   Definitions and structural lemmas for Development, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ParahoricIndexCount/Development.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_ParahoricIdxZ
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_LemmaU
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_MeasureUniformizerMatrixSetMulCard
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_RelIndexMulMeasure
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Matrix ComplexConjugate Finset
namespace PI.ParahoricIdxZ.W
def IdxStep : Prop :=
  ∀ (F : Type) [Field F] (O : Subring F) (ϖ : F) (hϖ : ϖ ∈ O), ϖ ≠ 0 → Formalism.DoubleCosetMeasures.IsLocalAt O ϖ →
    Finite (Formalism.DoubleCosetMeasures.kF O ϖ hϖ) → ∀ (a t : ℕ) (J' : Subgroup (GL (Fin a) F)),
    Formalism.DoubleCosetMeasures.congSub O ϖ a ≤ J' → J' ≤ Formalism.DoubleCosetMeasures.GLint O a →
    ∀ (J : Subgroup (GL (Fin (a + t)) F)), (∀ A, A ∈ J ↔ blockCond O ϖ J' A) →
    (J.subgroupOf (Formalism.DoubleCosetMeasures.GLint O (a + t))).index *
        Nat.card (J' ⧸ (Formalism.DoubleCosetMeasures.congSub O ϖ a).subgroupOf J') *
        Nat.card (Formalism.DoubleCosetMeasures.kF O ϖ hϖ) ^ (a * t) * Nat.card (GL (Fin t) (Formalism.DoubleCosetMeasures.kF O ϖ hϖ)) =
      Nat.card (GL (Fin (a + t)) (Formalism.DoubleCosetMeasures.kF O ϖ hϖ))
def CardStep : Prop :=
  ∀ (F : Type) [Field F] (O : Subring F) (ϖ : F) (hϖ : ϖ ∈ O), ϖ ≠ 0 → Formalism.DoubleCosetMeasures.IsLocalAt O ϖ →
    Finite (Formalism.DoubleCosetMeasures.kF O ϖ hϖ) → ∀ n : ℕ,
    (Nat.card (GL (Fin n) (Formalism.DoubleCosetMeasures.kF O ϖ hϖ)) : ℝ) =
      (Nat.card (Formalism.DoubleCosetMeasures.kF O ϖ hϖ) : ℝ) ^ (n * n) * qE (Nat.card (Formalism.DoubleCosetMeasures.kF O ϖ hϖ)) 1 n
end PI.ParahoricIdxZ.W


