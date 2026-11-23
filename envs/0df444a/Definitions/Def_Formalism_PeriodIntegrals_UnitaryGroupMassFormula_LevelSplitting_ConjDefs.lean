-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_ConjDefs
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_ConjDefs
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T00:28:05.141929+00:00
-- url     : https://prove2.me/theorems/1e397cf6-c261-4dec-8e80-42aa8b1959d2
-- title:
--   Conj Defs
-- statement:
--   Definitions and structural lemmas for Conj Defs, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LevelSplitting/ConjDefs.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_SemidirectExistsOfParts
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PI.LevelKSplit.W.CD
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory PI.LevelKSplit
open scoped TensorProduct
section Ext
variable (F E : Type) [Field F] [NumberField F] [Field E] [Algebra F E]
  (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E)
def ModV : Prop :=
  IsHermND σ J → (∀ x, σ (σ x) = x) → ∀ g : HA (Af F) σ J,
    ∀ μ : Measure (Fin M → Af F ⊗[F] E), μ.IsAddHaarMeasure →
      μ.map (lin (Af F) σ J g) = μ
end Ext
def ModVAll : Prop := ForAllCM fun F E _ _ _ _ σ M J => ModV F E σ M J
end PI.LevelKSplit.W.CD


