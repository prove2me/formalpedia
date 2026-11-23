-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IntegralSpanAlgebra_Burnside
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IntegralSpanAlgebra_Burnside
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T04:54:18.834911+00:00
-- url     : https://prove2.me/theorems/be2beda4-c1c8-4645-b697-6749f762607c
-- title:
--   Burnside
-- statement:
--   Definitions and structural lemmas for Burnside, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/IntegralSpanAlgebra/Burnside.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UMultOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PI.UMultOne.GelfSpanWork
open Matrix Module
variable {G : Type} [Group G] {N : ℕ}
def repEnd (ρ : G →* GL (Fin N) ℂ) : G →* Module.End ℂ (Fin N → ℂ) where
  toFun g := Matrix.toLin' ((ρ g : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ)
  map_one' := by simp; rfl
  map_mul' x y := by
    rw [map_mul, Units.val_mul, Matrix.toLin'_mul]
    rfl
def spanAlg (ρ : G →* GL (Fin N) ℂ) : Subalgebra ℂ (Module.End ℂ (Fin N → ℂ)) :=
  Algebra.adjoin ℂ (Set.range (repEnd ρ))
instance spanAlg_tower (ρ : G →* GL (Fin N) ℂ) : IsScalarTower ℂ (spanAlg ρ) (Fin N → ℂ) :=
  ⟨fun _ _ _ => rfl⟩
end PI.UMultOne.GelfSpanWork


