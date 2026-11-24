-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicIndexEquality_ModQOneOfClosure
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicIndexEquality_ModQOneOfClosure
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-24T13:32:53.916565+00:00
-- url     : https://prove2.me/theorems/ded1148d-b9f8-4bdd-9e36-b2d3badc0c66
-- title:
--   Mod QOne Of Closure
-- statement:
--   Definitions and structural lemmas for Mod QOne Of Closure, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicIndexEquality/ModQOneOfClosure.lean

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicIndexEquality_Commensurated
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PI.UnitaryGroupMassFormula.AdIndexEq
open NumberField IsDedekindDomain
open Formalism.MainNotions.S
def ModQHom : Prop :=
  ∀ (G : Type) [Group G] (K : Subgroup G), Commensurated K →
    (∀ x y : G, modQ K (x * y) = modQ K x * modQ K y) ∧ (∀ k ∈ K, modQ K k = 1) ∧
      (∀ x : G, modQ K x = 1 → dIdx K x = dIdx K x⁻¹)
end PI.UnitaryGroupMassFormula.AdIndexEq
end


