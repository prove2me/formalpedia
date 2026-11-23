-- Prove2me | Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_EigenspaceCyclicDensity_CreationOperators_KoszulDifferentialAnticommutator
-- name    : CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_EigenspaceCyclicDensity_CreationOperators_KoszulDifferentialAnticommutator
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T06:15:32.689851+00:00
-- url     : https://prove2.me/theorems/dec81fac-9491-4d03-a27e-26b7b2893a06
-- title:
--   Koszul Differential Anticommutator
-- statement:
--   Definitions and structural lemmas for Koszul Differential Anticommutator, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/LowKTypeMultiplicity/EigenspaceCyclicDensity/CreationOperators/KoszulDifferentialAnticommutator.lean

import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_EigenspaceCyclicDensity_CreationOperators_DifferentialBoundedSupport
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
namespace CompanionTheory.D.LK
open Car Formalism.REAL
open CompanionTheory.D.DSIC (KRel)
variable {n : ℕ} {ε : Fin n → Bool}
def tc (ε : Fin n → Bool) (i j k : Pos n) : ℂ := if Tri ε i j k then 1 else 0
def cc (ε : Fin n → Bool) (i : Pos n) : ℂ := if cpt ε i then 1 else 0
section Ring
variable {R : Type} [Ring R] [Algebra ℂ R] (E : Fin n → Fin n → R) (an cr : Pos n → R)
end Ring
end CompanionTheory.D.LK


