-- Prove2me | Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_EigenspaceCyclicDensity_CreationOperators_DifferentialBoundedSupport
-- name    : CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_EigenspaceCyclicDensity_CreationOperators_DifferentialBoundedSupport
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T06:11:10.169167+00:00
-- url     : https://prove2.me/theorems/1af876c5-a17d-4864-858d-6820bda03b4a
-- title:
--   Differential Bounded Support
-- statement:
--   Definitions and structural lemmas for Differential Bounded Support, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/LowKTypeMultiplicity/EigenspaceCyclicDensity/CreationOperators/DifferentialBoundedSupport.lean

import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_EigenspaceCyclicDensity_CreationOperators_CreApply
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
variable {n : ℕ} {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
abbrev Tri (ε : Fin n → Bool) (i j k : Pos n) : Prop :=
  cpt ε i ∧ cpt ε j ∧ i.1.2 = j.1.1 ∧ k.1.1 = i.1.1 ∧ k.1.2 = j.1.2
end CompanionTheory.D.LK


