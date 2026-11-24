-- Prove2me | Definitions.Def_GroundTheory_ProfiniteCohomology_CohomologicalDimension_PrimaryComponentCohomologyEqBotOfScdpLt
-- name    : GroundTheory_ProfiniteCohomology_CohomologicalDimension_PrimaryComponentCohomologyEqBotOfScdpLt
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-24T16:04:01.316408+00:00
-- url     : https://prove2.me/theorems/4f9d2286-43e0-4d07-9994-e94cf3ca721c
-- title:
--   Primary Component Cohomology Eq Bot Of Scdp Lt
-- statement:
--   Definitions and structural lemmas for Primary Component Cohomology Eq Bot Of Scdp Lt, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/CohomologicalDimension/PrimaryComponentCohomologyEqBotOfScdpLt.lean

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_ContinuousCochains
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.ProfCoh
universe u
variable (p : ℕ) (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
noncomputable def cdp : ℕ∞ :=
  sInf {n : ℕ∞ | ∀ (A : Rep.{u} (ULift.{u} ℤ) G) [IsDiscreteRep A], IsAddTorsion A →
    ∀ q : ℕ, n < q → AddCommGroup.primaryComponent (cohomology A q) p = ⊥}
noncomputable def scdp : ℕ∞ :=
  sInf {n : ℕ∞ | ∀ (A : Rep.{u} (ULift.{u} ℤ) G) [IsDiscreteRep A],
    ∀ q : ℕ, n < q → AddCommGroup.primaryComponent (cohomology A q) p = ⊥}
noncomputable def cd : ℕ∞ :=
  ⨆ p : Nat.Primes, cdp (p : ℕ) G
noncomputable def scd : ℕ∞ :=
  ⨆ p : Nat.Primes, scdp (p : ℕ) G
variable {p G}
end GroundTheory.ProfCoh


