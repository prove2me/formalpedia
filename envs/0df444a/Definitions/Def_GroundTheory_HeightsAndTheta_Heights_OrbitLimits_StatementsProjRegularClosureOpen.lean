-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StatementsProjRegularClosureOpen
-- name    : GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StatementsProjRegularClosureOpen
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-25T12:59:43.016714+00:00
-- url     : https://prove2.me/theorems/77314d51-f6d8-4278-9c34-76c49aa5e44c
-- title:
--   Statements Proj Regular Closure Open
-- statement:
--   Definitions and structural lemmas for Statements Proj Regular Closure Open, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/StatementsProjRegularClosureOpen.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StatementsProjRegular
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_DivPushResSideInhabitants
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
namespace GroundTheory.Heights₂.Heights.Targets
open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.AnForm.M
def ProjRegularClosureOpen.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P J : Ideal (MRing ι)) (n : ℕ)
    (R : AnLogRes P J (n + 1)) (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (n + 1) → ℂ))
    (V : Set R.X) (BV : FinHolAtlas n V),
    HoloMap BV R.A Subtype.val → IsOpen (closure (projRegular R Ψ BV))
end GroundTheory.Heights₂.Heights.Targets


