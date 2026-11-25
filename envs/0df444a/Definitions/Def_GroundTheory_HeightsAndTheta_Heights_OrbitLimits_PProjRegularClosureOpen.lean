-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PProjRegularClosureOpen
-- name    : GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PProjRegularClosureOpen
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-25T13:13:02.861154+00:00
-- url     : https://prove2.me/theorems/b52ae58d-8176-56da-8a6b-7204ab76f00e
-- title:
--   PProj Regular Closure Open
-- statement:
--   Definitions and structural lemmas for PProj Regular Closure Open, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PProjRegularClosureOpen.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PProjRegular
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StatementsProjRegularClosureOpen
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
open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.AnForm.M
namespace ProjRegularClosureOpen
def projNumMat {n : ℕ} (F : (Fin n → ℂ) → Fin (n + 1) → ℂ) (u : Fin n → ℂ) :
    Matrix (Fin n) (Fin n) ℂ :=
  fun i l => F u 0 * fderiv ℂ (fun v => F v i.succ) u (Pi.single l 1) -
    F u i.succ * fderiv ℂ (fun v => F v 0) u (Pi.single l 1)
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {P J : Ideal (MRing ι)}
  {n : ℕ} {R : AnLogRes P J (n + 1)} (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (n + 1) → ℂ))
end ProjRegularClosureOpen
end GroundTheory.Heights₂.Heights.Targets


