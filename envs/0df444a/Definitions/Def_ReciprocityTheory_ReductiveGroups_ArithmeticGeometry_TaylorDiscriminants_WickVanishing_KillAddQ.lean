-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_KillAddQ
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_KillAddQ
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T13:39:56.914988+00:00
-- url     : https://prove2.me/theorems/f4ba085b-d8a2-404e-96c5-1575db64f5b9
-- title:
--   Kill Add Q
-- statement:
--   Definitions and structural lemmas for Kill Add Q, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/WickVanishing/KillAddQ.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_KillAdd
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
namespace ReciprocityTheory.ChartRestriction.G.TB
def QuadColDerivSt : Prop :=
  ∀ (k : Type) [CommRing k] (d n : ℕ) (β : Matrix (Fin d) (Fin d) k),
    constantCoeff (quadCol (n := n) β) = 0 ∧
    (∀ (u : Fin d → k) (b : Fin n), constantCoeff (dAdd u b (quadCol (n := n) β)) = 0) ∧
    ∀ (u v : Fin d → k) (b b' : Fin n), dAdd u b (dAdd v b' (quadCol (n := n) β)) =
      C (if b = b' then dotProduct u (β.mulVec v) + dotProduct v (β.mulVec u) else 0)
end ReciprocityTheory.ChartRestriction.G.TB


