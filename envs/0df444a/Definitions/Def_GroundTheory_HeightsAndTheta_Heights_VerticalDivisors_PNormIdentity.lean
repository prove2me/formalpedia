-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_PNormIdentity
-- name    : GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_PNormIdentity
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:41:47.280874+00:00
-- url     : https://prove2.me/theorems/8124db94-da52-4345-b9a8-8b5a4d74b6dd
-- title:
--   PNorm Identity
-- statement:
--   Definitions and structural lemmas for PNorm Identity, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/PNormIdentity.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_ComapMaximalIdealParDVR
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.Vertical
open MvPolynomial NumberField IsDedekindDomain
noncomputable section
section Lemmas
variable {K : Type*} [Field K] [NumberField K] {n e : ℕ}
def chartVar (e n : ℕ) (ij : Fin (e + 1) × Fin n) : Par e n :=
  Fin.cases (motive := fun _ => Par e n) (.inr ij.2) (fun i => .inl (i, ij.2)) ij.1
end Lemmas
end
end GroundTheory.Heights₂.Heights.Vertical


