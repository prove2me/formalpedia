-- Prove2me | Definitions.Def_GroundTheory_GlobalFields_Adele_WeakApprox
-- name    : GroundTheory_GlobalFields_Adele_WeakApprox
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T05:12:11.270718+00:00
-- url     : https://prove2.me/theorems/4516bf08-ce53-42a7-84f5-4cf613cd61bb
-- title:
--   Weak Approx
-- statement:
--   Definitions and structural lemmas for Weak Approx, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/Adele/WeakApprox.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
namespace GroundTheory.Global
open IsDedekindDomain NumberField
variable {K : Type*} [Field K] [NumberField K]
section AbsoluteValues
end AbsoluteValues
section Density
variable (S : Finset (HeightOneSpectrum (𝓞 K))) (T : Finset (InfinitePlace K))
noncomputable def placeAbv : S ⊕ T → AbsoluteValue K ℝ :=
  Sum.elim (fun v ↦ NumberField.HeightOneSpectrum.adicAbv K v.1) (fun w ↦ w.1.1)
end Density
end GroundTheory.Global


