-- Prove2me | Definitions.Def_ReciprocityTheory_SemistableReduction_SphereTorusB
-- name    : ReciprocityTheory_SemistableReduction_SphereTorusB
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T10:02:20.326245+00:00
-- url     : https://prove2.me/theorems/39633201-f6c9-4d01-93d9-e7045a02f11c
-- title:
--   Sphere Torus B
-- statement:
--   Definitions and structural lemmas for Sphere Torus B, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/SphereTorusB.lean

import Definitions.Def_ReciprocityTheory_SemistableReduction_SphereTorusA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace ReciprocityTheory.MultiplicativeHeights
open MeasureTheory
def scaledTorusMean {ι : Type*} [Fintype ι] (r : ι → ℂ) (f : MvPolynomial ι ℂ) : ℝ :=
  ∫ θ, Real.log ‖MvPolynomial.eval (fun j => r j * torusPoint θ j) f‖ ∂(torusProb ι)
end ReciprocityTheory.MultiplicativeHeights


