-- Prove2me | Definitions.Def_ReciprocityTheory_DualLattices_FourierMapSmulLambdaWeight
-- name    : ReciprocityTheory_DualLattices_FourierMapSmulLambdaWeight
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T14:25:48.739833+00:00
-- url     : https://prove2.me/theorems/b00cbb25-a65a-4600-9c86-99e908a971e1
-- title:
--   Fourier Map Smul Lambda Weight
-- statement:
--   Definitions and structural lemmas for Fourier Map Smul Lambda Weight, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/FourierMapSmulLambdaWeight.lean

import Definitions.Def_ReciprocityTheory_DualLattices_SumLambdaWeight
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
namespace ReciprocityTheory.PGsh.Up.U3
open ReciprocityTheory.PGsh.L2
variable {p : ℕ} [hp : Fact p.Prime] {C : Type} [Field C] {v : Valuation C NNReal}
  {R : Type} [CommRing R] [Algebra R C]
end ReciprocityTheory.PGsh.Up.U3


