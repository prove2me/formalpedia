-- Prove2me | Definitions.Def_ReciprocityTheory_GaloisValuations_ArithOfA
-- name    : ReciprocityTheory_GaloisValuations_ArithOfA
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T00:54:06.919035+00:00
-- url     : https://prove2.me/theorems/68cbac33-4b87-4e0b-bebe-1ebc84686722
-- title:
--   Arith Of A
-- statement:
--   Definitions and structural lemmas for Arith Of A, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GaloisValuations/ArithOfA.lean

import Definitions.Def_ReciprocityTheory_GaloisValuations_Global
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Pointwise
namespace ReciprocityTheory.Gal
open Formalism.ConjugateSelfDual
section deg
variable {F : Type*} [Field F] [NumberField F]
def locDegree (v : HeightOneSpectrum (𝓞 F)) : ℕ :=
  v.asIdeal.ramificationIdx ℤ * v.asIdeal.inertiaDeg ℤ
end deg
section conj
variable {F Ω : Type*} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
end conj
end ReciprocityTheory.Gal


