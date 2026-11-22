-- Prove2me | Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_LocBasic
-- name    : Formalism_HermitianLattices_HermitianLatticesProofs_LocBasic
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T16:55:15.444355+00:00
-- url     : https://prove2.me/theorems/8b79ded0-173e-4754-8688-349627736990
-- title:
--   Loc Basic
-- statement:
--   Definitions and structural lemmas for Loc Basic, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianLattices/HermitianLatticesProofs/LocBasic.lean

import Mathlib
import Definitions.Def_Formalism_HermitianLattices_StatementLat
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace Formalism.HermitianLatticesTheory
section LocS
variable {R W : Type*} [CommRing R] [AddCommGroup W] [Module R W]
end LocS
section LocK
variable {R K V : Type*} [CommRing R] [Field K] [Algebra R K]
  [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]
end LocK
section Herm
variable {R K : Type*} [CommRing R] [Field K] [StarRing K] [Algebra R K]
def locBasic_sigma (hinj : Function.Injective (algebraMap R K))
    (hstar : ∀ r : R, star (algebraMap R K r) ∈ Set.range (algebraMap R K)) : R →+* R where
  toFun r := (hstar r).choose
  map_one' := hinj (by rw [(hstar 1).choose_spec, map_one, star_one])
  map_mul' a b := hinj (by
    rw [(hstar (a * b)).choose_spec, map_mul, map_mul, (hstar a).choose_spec,
      (hstar b).choose_spec, star_mul'])
  map_zero' := hinj (by rw [(hstar 0).choose_spec, map_zero, star_zero])
  map_add' a b := hinj (by
    rw [(hstar (a + b)).choose_spec, map_add, map_add, (hstar a).choose_spec,
      (hstar b).choose_spec, star_add])
end Herm
end Formalism.HermitianLatticesTheory


