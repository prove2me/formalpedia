-- Prove2me | Definitions.Def_ReciprocityTheory_ClassFieldTheory_GlobalClassField_IsFrobAtMulOfMemInertiaGroup
-- name    : ReciprocityTheory_ClassFieldTheory_GlobalClassField_IsFrobAtMulOfMemInertiaGroup
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:23:17.683436+00:00
-- url     : https://prove2.me/theorems/8575298f-bf4d-4f19-9999-a580c80fd3a5
-- title:
--   Is Frob At Mul Of Mem Inertia Group
-- statement:
--   Definitions and structural lemmas for Is Frob At Mul Of Mem Inertia Group, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/GlobalClassField/IsFrobAtMulOfMemInertiaGroup.lean

import Definitions.Def_ReciprocityTheory_NeutralLocalFields_Reciprocity
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_GlobalClassField_SUnitGalois_GalSmulAsIdeal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Neutral.B1
open scoped Pointwise
namespace ReciprocityTheory.DiscreteGroups.GlobalClassField
variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
def inertiaGroup (Q : Ideal (𝓞 L)) : Subgroup (L ≃ₐ[K] L) :=
  (Q.toAddSubgroup.inertia (𝓞 L ≃ₐ[𝓞 K] 𝓞 L)).comap (galRestrict (𝓞 K) K L (𝓞 L)).toMonoidHom
variable {K L}
section Over
variable (v : HeightOneSpectrum (𝓞 K)) (Q Q' : Ideal (𝓞 L)) [Q.IsPrime] [Q.LiesOver v.asIdeal]
variable [IsGalois K L]
end Over
end ReciprocityTheory.DiscreteGroups.GlobalClassField


