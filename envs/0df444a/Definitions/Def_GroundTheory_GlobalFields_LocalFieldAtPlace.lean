-- Prove2me | Definitions.Def_GroundTheory_GlobalFields_LocalFieldAtPlace
-- name    : GroundTheory_GlobalFields_LocalFieldAtPlace
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T05:07:10.844542+00:00
-- url     : https://prove2.me/theorems/3f9564f3-f63d-4d0e-b3ee-1989d14b1772
-- title:
--   Local Field At Place
-- statement:
--   Definitions and structural lemmas for Local Field At Place, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/LocalFieldAtPlace.lean

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_LocalAtPlace
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField WithZero
open scoped WithZero
namespace GroundTheory.Global
section Discrete
variable {R : Type*} [CommRing R] [IsDedekindDomain R] {K : Type*} [Field K] [Algebra R K]
  [IsFractionRing R K] (v : HeightOneSpectrum R)
end Discrete
section AbsoluteValue
variable {K : Type*} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
noncomputable def normalizedAbv : AbsoluteValue (v.adicCompletion K) ℝ where
  toFun x := ‖x‖
  map_mul' := norm_mul
  nonneg' := norm_nonneg
  eq_zero' _ := norm_eq_zero
  add_le' := norm_add_le
end AbsoluteValue
section LocalField
variable {R : Type*} [CommRing R] [IsDedekindDomain R] {K : Type*} [Field K] [Algebra R K]
  [IsFractionRing R K] (v : HeightOneSpectrum R)
noncomputable instance : ValuativeRel (v.adicCompletion K) :=
  .ofValuation Valued.v
instance : (Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰).Compatible :=
  .ofValuation _
instance : IsValuativeTopology (v.adicCompletion K) :=
  IsValuativeTopology.of_mem_nhds_iff_vle Valued.v Valued.mem_nhds
instance : ValuativeRel.IsNontrivial (v.adicCompletion K) :=
  (ValuativeRel.isNontrivial_iff_isNontrivial Valued.v).2 inferInstance
end LocalField
section Bridge
open ValuativeRel
variable {R : Type*} [CommRing R] [IsDedekindDomain R] {K : Type*} [Field K] [Algebra R K]
  [IsFractionRing R K] (v : HeightOneSpectrum R)
end Bridge
section NumberField
variable {K : Type*} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
instance : IsNonarchimedeanLocalField (v.adicCompletion K) where
end NumberField
end GroundTheory.Global


