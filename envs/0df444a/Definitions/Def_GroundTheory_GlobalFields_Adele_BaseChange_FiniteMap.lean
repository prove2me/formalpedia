-- Prove2me | Definitions.Def_GroundTheory_GlobalFields_Adele_BaseChange_FiniteMap
-- name    : GroundTheory_GlobalFields_Adele_BaseChange_FiniteMap
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-25T01:17:52.223149+00:00
-- url     : https://prove2.me/theorems/1690316e-b061-4ea7-9ace-23acb3b3a1a2
-- title:
--   Finite Map
-- statement:
--   Definitions and structural lemmas for Finite Map, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/Adele/BaseChange/FiniteMap.lean

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_SemilocalAlgebras_NormTrace
import Definitions.Def_GroundTheory_GlobalFields_CompletionAtPlace_Integers
import Theorems.Thm_GroundTheory_Global_SemiLocal_valued_completionMap

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
open IsDedekindDomain NumberField TensorProduct Module Filter Topology
open scoped RestrictedProduct
noncomputable section
namespace AdeleBaseChange
open SemiLocal
variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
variable (K) in

def below (w : HeightOneSpectrum (𝓞 L)) : HeightOneSpectrum (𝓞 K) where
  asIdeal := w.asIdeal.under (𝓞 K)
  isPrime := Ideal.IsPrime.under (𝓞 K) w.asIdeal
  ne_bot := Ideal.under_ne_bot (𝓞 K) w.ne_bot
instance liesOver_below (w : HeightOneSpectrum (𝓞 L)) :
    w.asIdeal.LiesOver (below K w).asIdeal :=
  ⟨rfl⟩
omit [NumberField K] [NumberField L] in

theorem below_eq_iff (w : HeightOneSpectrum (𝓞 L)) (v : HeightOneSpectrum (𝓞 K)) :
    below K w = v ↔ w.asIdeal.LiesOver v.asIdeal := by
  constructor
  · rintro rfl
    infer_instance
  · intro h
    exact HeightOneSpectrum.ext h.over.symm
theorem tendsto_below : Tendsto (below K (L := L)) cofinite cofinite :=
  Filter.Tendsto.cofinite_of_finite_preimage_singleton fun v ↦
    ((Set.finite_range (Subtype.val : PlacesOver L v → HeightOneSpectrum (𝓞 L))).subset
      fun w hw ↦ ⟨⟨w, (below_eq_iff w v).1 hw⟩, rfl⟩).to_subtype
theorem mapsTo_completionMap (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L))
    [w.asIdeal.LiesOver v.asIdeal] :
    Set.MapsTo (completionMap v w) (v.adicCompletionIntegers K) (w.adicCompletionIntegers L) := by
  intro x hx
  rw [SetLike.mem_coe, HeightOneSpectrum.mem_adicCompletionIntegers] at hx ⊢
  rw [valued_completionMap]
  exact pow_le_one' hx _
variable (K L) in

def finiteAdeleMap : FiniteAdeleRing (𝓞 K) K →+* FiniteAdeleRing (𝓞 L) L :=
  RestrictedProduct.mapAlongRingHom (fun v : HeightOneSpectrum (𝓞 K) ↦ v.adicCompletion K)
    (fun w : HeightOneSpectrum (𝓞 L) ↦ w.adicCompletion L)
    (B₁ := fun v ↦ v.adicCompletionIntegers K) (B₂ := fun w ↦ w.adicCompletionIntegers L)
    (below K) tendsto_below (fun w ↦ completionMap (below K w) w)
    (hφ := .of_forall fun w ↦ mapsTo_completionMap (below K w) w)
end AdeleBaseChange
end
end GroundTheory.Global


