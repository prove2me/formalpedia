-- Prove2me | Definitions.Def_GroundTheory_IdeleRoots_TorusPowers_HeckeIdem
-- name    : GroundTheory_IdeleRoots_TorusPowers_HeckeIdem
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-25T09:37:25.805168+00:00
-- url     : https://prove2.me/theorems/420b63c2-f4f6-4028-9bdf-27519494c80c
-- title:
--   Hecke Idem
-- statement:
--   Definitions and structural lemmas for Hecke Idem, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/IdeleRoots/TorusPowers/HeckeIdem.lean

import Mathlib
import Definitions.Def_GroundTheory_IdeleRoots_TorusPowers_HeckeTensor
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open scoped TensorProduct NumberField.AdeleRing
open NumberField IsDedekindDomain HeckeCharacterZeroLocus.ThmBIn GroundTheory.Global GroundTheory.Global.AdeleBaseChange
  GroundTheory.Global.SemiLocal
namespace GroundTheory.BlockD
namespace ThmBHecke
section Single
variable {K : Type} [Field K] [NumberField K]
open Classical in

def finSingleOne (w : HeightOneSpectrum (𝓞 K)) : FiniteAdeleRing (𝓞 K) K :=
  ⟨Pi.single (M := fun u : HeightOneSpectrum (𝓞 K) ↦ u.adicCompletion K) w 1, by
    refine Filter.eventually_cofinite.2 ((Set.finite_singleton w).subset fun u hu ↦ ?_)
    by_contra h
    exact hu (by rw [Pi.single_eq_of_ne h]; exact zero_mem _)⟩
end Single
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
def idemAt (P : HeightOneSpectrum (𝓞 E)) : 𝔸[E] := (0, finSingleOne P)
def placeIdem (v : HeightOneSpectrum (𝓞 F)) : AF F := pairA F 0 (finSingleOne v)
section Conj
variable {σ : E →ₐ[F] E}
end Conj
end ThmBHecke
end GroundTheory.BlockD


