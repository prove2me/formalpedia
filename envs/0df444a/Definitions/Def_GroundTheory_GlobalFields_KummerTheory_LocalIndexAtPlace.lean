-- Prove2me | Definitions.Def_GroundTheory_GlobalFields_KummerTheory_LocalIndexAtPlace
-- name    : GroundTheory_GlobalFields_KummerTheory_LocalIndexAtPlace
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T06:44:54.697908+00:00
-- url     : https://prove2.me/theorems/b44004d3-15b5-4b7f-abba-1231a776ab8e
-- title:
--   Local Index At Place
-- statement:
--   Definitions and structural lemmas for Local Index At Place, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/KummerTheory/LocalIndexAtPlace.lean

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_LocalFieldAtPlace
import Definitions.Def_GroundTheory_GlobalFields_KummerTheory_LocalIndex
import Theorems.Thm_GroundTheory_Global_mem_valuationInteger_iff

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
open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField ValuativeRel
  GroundTheory.LocalField
section FinitePlace
variable {K : Type*} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
theorem coe_mem_adicCompletionIntegers (x : 𝒪[v.adicCompletion K]) :
    (x : v.adicCompletion K) ∈ v.adicCompletionIntegers K :=
  (mem_valuationInteger_iff v (x : v.adicCompletion K)).1 x.2
theorem coe_mem_valuationInteger (x : v.adicCompletionIntegers K) :
    (x : v.adicCompletion K) ∈ 𝒪[v.adicCompletion K] :=
  (mem_valuationInteger_iff v (x : v.adicCompletion K)).2 x.2
def integerEquivAdicCompletionIntegers :
    𝒪[v.adicCompletion K] ≃+* v.adicCompletionIntegers K where
  toFun x := ⟨x, coe_mem_adicCompletionIntegers v x⟩
  invFun x := ⟨x, coe_mem_valuationInteger v x⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl
variable {v}
variable (v)
end FinitePlace
section Archimedean
end Archimedean
end GroundTheory.Global


