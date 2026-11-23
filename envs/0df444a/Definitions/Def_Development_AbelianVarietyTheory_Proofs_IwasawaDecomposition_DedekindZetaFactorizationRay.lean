-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_DedekindZetaFactorizationRay
-- name    : Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_DedekindZetaFactorizationRay
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T04:35:29.317055+00:00
-- url     : https://prove2.me/theorems/53c02710-ec9b-4737-949c-7108074bec52
-- title:
--   Dedekind Zeta Factorization Ray
-- statement:
--   Definitions and structural lemmas for Dedekind Zeta Factorization Ray, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/DedekindZetaFactorizationRay.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_NonemptyRayDataOfNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_RayLSeriesEulerProductStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.Mem Complex
open scoped ComplexOrder
namespace GlobalTheory.Mem
def PosDirichlet (F : ℂ → ℂ) : Prop :=
  ∃ (ι : Type) (w : ι → ℝ) (N : ι → ℕ), (∀ i, 0 ≤ w i) ∧ (∀ i, N i ≠ 0) ∧
    ∀ s : ℂ, 1 < s.re → HasSum (fun i => (w i : ℂ) * (N i : ℂ) ^ (-s)) (F s)
namespace PosDirichlet
end PosDirichlet
end GlobalTheory.Mem


