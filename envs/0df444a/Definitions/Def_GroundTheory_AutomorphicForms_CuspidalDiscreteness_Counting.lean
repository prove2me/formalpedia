-- Prove2me | Definitions.Def_GroundTheory_AutomorphicForms_CuspidalDiscreteness_Counting
-- name    : GroundTheory_AutomorphicForms_CuspidalDiscreteness_Counting
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T19:03:40.785269+00:00
-- url     : https://prove2.me/theorems/bb94baa7-8587-426c-8547-b9e2b6c4f6ce
-- title:
--   Counting
-- statement:
--   Definitions and structural lemmas for Counting, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/CuspidalDiscreteness/Counting.lean

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_Adele_Discrete
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Set
namespace GroundTheory.Automorphic
noncomputable section
namespace CuspidalSpectrum
variable (K : Type*) [Field K] [NumberField K]
variable {K}
def ratGLBox (n : ℕ) (𝒦 : Set (FiniteAdeleRing (𝓞 K) K)) (T : ℝ) : Set (GL (Fin n) K) :=
  {γ | ∀ i j, algebraMap K (FiniteAdeleRing (𝓞 K) K) ((γ : Matrix (Fin n) (Fin n) K) i j) ∈ 𝒦 ∧
    ∀ w : InfinitePlace K, w ((γ : Matrix (Fin n) (Fin n) K) i j) ≤ T}
end CuspidalSpectrum
end
end GroundTheory.Automorphic


