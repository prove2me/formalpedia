-- Prove2me | Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_IsLocUnif
-- name    : Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_IsLocUnif
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T23:27:35.490242+00:00
-- url     : https://prove2.me/theorems/f6e8f5f8-c7c4-4dc8-849d-7a37ded7284f
-- title:
--   Is Loc Unif
-- statement:
--   Definitions and structural lemmas for Is Loc Unif, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/IsLocUnif.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
namespace Formalism.HermitianLattices.Ext.L3.HU
variable {K : Type*} [Field K] [StarRing K]
structure IsLocUnif (S : Subring K) (ϖ : K) : Prop where
  star_mem : ∀ a ∈ S, star a ∈ S
  mem : ϖ ∈ S
  fix : star ϖ = ϖ
  ne : ϖ ≠ 0
  tr : ∃ τ ∈ S, τ + star τ = 1
  skew : ∃ θ ∈ S, star θ = -θ ∧ θ ≠ 0
  dv : ∀ f ∈ S, star f = f → f⁻¹ ∈ S ∨ f * ϖ⁻¹ ∈ S
  rad : ∀ s ∈ S, 1 + ϖ * s ≠ 0 ∧ (1 + ϖ * s)⁻¹ ∈ S
  arch : ∀ a : K, ∃ l : ℕ, ϖ ^ l * a ∈ S
def Ent (S : Subring K) {m n : Type*} (M : Matrix m n K) : Prop := ∀ i j, M i j ∈ S
variable {S : Subring K} {m n o : Type*}
end Formalism.HermitianLattices.Ext.L3.HU


