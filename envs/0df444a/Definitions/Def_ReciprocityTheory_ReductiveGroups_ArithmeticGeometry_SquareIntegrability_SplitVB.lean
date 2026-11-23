-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_SplitVB
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_SplitVB
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T15:35:23.988605+00:00
-- url     : https://prove2.me/theorems/5cbc7836-bebb-4722-ae8f-25505f7acb34
-- title:
--   Split VB
-- statement:
--   Definitions and structural lemmas for Split VB, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/SplitVB.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_SplitSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_SplitVM
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_SplitVA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.ChartRestriction.G.I2
open NumberField Complex Module
noncomputable section
variable {E : Type} [Field E] [NumberField E]
section Emb
end Emb
section Coord
variable {dim : (E →+* ℂ) → ℕ}
def pN (ξ : Vsp dim) (σ : E →+* ℂ) : ℝ := ∑ a : Fin (dim σ), ‖ξ ⟨σ, a⟩‖ ^ 2
def nS (ξ : Vsp dim) (σ : E →+* ℂ) : ℝ := pN ξ σ + pN ξ (ComplexEmbedding.conjugate σ)
def hA (x ξ : Vsp dim) (σ : E →+* ℂ) : ℂ := ∑ a : Fin (dim σ), x ⟨σ, a⟩ * (starRingEnd ℂ) (ξ ⟨σ, a⟩)
def actT (t : (E →+* ℂ) → ℂ) (v : Vsp dim) : Vsp dim := WithLp.toLp 2 fun i => t i.1 * v i
end Coord
section CS
variable {dim : (E →+* ℂ) → ℕ}
end CS
end
end ReciprocityTheory.ChartRestriction.G.I2


