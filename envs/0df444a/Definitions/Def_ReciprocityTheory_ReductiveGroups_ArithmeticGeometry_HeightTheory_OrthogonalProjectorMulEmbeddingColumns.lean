-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_OrthogonalProjectorMulEmbeddingColumns
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_OrthogonalProjectorMulEmbeddingColumns
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T14:32:17.50424+00:00
-- url     : https://prove2.me/theorems/0649c37b-5550-4453-bf9e-a32e2b2d0e75
-- title:
--   Orthogonal Projector Mul Embedding Columns
-- statement:
--   Definitions and structural lemmas for Orthogonal Projector Mul Embedding Columns, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/OrthogonalProjectorMulEmbeddingColumns.lean

import Definitions.Def_ReciprocityTheory_SemistableReduction_LatSemiSt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.ChartRestriction.G.T0
open Matrix NumberField ComplexConjugate
open scoped ComplexOrder
section Proj
variable {K : Type} [Field K] {r k : ℕ}
noncomputable def hBm (σ : K →+* ℂ) (b : Fin k → Fin r → K) : Matrix (Fin r) (Fin k) ℂ :=
  Matrix.of fun l j => σ (b j l)
noncomputable def hPm (σ : K →+* ℂ) (b : Fin k → Fin r → K) : Matrix (Fin r) (Fin r) ℂ :=
  1 - hBm σ b * ((hBm σ b)ᴴ * hBm σ b)⁻¹ * (hBm σ b)ᴴ
noncomputable def hns {r : ℕ} (x : Fin r → ℂ) : ℝ := ∑ i, ‖x i‖ ^ 2
end Proj
section PT
variable {K : Type} [Field K] [NumberField K] {r k : ℕ}
end PT
end ReciprocityTheory.ChartRestriction.G.T0


