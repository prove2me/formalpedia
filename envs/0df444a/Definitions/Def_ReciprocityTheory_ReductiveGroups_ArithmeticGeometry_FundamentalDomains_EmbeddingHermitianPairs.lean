-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_EmbeddingHermitianPairs
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_EmbeddingHermitianPairs
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T05:22:27.513149+00:00
-- url     : https://prove2.me/theorems/5fcde76e-0279-4304-839a-3d55896f5d46
-- title:
--   Embedding Hermitian Pairs
-- statement:
--   Definitions and structural lemmas for Embedding Hermitian Pairs, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/EmbeddingHermitianPairs.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_ModerateCoefficientPositivity
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.ChartRestriction.G.FD.EmbeddingHermitianPairs
open NumberField Complex Matrix ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
section herm
variable (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E)
end herm
section flowAlg
variable (X : Data E r)
def wv (ξ : Fin r → E) (τ : X.Ψ) : Fin r → ℂ := fun b => ∑ k, τ.1 (X.Gm b k) * conj (τ.1 (ξ k))
end flowAlg
end ReciprocityTheory.ChartRestriction.G.FD.EmbeddingHermitianPairs


