-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_RankOneBoostIsometries
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_RankOneBoostIsometries
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T11:29:49.810799+00:00
-- url     : https://prove2.me/theorems/209a2fbb-c840-43d5-b942-6aad27f35dc7
-- title:
--   Rank One Boost Isometries
-- statement:
--   Definitions and structural lemmas for Rank One Boost Isometries, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/RankOneBoostIsometries.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FlowMatrixMajorants
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.ChartRestriction.G.FD
open NumberField Complex
open scoped ComplexConjugate
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
namespace RankOneBoostIsometries
open MajorantConjugateTransfer FlowMatrixMajorants
variable {r : ℕ} (X : Data E r) (τ : X.Ψ)
noncomputable def rk (p w : Fin r → ℂ) : Matrix (Fin r) (Fin r) ℂ :=
  Matrix.of fun i a => p i * ∑ b, τ.1 (X.Gm a b) * conj (w b)
noncomputable def boost (e f : Fin r → ℂ) (m σ : ℝ) : Matrix (Fin r) (Fin r) ℂ :=
  1 + (((σ - 1) / m : ℝ) : ℂ) • rk X τ e f + (((σ⁻¹ - 1) / m : ℝ) : ℂ) • rk X τ f e
section plane
variable {e f : Fin r → ℂ} {m : ℝ} (hm : 0 < m) (hee : hermC τ.1 X.Gm e e = 0)
  (hff : hermC τ.1 X.Gm f f = 0) (hef : hermC τ.1 X.Gm e f = m) (hfe : hermC τ.1 X.Gm f e = m)
include hm hee hff hef hfe
end plane
end RankOneBoostIsometries
end ReciprocityTheory.ChartRestriction.G.FD


