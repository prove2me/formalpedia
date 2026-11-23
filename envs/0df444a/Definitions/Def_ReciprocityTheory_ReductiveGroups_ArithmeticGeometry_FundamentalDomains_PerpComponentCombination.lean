-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_PerpComponentCombination
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_PerpComponentCombination
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T10:39:55.473846+00:00
-- url     : https://prove2.me/theorems/7ca2cae4-e058-4520-aea8-49400898f914
-- title:
--   Perp Component Combination
-- statement:
--   Definitions and structural lemmas for Perp Component Combination, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/PerpComponentCombination.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_PerpLatticeTransfer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_OrthogonalLatticeDecomposition
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_MajPos
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.ChartRestriction.G.FD.PerpComponentCombination
open NumberField Complex Matrix ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.PerpBasisExistence
  ReciprocityTheory.ChartRestriction.G.FD.PerpLatticeTransfer
open scoped ComplexConjugate
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
def eps' (p : ℕ) {n : ℕ} (k : Fin n) : ℂ := if (k : ℕ) < p then 1 else -1
section Coord
variable (X : Data E r) (τ : X.Ψ) {n : ℕ} (p : ℕ) (f : Fin n → Fin r → ℂ)
  (hf : ∀ k l, hermC τ.1 X.Gm (f k) (f l) = if k = l then eps' p k else 0)
include hf
end Coord
def uc (X : Data E r) (z0 : Frame X.Ψ r) (ξ : Fin r → E) (τ : X.Ψ) (v : Fin r → ℂ) : Fin r → ℂ :=
  v - (X.Hf z0 τ v (Data.emb τ.1 ξ) / X.Hf z0 τ (Data.emb τ.1 ξ) (Data.emb τ.1 ξ)) •
    Data.emb τ.1 ξ
section Uc
variable (X : Data E r) {z0 : Frame X.Ψ r} (ξ : Fin r → E) (τ : X.Ψ)
end Uc
end
end ReciprocityTheory.ChartRestriction.G.FD.PerpComponentCombination


