-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_NonvanishingNearHalfMax
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_NonvanishingNearHalfMax
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T14:42:09.531001+00:00
-- url     : https://prove2.me/theorems/79a92269-71bb-491e-b6e3-6f9d2f49abf6
-- title:
--   Nonvanishing Near Half Max
-- statement:
--   Definitions and structural lemmas for Nonvanishing Near Half Max, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/NonvanishingNearHalfMax.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_NonvanishingNearMaximum
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
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
def NonvanishingNearHalfMax : Prop :=
  ∀ (r : ℕ) (X : Data E r) (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ) (z0 x0 : Frame X.Ψ r) (w : ℝ),
    X.IsSec la P → z0 ∈ X.dom → X.IsOrtho x0 → (∃ b ∈ Bor X.Ψ r, x0 = rmul z0 b) →
    (∀ x ∈ X.dom, X.pnorm la P x ≤ 2 * X.pnorm la P z0) → 0 < X.pnorm la P z0 →
    (∑ τ, X.spread la τ) ≤ w → 1 ≤ w → 0 < r →
    ∀ Z : X.Coord, X.zN Z ≤ frameRadius w r / 5 → P (X.xZ x0 Z) ≠ 0
def FrameAtHalfMaximum : Prop :=
  ∀ (r : ℕ) (X : DataX E r) (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ) (z0 : Frame X.Ψ r) (laStar w : ℝ),
    X.IsSec la P → z0 ∈ X.dom →
    (∀ x ∈ X.dom, X.pnorm la P x ≤ 2 * X.pnorm la P z0) → 0 < X.pnorm la P z0 →
    (∑ τ, X.spread la τ) ≤ w → 1 ≤ w → 0 < r → 0 < laStar → laStar ≤ 1 →
    (∀ v ∈ X.L', v ≠ 0 → laStar ^ 2 ≤ ∑ τ, X.maj z0 τ (Data.emb τ.1 v)) →
    ∃ (x : Frame X.Ψ r) (lam : Fin r → Fin r → E), x ∈ X.dom ∧
      LamBasis X (frameBasisRadius r X.p0 (fdeg E) (dE E) laStar (3 * frameRadius w r / 5)) x lam ∧
      P x ≠ 0 ∧ ∀ τ v, X.maj x τ v ≤ 2 * X.maj z0 τ v
end
end ReciprocityTheory.ChartRestriction.G.FD


