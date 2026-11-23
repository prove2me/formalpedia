-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_NonvanishingNearMaximum
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_NonvanishingNearMaximum
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T10:07:37.736295+00:00
-- url     : https://prove2.me/theorems/569a8535-c252-4f71-9f90-8c5153e3bc83
-- title:
--   Nonvanishing Near Maximum
-- statement:
--   Definitions and structural lemmas for Nonvanishing Near Maximum, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/NonvanishingNearMaximum.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_IsotropicCoefficientSplitting
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
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
def frameBasisRadius (r p0 f : ℕ) (d laStar ρ : ℝ) : ℝ :=
  (2 * ReciprocityTheory.MultiplicativeHeights.approxR r (d5mu f r d (laStar / Real.sqrt f)) ρ) ^ (2 * p0 + 1)
def frameRadius (w : ℝ) (r : ℕ) : ℝ := 1 / (10 * Real.sqrt (w * r))
def LamBasis {r : ℕ} (X : DataX E r) (La : ℝ) (x : Frame X.Ψ r) (lam : Fin r → Fin r → E) : Prop :=
  (∀ j, lam j ∈ X.L') ∧ LinearIndependent E lam ∧
  (∀ j k : Fin r, (j : ℕ) < X.p0 → X.p0 ≤ (k : ℕ) → herm X.Gm (lam j) (lam k) = 0) ∧
  (∀ j : Fin r, (j : ℕ) < X.p0 → ∀ τ : X.Ψ, 0 < (τ.1 (herm X.Gm (lam j) (lam j))).re) ∧
  (∀ j : Fin r, X.p0 ≤ (j : ℕ) → ∀ τ : X.Ψ, (τ.1 (herm X.Gm (lam j) (lam j))).re < 0) ∧
  (∀ j (τ : X.Ψ), ‖τ.1 (herm X.Gm (lam j) (lam j))‖ ≤ La ^ 2) ∧
  ∀ τ : X.Ψ, Submodule.span ℂ (Set.range fun a : Fin X.p0 => col (mat x τ) (Fin.castLE X.p0_le a)) =
    Submodule.span ℂ (Set.range fun a : Fin X.p0 => Data.emb τ.1 (lam (Fin.castLE X.p0_le a)))
def LatticeBoundAtMaximum : Prop :=
  ∀ (r : ℕ) (X : DataX E r) (z0 x0 : Frame X.Ψ r) (laStar ρ : ℝ),
    z0 ∈ X.dom → x0 ∈ X.dom → X.IsOrtho x0 → X.SameFlag z0 x0 → 0 < laStar → laStar ≤ 1 → 0 < ρ → ρ ≤ 1 →
    (∀ v ∈ X.L', v ≠ 0 → laStar ^ 2 ≤ ∑ τ, X.maj z0 τ (Data.emb τ.1 v)) →
    ∃ (lam : Fin r → Fin r → E) (Z : X.Coord), X.zN Z ≤ ρ / 3 ∧
      LamBasis X (frameBasisRadius r X.p0 (fdeg E) (dE E) laStar ρ) (X.xZ x0 Z) lam
def NonvanishingNearMaximum : Prop :=
  ∀ (r : ℕ) (X : Data E r) (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ) (z0 x0 : Frame X.Ψ r) (w : ℝ),
    X.IsSec la P → z0 ∈ X.dom → X.IsOrtho x0 → (∃ b ∈ Bor X.Ψ r, x0 = rmul z0 b) →
    (∀ x ∈ X.dom, X.pnorm la P x ≤ X.pnorm la P z0) → 0 < X.pnorm la P z0 →
    (∑ τ, X.spread la τ) ≤ w → 1 ≤ w → 0 < r →
    ∀ Z : X.Coord, X.zN Z ≤ frameRadius w r / 3 → P (X.xZ x0 Z) ≠ 0
def FrameAtMaximum : Prop :=
  ∀ (r : ℕ) (X : DataX E r) (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ) (z0 : Frame X.Ψ r) (laStar w : ℝ),
    X.IsSec la P → z0 ∈ X.dom →
    (∀ x ∈ X.dom, X.pnorm la P x ≤ X.pnorm la P z0) → 0 < X.pnorm la P z0 →
    (∑ τ, X.spread la τ) ≤ w → 1 ≤ w → 0 < r → 0 < laStar → laStar ≤ 1 →
    (∀ v ∈ X.L', v ≠ 0 → laStar ^ 2 ≤ ∑ τ, X.maj z0 τ (Data.emb τ.1 v)) →
    ∃ (x : Frame X.Ψ r) (lam : Fin r → Fin r → E), x ∈ X.dom ∧
      LamBasis X (frameBasisRadius r X.p0 (fdeg E) (dE E) laStar (frameRadius w r)) x lam ∧
      P x ≠ 0 ∧ ∀ τ v, X.maj x τ v ≤ 2 * X.maj z0 τ v
end
end ReciprocityTheory.ChartRestriction.G.FD


