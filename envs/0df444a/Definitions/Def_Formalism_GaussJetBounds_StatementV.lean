-- Prove2me | Definitions.Def_Formalism_GaussJetBounds_StatementV
-- name    : Formalism_GaussJetBounds_StatementV
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:06:58.603354+00:00
-- url     : https://prove2.me/theorems/f7c136b5-af93-472a-ab14-bdac23cb426e
-- title:
--   Statement V
-- statement:
--   Definitions and structural lemmas for Statement V, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/StatementV.lean

import Definitions.Def_Formalism_GaussJetBounds_StatementS
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace Formalism.DworkPowerSeriesWeights
open Formalism.IncomingBounds
def ThmAEntry : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (d N0 N1 : ℕ) [NeZero d], 3 ≤ l → 2 ≤ d → Even d →
    ∀ (K0 : Subfield ℂ_[l]), Unram l K0 → ∀ ζ : ℂ_[l], IsPrimitiveRoot ζ (l ^ d - 1) →
    ∀ be : MvPowerSeries (ZMod d) ℂ_[l], BHyp l d K0 ζ be →
    ∀ g : ZV d N0 N1 → MvPowerSeries (ZV d N0 N1) ℂ_[l],
      (∀ y, MvPowerSeries.constantCoeff (g y) = 0) →
      (∀ y, MvPowerSeries.subst g (entLog (K := ℂ_[l]) l y) = MvPowerSeries.X y) →
    ∀ U : MvPowerSeries (ZV d N0 N1) ℂ_[l], Integral U → ∀ (ε : ℂ_[l]), (ε = 1 ∨ ε = -1) →
    ∀ (TT : Finset (ZMod d)) (colN : ZMod d → ℕ) (p : ∀ s, Fin (colN s) → ℕ)
      (hp : ∀ s c, p s c ≤ N0), (∀ s c, 1 ≤ p s c) → ∀ (I : ∀ s c, Fin (p s c) → Fin N1),
    ∀ (nu1 nu2 size : ZMod d → ℕ), (∀ s, nu1 s = colN s) →
      (∀ s, nu2 s = (Finset.univ.filter (fun c => 2 ≤ p s c)).card) → (∀ s, size s = ∑ c, p s c) →
    ∀ a : ℕ, 1 ≤ a → (∀ s, size s ≤ a) → 2 * Real.logb l a + 2 ≤ (N0 : ℝ) - 1 →
    SBSat ℂ_[l] colN p hp →
    ∀ δ : MvPolynomial (ZMod d × Fin N0 × Fin N0) ℂ_[l] →ₗ[ℂ_[l]] ℂ_[l],
      (∀ P ∈ nablaO (K := ℂ_[l]) colN p hp, ‖δ P‖ ≤ 1) →
      ‖δ (frameJet colN p hp I (thetaZ g U ε be))‖ ≤
        ‖(l : ℂ_[l])‖ ^ ((∑ s ∈ TT, (topTerm l d TT nu1 nu2 s -
            gam l * (Wcap l d TT nu1 nu2 size s : ℝ))) +
          Fnum l d (fun s => (Dl d TT nu1 size s : ℝ)) -
          ((d : ℝ) * N0 * N1) * (Real.logb l (a : ℝ) + 1))
end Formalism.DworkPowerSeriesWeights


