-- Prove2me | Definitions.Def_Formalism_GaussJetBounds_StatementY
-- name    : Formalism_GaussJetBounds_StatementY
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-24T21:09:59.041943+00:00
-- url     : https://prove2.me/theorems/aa3c1aa0-3e9a-4f9e-a87f-5b511c6e0f6d
-- title:
--   Statement Y
-- statement:
--   Definitions and structural lemmas for Statement Y, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/StatementY.lean

import Definitions.Def_Formalism_GaussJetBounds_StatementN
import Definitions.Def_Formalism_GaussJetBounds_StatementP
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
def ThmBGauss : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (H : Type) [Fintype H] [DecidableEq H] (N0 N1 : ℕ) (S : ℂ_[p])
    (u : H → ℂ_[p]), ‖S‖ ≤ ‖(p : ℂ_[p])‖ ^ (-(1 / 2 : ℝ)) → (∀ t, ‖u t‖ ≤ 1) →
    ∀ sg : MvPowerSeries ((Bool × H) × Fin N0 × Fin N1) ℂ_[p], JetsIntegral sg →
    ∀ (TT : Finset H) (colN : Bool × H → ℕ) (ht : ∀ τ, Fin (colN τ) → ℕ)
      (hht : ∀ τ c, ht τ c ≤ N0), (∀ τ c, 1 ≤ ht τ c) → ∀ (I : ∀ τ c, Fin (ht τ c) → Fin N1),
    ∀ (nu1 nu2 size : Bool × H → ℕ), (∀ τ, nu1 τ = colN τ) →
      (∀ τ, nu2 τ = (Finset.univ.filter (fun c => 2 ≤ ht τ c)).card) →
      (∀ τ, size τ = ∑ c, ht τ c) →
    ∀ n : ((Bool × H) × Fin N0 × Fin N0) →₀ ℕ,
      ‖MvPolynomial.coeff n (jetPairPoly (∏ τ : Bool × H, minorProd
            (fun (i : Fin N0) (b : Fin N1) =>
              (∑ a : Fin N0, MvPolynomial.C (MvPolynomial.X (τ, i, a)) * MvPolynomial.X (τ, a, b) :
                MvPolynomial ((Bool × H) × Fin N0 × Fin N1)
                  (MvPolynomial ((Bool × H) × Fin N0 × Fin N0) ℂ_[p])))
            (ht τ) (hht τ) (I τ))
          (mvExp ((-S) • ∑ t : H, ∑ ab : Fin N0 × Fin N1, MvPowerSeries.C (u t) *
              MvPowerSeries.X ((false, t), ab.1, ab.2) * MvPowerSeries.X ((true, t), ab.1, ab.2)) * sg))‖ ≤
        ‖(p : ℂ_[p])‖ ^ (-(1 / 2 : ℝ) * ∑ t : H, ((size (false, t) : ℝ) -
          (if t ∈ TT then (nu1 (false, t) : ℝ) - nu2 (false, t) else 0) +
          (if t ∈ TT then (nu1 (true, t) : ℝ) else 0)))
end Formalism.DworkPowerSeriesWeights


