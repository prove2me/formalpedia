-- Prove2me | Definitions.Def_Formalism_GaussJetBounds_StatementU
-- name    : Formalism_GaussJetBounds_StatementU
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:06:14.267607+00:00
-- url     : https://prove2.me/theorems/8c05c08e-fd8f-472f-af65-f787892ba211
-- title:
--   Statement U
-- statement:
--   Definitions and structural lemmas for Statement U, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/StatementU.lean

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
open Formalism.IncomingBounds
def thetaOne {K : Type} [NormedField K] [CharZero K] {N0 N1 : ℕ}
    (g : Fin N0 × Fin N1 → MvPowerSeries (Fin N0 × Fin N1) K)
    (U : MvPowerSeries (Fin N0 × Fin N1) K) (sgn ep : K) (be : MvPowerSeries (ZMod 2) K) :
    MvPowerSeries (Fin N0 × Fin N1) K :=
  MvPowerSeries.subst g U * mvExp ((sgn / 2) • ∑ x : Fin N0 × Fin N1, MvPowerSeries.subst
    (fun s : ZMod 2 => (if s = 0 then (1 : K) else ep) •
      (MvPowerSeries.X x : MvPowerSeries (Fin N0 × Fin N1) K)) be)
def frameJetOne {K : Type} [Field K] {N0 N1 C : ℕ} (p : Fin C → ℕ) (hp : ∀ c, p c ≤ N0)
    (I : ∀ c, Fin (p c) → Fin N1) (Th : MvPowerSeries (Fin N0 × Fin N1) K) :
    MvPolynomial (Fin N0 × Fin N0) K :=
  jetPairPoly (minorProd
    (fun (i : Fin N0) (b : Fin N1) =>
      (∑ a : Fin N0, MvPolynomial.C (MvPolynomial.X (i, a)) * MvPolynomial.X (a, b) :
        MvPolynomial (Fin N0 × Fin N1) (MvPolynomial (Fin N0 × Fin N0) K))) p hp I) Th
def OneLetterGauss : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (N0 N1 C : ℕ), 3 ≤ l →
    ∀ (K0 : Subfield ℂ_[l]), Unram l K0 → ∀ ζ : ℂ_[l], IsPrimitiveRoot ζ (l ^ 2 - 1) →
    ∀ be : MvPowerSeries (ZMod 2) ℂ_[l], BHyp l 2 K0 ζ be → ∀ ep : ℂ_[l], ‖ep‖ = 1 →
    ∀ g : Fin N0 × Fin N1 → MvPowerSeries (Fin N0 × Fin N1) ℂ_[l],
      (∀ y, MvPowerSeries.constantCoeff (g y) = 0) →
      (∀ y, MvPowerSeries.subst g (oneLog (K := ℂ_[l]) l y) = MvPowerSeries.X y) →
    ∀ U : MvPowerSeries (Fin N0 × Fin N1) ℂ_[l], Integral U →
    ∀ (sgn : ℂ_[l]), (sgn = 1 ∨ sgn = -1) →
    ∀ (p : Fin C → ℕ) (hp : ∀ c, p c ≤ N0) (I : ∀ c, Fin (p c) → Fin N1) (a : ℕ), 1 ≤ a →
      (∑ c, p c) ≤ a → ∀ n : (Fin N0 × Fin N0) →₀ ℕ,
      ‖MvPolynomial.coeff n (frameJetOne p hp I (thetaOne g U sgn ep be))‖ ≤
        ‖(l : ℂ_[l])‖ ^ (rho l * ((∑ c, p c : ℕ) : ℝ) -
          ((N0 : ℝ) * N1) * (Real.logb l (a : ℝ) + 1))
end Formalism.DworkPowerSeriesWeights


