-- Prove2me | Definitions.Def_Formalism_GaussJetBounds_OneLetterGaussJets_StatementG
-- name    : Formalism_GaussJetBounds_OneLetterGaussJets_StatementG
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:24:17.441961+00:00
-- url     : https://prove2.me/theorems/6969ba44-5b85-4b65-9bbf-b34af197ebb0
-- title:
--   Statement G
-- statement:
--   Definitions and structural lemmas for Statement G, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/OneLetterGaussJets/StatementG.lean

import Definitions.Def_Formalism_GaussJetBounds_OneLetterGaussJets_OddLevelGainSum
import Definitions.Def_Formalism_GaussJetBounds_StatementX
import Definitions.Def_Formalism_GaussJetBounds_StatementU
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
universe u v w
namespace Formalism.DworkPowerSeriesWeights.OddLevelGainBounds
open Formalism.IncomingBounds
def ThmAGauss7 : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (d N0 N1 : ℕ) [NeZero d], 3 ≤ l → 2 ≤ d → Even d → 0 < N0 →
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
    (∀ s, JnumOneLetter l d TT nu1 size s + (if s ∈ TT then 1 else 0) ≤ N0) →
    ∀ n : (ZMod d × Fin N0 × Fin N0) →₀ ℕ,
      ‖MvPolynomial.coeff n (frameJet colN p hp I (thetaZ g U ε be))‖ ≤
        ‖(l : ℂ_[l])‖ ^ ((∑ s ∈ TT, (topTerm l d TT nu1 nu2 s -
            gam l * (WcapOneLetter l d TT nu1 nu2 size s : ℝ))) +
          Fnum l d (fun s => (Dl d TT nu1 size s : ℝ)) -
          ((d : ℝ) * N0 * N1) * (Real.logb l (kaMaxOneLetter d TT nu1 nu2 : ℝ) + 1))
def ThmAWeyl7 : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (d N0 N1 : ℕ) [NeZero d], 3 ≤ l → 2 ≤ d → Even d → 0 < N0 →
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
    (∀ s, JnumOneLetter l d TT nu1 size s + (if s ∈ TT then 1 else 0) ≤ N0) →
    ∀ c : ℂ_[l], ‖(l : ℂ_[l])‖ ^ ((∑ s ∈ TT, (topTerm l d TT nu1 nu2 s -
            gam l * (WcapOneLetter l d TT nu1 nu2 size s : ℝ))) +
          Fnum l d (fun s => (Dl d TT nu1 size s : ℝ)) -
          ((d : ℝ) * N0 * N1) * (Real.logb l (kaMaxOneLetter d TT nu1 nu2 : ℝ) + 1)) ≤ ‖c‖ →
      c⁻¹ • frameJet colN p hp I (thetaZ g U ε be) ∈ nablaO colN p hp
def ThmAEntry7 : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (d N0 N1 : ℕ) [NeZero d], 3 ≤ l → 2 ≤ d → Even d → 0 < N0 →
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
    (∀ s, JnumOneLetter l d TT nu1 size s + (if s ∈ TT then 1 else 0) ≤ N0) →
    ∀ δ : MvPolynomial (ZMod d × Fin N0 × Fin N0) ℂ_[l] →ₗ[ℂ_[l]] ℂ_[l],
      (∀ P ∈ nablaO (K := ℂ_[l]) colN p hp, ‖δ P‖ ≤ 1) →
      ‖δ (frameJet colN p hp I (thetaZ g U ε be))‖ ≤
        ‖(l : ℂ_[l])‖ ^ ((∑ s ∈ TT, (topTerm l d TT nu1 nu2 s -
            gam l * (WcapOneLetter l d TT nu1 nu2 size s : ℝ))) +
          Fnum l d (fun s => (Dl d TT nu1 size s : ℝ)) -
          ((d : ℝ) * N0 * N1) * (Real.logb l (kaMaxOneLetter d TT nu1 nu2 : ℝ) + 1))
def OneLetterJetBoundTwoForms : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (d N0 N1 : ℕ) [NeZero d], 3 ≤ l → 2 ≤ d → Even d → 0 < N0 →
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
    (∀ s, JnumOneLetter l d TT nu1 size s + (if s ∈ TT then 1 else 0) ≤ N0) →
    ∀ a : ℝ, (l : ℝ) ≤ a → (∀ s, (nu1 s : ℝ) ≤ 2 * a) →
    ∀ δ : MvPolynomial (ZMod d × Fin N0 × Fin N0) ℂ_[l] →ₗ[ℂ_[l]] ℂ_[l],
      (∀ P ∈ nablaO (K := ℂ_[l]) colN p hp, ‖δ P‖ ≤ 1) →
      ‖δ (frameJet colN p hp I (thetaZ g U ε be))‖ ≤
        ‖(l : ℂ_[l])‖ ^ ((∑ s ∈ TT, (topTerm l d TT nu1 nu2 s -
            gam l * (WcapOneLetter l d TT nu1 nu2 size s : ℝ))) +
          Fnum l d (fun s => (Dl d TT nu1 size s : ℝ)) -
          ((d : ℝ) * N0 * N1) * (Real.logb l (2 * a) + 1)) ∧
      ‖δ (frameJet colN p hp I (thetaZ g U ε be))‖ ≤
        ‖(l : ℂ_[l])‖ ^ ((∑ s ∈ TT, (topTerm l d TT nu1 nu2 s -
            gam l * (WcapOneLetter l d TT nu1 nu2 size s : ℝ))) +
          Fnum l d (fun s => (Dl d TT nu1 size s : ℝ)) -
          3 * ((d : ℝ) * N0 * N1) * Real.logb l a)
def OneLetterGauss7 : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (N0 N1 C : ℕ), 3 ≤ l →
    ∀ (K0 : Subfield ℂ_[l]), Unram l K0 → ∀ ζ : ℂ_[l], IsPrimitiveRoot ζ (l ^ 2 - 1) →
    ∀ be : MvPowerSeries (ZMod 2) ℂ_[l], BHyp l 2 K0 ζ be → ∀ ep : ℂ_[l], ‖ep‖ = 1 →
    ∀ g : Fin N0 × Fin N1 → MvPowerSeries (Fin N0 × Fin N1) ℂ_[l],
      (∀ y, MvPowerSeries.constantCoeff (g y) = 0) →
      (∀ y, MvPowerSeries.subst g (oneLog (K := ℂ_[l]) l y) = MvPowerSeries.X y) →
    ∀ U : MvPowerSeries (Fin N0 × Fin N1) ℂ_[l], Integral U →
    ∀ (sgn : ℂ_[l]), (sgn = 1 ∨ sgn = -1) →
    ∀ (p : Fin C → ℕ) (hp : ∀ c, p c ≤ N0) (I : ∀ c, Fin (p c) → Fin N1),
      ∀ n : (Fin N0 × Fin N0) →₀ ℕ,
      ‖MvPolynomial.coeff n (frameJetOne p hp I (thetaOne g U sgn ep be))‖ ≤
        ‖(l : ℂ_[l])‖ ^ (rho l * ((∑ c, p c : ℕ) : ℝ) -
          ((N0 : ℝ) * N1) * (Real.logb l (C : ℝ) + 1))
end Formalism.DworkPowerSeriesWeights.OddLevelGainBounds


