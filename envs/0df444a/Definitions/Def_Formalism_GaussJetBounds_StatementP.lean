-- Prove2me | Definitions.Def_Formalism_GaussJetBounds_StatementP
-- name    : Formalism_GaussJetBounds_StatementP
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:02:37.042093+00:00
-- url     : https://prove2.me/theorems/e121b4af-cef2-4c4d-a259-ac9e0fe8c16e
-- title:
--   Statement P
-- statement:
--   Definitions and structural lemmas for Statement P, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/StatementP.lean

import Definitions.Def_Formalism_GaussJetBounds_StatementM
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
def idM {K : Type} [Field K] {d N0 N1 : ℕ} : ZV d N0 N1 → ZV d N0 N1 → K :=
  fun x y => if x = y then 1 else 0
def thetaZ {K : Type} [NormedField K] [CharZero K] {d N0 N1 : ℕ} [NeZero d]
    (g : ZV d N0 N1 → MvPowerSeries (ZV d N0 N1) K) (U : MvPowerSeries (ZV d N0 N1) K) (ε : K)
    (be : MvPowerSeries (ZMod d) K) : MvPowerSeries (ZV d N0 N1) K :=
  MvPowerSeries.subst (linSub (idM : ZV d N0 N1 → ZV d N0 N1 → K)) (MvPowerSeries.subst g U) *
    mvExp (ε • bSum (idM : ZV d N0 N1 → ZV d N0 N1 → K) be)
def jetPairPoly {K : Type} [Field K] {σ ι : Type} (P : MvPolynomial ι (MvPolynomial σ K))
    (Th : MvPowerSeries ι K) : MvPolynomial σ K :=
  ∑ κ ∈ P.support, MvPolynomial.coeff κ P *
    MvPolynomial.C (((mfact κ : ℕ) : K) * MvPowerSeries.coeff κ Th)
def frameJet {K : Type} [Field K] {d N0 N1 : ℕ} [NeZero d] (colN : ZMod d → ℕ)
    (p : ∀ s, Fin (colN s) → ℕ) (hp : ∀ s c, p s c ≤ N0) (I : ∀ s c, Fin (p s c) → Fin N1)
    (Th : MvPowerSeries (ZV d N0 N1) K) : MvPolynomial (ZMod d × Fin N0 × Fin N0) K :=
  jetPairPoly (∏ s : ZMod d, minorProd
    (fun (i : Fin N0) (b : Fin N1) =>
      (∑ a : Fin N0, MvPolynomial.C (MvPolynomial.X (s, i, a)) * MvPolynomial.X (s, a, b) :
        MvPolynomial (ZV d N0 N1) (MvPolynomial (ZMod d × Fin N0 × Fin N0) K)))
    (p s) (hp s) (I s)) Th
def ThmAGauss : Prop :=
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
    ∀ n : (ZMod d × Fin N0 × Fin N0) →₀ ℕ,
      ‖MvPolynomial.coeff n (frameJet colN p hp I (thetaZ g U ε be))‖ ≤
        ‖(l : ℂ_[l])‖ ^ ((∑ s ∈ TT, (topTerm l d TT nu1 nu2 s -
            gam l * (Wcap l d TT nu1 nu2 size s : ℝ))) +
          Fnum l d (fun s => (Dl d TT nu1 size s : ℝ)) -
          ((d : ℝ) * N0 * N1) * (Real.logb l (a : ℝ) + 1))
end Formalism.DworkPowerSeriesWeights


