-- Prove2me | Definitions.Def_Formalism_GaussJetBounds_StatementK
-- name    : Formalism_GaussJetBounds_StatementK
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T20:58:09.32295+00:00
-- url     : https://prove2.me/theorems/cec89f33-5b12-4a76-8f6d-7a7e5599887c
-- title:
--   Statement K
-- statement:
--   Definitions and structural lemmas for Statement K, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/StatementK.lean

import Definitions.Def_Formalism_GaussJetBounds_StatementJ
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
universe u
namespace Formalism.DworkPowerSeriesWeights
open Formalism.IncomingBounds
def ThmAFrame : Prop :=
  ∀ (K : Type u) [NormedField K] [IsUltrametricDist K] [CharZero K] (l d N0 N1 : ℕ) [NeZero d],
    l.Prime → 3 ≤ l → 2 ≤ d → Even d → ‖(l : K)‖ < 1 → ∀ (h0 : 0 < N0),
    ∀ (K0 : Subfield K), Unram l K0 → ∀ ζ : K, IsPrimitiveRoot ζ (l ^ d - 1) →
    ∀ be : MvPowerSeries (ZMod d) K, BHyp l d K0 ζ be →
    ∀ g : ZV d N0 N1 → MvPowerSeries (ZV d N0 N1) K, (∀ y, MvPowerSeries.constantCoeff (g y) = 0) →
      (∀ y, MvPowerSeries.subst g (entLog (K := K) l y) = MvPowerSeries.X y) →
    ∀ U : MvPowerSeries (ZV d N0 N1) K, Integral U → ∀ (ε : K), (ε = 1 ∨ ε = -1) →
    ∀ (TT : Finset (ZMod d)) (colN : ZMod d → ℕ) (p : ∀ s, Fin (colN s) → ℕ)
      (hp : ∀ s c, p s c ≤ N0), (∀ s c, 1 ≤ p s c) → ∀ (I : ∀ s c, Fin (p s c) → Fin N1),
    ∀ xg : ZMod d × Fin N0 × Fin N0 → K, (∀ y, ‖xg y‖ ≤ 1) →
    ∀ (nu1 nu2 size : ZMod d → ℕ), (∀ s, nu1 s = colN s) →
      (∀ s, nu2 s = (Finset.univ.filter (fun c => 2 ≤ p s c)).card) → (∀ s, size s = ∑ c, p s c) →
    ∀ a : ℕ, 1 ≤ a → (∀ s, size s ≤ a) →
    ∀ (J : ZMod d → ℕ) (lab : ∀ s, Fin (J s) → ZMod d × ℤ), (∀ s, Function.Injective (lab s)) →
      (∀ (s s0 : ZMod d) (j : ℤ), (∃ i, lab s i = (s0, j)) ↔
        (s0 ∈ TT ∧ Odd j ∧ s = s0 + (j : ZMod d) ∧ (0 < j → l ^ j.toNat ≤ nu1 s0) ∧
          (j < 0 → l ^ (-j).toNat ≤ size s))) →
    ∀ (lam : ∀ s, Fin (J s) → Fin N0 → K), (∀ s i a, ‖lam s i a‖ ≤ 1) →
      (∀ s i a, 0 < (lab s i).2 →
        lam s i a = xg ((lab s i).1, ⟨0, h0⟩, a) ^ (l ^ (lab s i).2.toNat)) →
      (∀ s i a, (lab s i).2 < 0 →
        lam s i a ^ (l ^ (-(lab s i).2).toNat) = xg ((lab s i).1, ⟨0, h0⟩, a)) →
    ∀ (e : ∀ s, Fin (J s) → Fin N0), (∀ s, Function.Injective (e s)) →
      (∀ s i, ¬ (s ∈ TT ∧ (e s i).val = 0)) →
      (∀ s, ‖(Matrix.of fun (i i' : Fin (J s)) => ∑ a, lam s i a * xg (s, e s i', a)).det‖ = 1) →
      ‖jetPair (∏ s : ZMod d, minorProd
            (fun (i : Fin N0) (b : Fin N1) => (MvPolynomial.X (s, i, b) : MvPolynomial (ZV d N0 N1) K))
            (p s) (hp s) (I s))
          (MvPowerSeries.subst (linSub (frameM (N1 := N1) xg)) (MvPowerSeries.subst g U) *
            mvExp (ε • bSum (frameM (N1 := N1) xg) be))‖ ≤
        ‖(l : K)‖ ^ ((∑ s ∈ TT, (topTerm l d TT nu1 nu2 s - gam l * (Wcap l d TT nu1 nu2 size s : ℝ))) +
          Fnum l d (fun s => (Dl d TT nu1 size s : ℝ)) -
          ((d : ℝ) * N0 * N1) * (Real.logb l (a : ℝ) + 1))
end Formalism.DworkPowerSeriesWeights


