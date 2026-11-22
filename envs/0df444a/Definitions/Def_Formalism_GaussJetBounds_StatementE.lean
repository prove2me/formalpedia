-- Prove2me | Definitions.Def_Formalism_GaussJetBounds_StatementE
-- name    : Formalism_GaussJetBounds_StatementE
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T20:40:50.768798+00:00
-- url     : https://prove2.me/theorems/471dcbd8-0c98-4520-b461-a57139b50f0e
-- title:
--   Statement E
-- statement:
--   Definitions and structural lemmas for Statement E, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/StatementE.lean

import Definitions.Def_Formalism_GaussJetBounds_StatementA
import Definitions.Def_Formalism_GaussJetBounds_StatementC
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
def frameTop {d N0 N1 : ℕ} (TT : Finset (ZMod d)) (y : ZV d N0 N1) : Bool :=
  decide (y.1 ∈ TT ∧ y.2.1.val = 0)
def ThmAJet : Prop :=
  ∀ (K : Type u) [NormedField K] [IsUltrametricDist K] [CharZero K] (l d N0 N1 : ℕ) [NeZero d],
    l.Prime → 3 ≤ l → 2 ≤ d → Even d → ‖(l : K)‖ < 1 → ∀ (h0 : 0 < N0),
    ∀ (K0 : Subfield K), Unram l K0 → ∀ ζ : K, IsPrimitiveRoot ζ (l ^ d - 1) →
    ∀ be : MvPowerSeries (ZMod d) K, BHyp l d K0 ζ be →
    ∀ x : ZMod d × Fin N0 × Fin N0 → K, (∀ y, ‖x y‖ ≤ 1) →
    ∀ g : ZV d N0 N1 → MvPowerSeries (ZV d N0 N1) K, (∀ y, MvPowerSeries.constantCoeff (g y) = 0) →
      (∀ y, MvPowerSeries.subst g (entLog (K := K) l y) = MvPowerSeries.X y) →
    ∀ U : MvPowerSeries (ZV d N0 N1) K, Integral U → ∀ (ε : K), (ε = 1 ∨ ε = -1) →
    ∀ (TT : Finset (ZMod d)) (nu1 nu2 size : ZMod d → ℕ), (∀ s, nu2 s ≤ nu1 s) →
      (∀ s, nu1 s ≤ size s) →
    ∀ (spec : ZMod d × Fin N0 → Option (ZMod d × ℤ)) (κ : ZV d N0 N1 →₀ ℕ),
      (∀ s ∈ TT, (∑ b : Fin N1, κ (s, ⟨0, h0⟩, b)) = nu1 s) →
      (∀ s, (∑ y ∈ Finset.univ.filter (fun y : ZV d N0 N1 => y.1 = s ∧ frameTop TT y = false), κ y) =
        Dl d TT nu1 size s) →
      (∀ (s : ZMod d) (k : Fin N0) (s0 : ZMod d) (j : ℤ), spec (s, k) = some (s0, j) →
        s0 ∈ TT ∧ Odd j ∧ s = s0 + (j : ZMod d) ∧ ¬ (s ∈ TT ∧ k.val = 0) ∧
        (0 < j → l ^ j.toNat ≤ nu1 s0) ∧ (j < 0 → l ^ (-j).toNat ≤ size s)) →
      (∀ (s0 : ZMod d) (j : ℤ),
        (∑ y ∈ Finset.univ.filter (fun y : ZV d N0 N1 => spec (y.1, y.2.1) = some (s0, j)), κ y) ≤
          capL d TT nu1 nu2 (s0 + (j : ZMod d))) →
      (∀ s0 ∈ TT, ∀ (s : ZMod d) (k : Fin N0) (j : ℤ), ¬ (s ∈ TT ∧ k.val = 0) → Odd j →
        s = s0 + (j : ZMod d) → (0 < j → l ^ j.toNat ≤ nu1 s0) → (j < 0 → l ^ (-j).toNat ≤ size s) →
        spec (s, k) ≠ some (s0, j) →
        (if 0 ≤ j then ‖∑ a : Fin N0, x (s0, ⟨0, h0⟩, a) ^ (l ^ j.toNat) * x (s, k, a)‖
          else ‖∑ a : Fin N0, x (s0, ⟨0, h0⟩, a) * x (s, k, a) ^ (l ^ (-j).toNat)‖) ≤ ‖(l : K)‖) →
      ‖((mfact κ : ℕ) : K) * MvPowerSeries.coeff κ
          (MvPowerSeries.subst (linSub (frameM (N1 := N1) x)) (MvPowerSeries.subst g U) *
            mvExp (ε • bSum (frameM (N1 := N1) x) be))‖ ≤
        ‖(l : K)‖ ^ ((∑ s ∈ TT, (topTerm l d TT nu1 nu2 s - gam l * (Wcap l d TT nu1 nu2 size s : ℝ))) +
          Fnum l d (fun s => (Dl d TT nu1 size s : ℝ)) -
          (Fintype.card (ZV d N0 N1) : ℝ) * (Real.logb l (κ.degree : ℝ) + 1))
end Formalism.DworkPowerSeriesWeights


