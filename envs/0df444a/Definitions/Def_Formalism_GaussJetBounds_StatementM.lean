-- Prove2me | Definitions.Def_Formalism_GaussJetBounds_StatementM
-- name    : Formalism_GaussJetBounds_StatementM
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:00:34.015806+00:00
-- url     : https://prove2.me/theorems/8f43399b-1a83-4f4c-baff-aa19963c198a
-- title:
--   Statement M
-- statement:
--   Definitions and structural lemmas for Statement M, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/StatementM.lean

import Definitions.Def_Formalism_GaussJetBounds_StatementK
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
def IsGeneric {K : Type u} [NormedField K] {σ : Type} (l : ℕ) (Y : σ → K) : Prop :=
  ∀ P : MvPolynomial σ ℤ, MvPolynomial.map (Int.castRingHom (ZMod l)) P ≠ 0 →
    ‖MvPolynomial.aeval Y P‖ = 1
def genFrame {K : Type u} [Field K] {d N0 : ℕ} (TT : Finset (ZMod d)) (l m : ℕ)
    (Y : ZMod d × Fin N0 × Fin N0 → K) : ZMod d × Fin N0 × Fin N0 → K :=
  fun y => if y.1 ∈ TT ∧ y.2.1.val = 0 then Y y ^ (l ^ m) else Y y
def ThmAGeneric : Prop :=
  ∀ (K : Type u) [NormedField K] [IsUltrametricDist K] [CharZero K] (l d N0 N1 : ℕ) [NeZero d],
    l.Prime → 3 ≤ l → 2 ≤ d → Even d → ‖(l : K)‖ < 1 → 0 < N0 →
    ∀ (K0 : Subfield K), Unram l K0 → ∀ ζ : K, IsPrimitiveRoot ζ (l ^ d - 1) →
    ∀ be : MvPowerSeries (ZMod d) K, BHyp l d K0 ζ be →
    ∀ g : ZV d N0 N1 → MvPowerSeries (ZV d N0 N1) K, (∀ y, MvPowerSeries.constantCoeff (g y) = 0) →
      (∀ y, MvPowerSeries.subst g (entLog (K := K) l y) = MvPowerSeries.X y) →
    ∀ U : MvPowerSeries (ZV d N0 N1) K, Integral U → ∀ (ε : K), (ε = 1 ∨ ε = -1) →
    ∀ (TT : Finset (ZMod d)) (colN : ZMod d → ℕ) (p : ∀ s, Fin (colN s) → ℕ)
      (hp : ∀ s c, p s c ≤ N0), (∀ s c, 1 ≤ p s c) → ∀ (I : ∀ s c, Fin (p s c) → Fin N1),
    ∀ Y : ZMod d × Fin N0 × Fin N0 → K, IsGeneric l Y →
    ∀ (nu1 nu2 size : ZMod d → ℕ), (∀ s, nu1 s = colN s) →
      (∀ s, nu2 s = (Finset.univ.filter (fun c => 2 ≤ p s c)).card) → (∀ s, size s = ∑ c, p s c) →
    ∀ a : ℕ, 1 ≤ a → (∀ s, size s ≤ a) →
    ∀ (J : ZMod d → ℕ) (lab : ∀ s, Fin (J s) → ZMod d × ℤ), (∀ s, Function.Injective (lab s)) →
      (∀ (s s0 : ZMod d) (j : ℤ), (∃ i, lab s i = (s0, j)) ↔
        (s0 ∈ TT ∧ Odd j ∧ s = s0 + (j : ZMod d) ∧ (0 < j → l ^ j.toNat ≤ nu1 s0) ∧
          (j < 0 → l ^ (-j).toNat ≤ size s))) →
      (∀ s, J s + (if s ∈ TT then 1 else 0) ≤ N0) →
    ∀ m : ℕ, (∀ s i, (-(lab s i).2).toNat ≤ m) →
      ‖jetPair (∏ s : ZMod d, minorProd
            (fun (i : Fin N0) (b : Fin N1) => (MvPolynomial.X (s, i, b) : MvPolynomial (ZV d N0 N1) K))
            (p s) (hp s) (I s))
          (MvPowerSeries.subst (linSub (frameM (N1 := N1) (genFrame TT l m Y)))
              (MvPowerSeries.subst g U) *
            mvExp (ε • bSum (frameM (N1 := N1) (genFrame TT l m Y)) be))‖ ≤
        ‖(l : K)‖ ^ ((∑ s ∈ TT, (topTerm l d TT nu1 nu2 s - gam l * (Wcap l d TT nu1 nu2 size s : ℝ))) +
          Fnum l d (fun s => (Dl d TT nu1 size s : ℝ)) -
          ((d : ℝ) * N0 * N1) * (Real.logb l (a : ℝ) + 1))
def GenericExists : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (σ : Type) [Finite σ],
    ∃ (K : Type) (_ : NormedField K), IsUltrametricDist K ∧ CharZero K ∧
      ∃ (φ : ℂ_[l] →+* K) (Y : σ → K), (∀ z, ‖φ z‖ = ‖z‖) ∧
        (∀ P : MvPolynomial σ ℂ_[l],
          ‖MvPolynomial.eval₂ φ Y P‖ = ⨆ n : σ →₀ ℕ, ‖MvPolynomial.coeff n P‖) ∧
        IsGeneric l Y
end Formalism.DworkPowerSeriesWeights


