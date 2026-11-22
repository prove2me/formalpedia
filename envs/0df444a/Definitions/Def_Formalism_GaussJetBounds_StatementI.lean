-- Prove2me | Definitions.Def_Formalism_GaussJetBounds_StatementI
-- name    : Formalism_GaussJetBounds_StatementI
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T20:47:29.767499+00:00
-- url     : https://prove2.me/theorems/19ab412a-1f20-491e-838d-feffc1f34aaf
-- title:
--   Statement I
-- statement:
--   Definitions and structural lemmas for Statement I, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/StatementI.lean

import Definitions.Def_Formalism_GaussJetBounds_StatementG
import Definitions.Def_Formalism_GaussJetBounds_StatementH
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
def jetPair {K : Type u} [Field K] {ι : Type} (P : MvPolynomial ι K) (Th : MvPowerSeries ι K) : K :=
  ∑ κ ∈ P.support, MvPolynomial.coeff κ P * ((mfact κ : ℕ) : K) * MvPowerSeries.coeff κ Th
def rowOp {K : Type u} [Field K] {d N0 N1 : ℕ} (TT : Finset (ZMod d))
    (T : ZMod d → Fin N0 → Fin N0 → K) (s : ZMod d) (i : Fin N0) (b : Fin N1) :
    MvPolynomial (ZV d N0 N1) K :=
  if s ∈ TT ∧ i.val = 0 then MvPolynomial.X (s, i, b)
  else ∑ k : Fin N0, if s ∈ TT ∧ k.val = 0 then 0
    else MvPolynomial.C (T s i k) * MvPolynomial.X (s, k, b)
def ThmAOp : Prop :=
  ∀ (K : Type u) [NormedField K] [IsUltrametricDist K] [CharZero K] (l d N0 N1 : ℕ) [NeZero d],
    l.Prime → 3 ≤ l → 2 ≤ d → Even d → ‖(l : K)‖ < 1 → ∀ (h0 : 0 < N0),
    ∀ (K0 : Subfield K), Unram l K0 → ∀ ζ : K, IsPrimitiveRoot ζ (l ^ d - 1) →
    ∀ be : MvPowerSeries (ZMod d) K, BHyp l d K0 ζ be →
    ∀ x : ZMod d × Fin N0 × Fin N0 → K, (∀ y, ‖x y‖ ≤ 1) →
    ∀ g : ZV d N0 N1 → MvPowerSeries (ZV d N0 N1) K, (∀ y, MvPowerSeries.constantCoeff (g y) = 0) →
      (∀ y, MvPowerSeries.subst g (entLog (K := K) l y) = MvPowerSeries.X y) →
    ∀ U : MvPowerSeries (ZV d N0 N1) K, Integral U → ∀ (ε : K), (ε = 1 ∨ ε = -1) →
    ∀ (TT : Finset (ZMod d)) (colN : ZMod d → ℕ) (p : ∀ s, Fin (colN s) → ℕ)
      (hp : ∀ s c, p s c ≤ N0), (∀ s c, 1 ≤ p s c) → ∀ (I : ∀ s c, Fin (p s c) → Fin N1)
      (T : ZMod d → Fin N0 → Fin N0 → K), (∀ s i k, ‖T s i k‖ ≤ 1) →
    ∀ (nu1 nu2 size : ZMod d → ℕ), (∀ s, nu1 s = colN s) →
      (∀ s, nu2 s = (Finset.univ.filter (fun c => 2 ≤ p s c)).card) → (∀ s, size s = ∑ c, p s c) →
    ∀ a : ℕ, 1 ≤ a → (∀ s, size s ≤ a) →
    ∀ (spec : ZMod d × Fin N0 → Option (ZMod d × ℤ)),
      (∀ (s : ZMod d) (k : Fin N0) (s0 : ZMod d) (j : ℤ), spec (s, k) = some (s0, j) →
        s0 ∈ TT ∧ Odd j ∧ s = s0 + (j : ZMod d) ∧ ¬ (s ∈ TT ∧ k.val = 0) ∧
        (0 < j → l ^ j.toNat ≤ nu1 s0) ∧ (j < 0 → l ^ (-j).toNat ≤ size s)) →
      (∀ r r' : ZMod d × Fin N0, spec r ≠ none → spec r = spec r' → r = r') →
      (∀ s0 ∈ TT, ∀ (s : ZMod d) (k : Fin N0) (j : ℤ), ¬ (s ∈ TT ∧ k.val = 0) → Odd j →
        s = s0 + (j : ZMod d) → (0 < j → l ^ j.toNat ≤ nu1 s0) → (j < 0 → l ^ (-j).toNat ≤ size s) →
        spec (s, k) ≠ some (s0, j) →
        (if 0 ≤ j then ‖∑ a : Fin N0, x (s0, ⟨0, h0⟩, a) ^ (l ^ j.toNat) * x (s, k, a)‖
          else ‖∑ a : Fin N0, x (s0, ⟨0, h0⟩, a) * x (s, k, a) ^ (l ^ (-j).toNat)‖) ≤ ‖(l : K)‖) →
      ‖jetPair (∏ s : ZMod d, minorProd (rowOp (N1 := N1) TT T s) (p s) (hp s) (I s))
          (MvPowerSeries.subst (linSub (frameM (N1 := N1) x)) (MvPowerSeries.subst g U) *
            mvExp (ε • bSum (frameM (N1 := N1) x) be))‖ ≤
        ‖(l : K)‖ ^ ((∑ s ∈ TT, (topTerm l d TT nu1 nu2 s - gam l * (Wcap l d TT nu1 nu2 size s : ℝ))) +
          Fnum l d (fun s => (Dl d TT nu1 size s : ℝ)) -
          ((d : ℝ) * N0 * N1) * (Real.logb l (a : ℝ) + 1))
end Formalism.DworkPowerSeriesWeights


