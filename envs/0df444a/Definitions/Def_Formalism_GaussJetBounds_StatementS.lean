-- Prove2me | Definitions.Def_Formalism_GaussJetBounds_StatementS
-- name    : Formalism_GaussJetBounds_StatementS
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:04:48.832865+00:00
-- url     : https://prove2.me/theorems/95a03b67-1a72-4d2e-b684-f7931c313d9b
-- title:
--   Statement S
-- statement:
--   Definitions and structural lemmas for Statement S, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/StatementS.lean

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
def unitBall (K : Type) [NormedField K] [IsUltrametricDist K] : Subring K where
  carrier := {x | ‖x‖ ≤ 1}
  mul_mem' := fun {a b} ha hb => by
    simp only [Set.mem_ofPred_eq, norm_mul] at *
    exact mul_le_one₀ ha (norm_nonneg _) hb
  one_mem' := by simp
  add_mem' := fun {a b} ha hb => by
    simp only [Set.mem_ofPred_eq] at *
    exact (IsUltrametricDist.norm_add_le_max a b).trans (max_le ha hb)
  zero_mem' := by simp
  neg_mem' := fun {a} ha => by simpa using ha
def xMinors {K : Type} [Field K] {d N0 : ℕ} [NeZero d] (colN : ZMod d → ℕ)
    (p : ∀ s, Fin (colN s) → ℕ) (hp : ∀ s c, p s c ≤ N0) :
    Set (MvPolynomial (ZMod d × Fin N0 × Fin N0) K) :=
  {P | ∃ A : ∀ s c, Fin (p s c) → Fin N0, P = ∏ s : ZMod d, minorProd
    (fun (i a : Fin N0) => (MvPolynomial.X (s, i, a) : MvPolynomial (ZMod d × Fin N0 × Fin N0) K))
    (p s) (hp s) (A s)}
def nablaK {K : Type} [Field K] {d N0 : ℕ} [NeZero d] (colN : ZMod d → ℕ)
    (p : ∀ s, Fin (colN s) → ℕ) (hp : ∀ s c, p s c ≤ N0) :
    Submodule K (MvPolynomial (ZMod d × Fin N0 × Fin N0) K) :=
  Submodule.span K (xMinors colN p hp)
def nablaO {K : Type} [NormedField K] [IsUltrametricDist K] {d N0 : ℕ} [NeZero d]
    (colN : ZMod d → ℕ) (p : ∀ s, Fin (colN s) → ℕ) (hp : ∀ s c, p s c ≤ N0) :
    Submodule (unitBall K) (MvPolynomial (ZMod d × Fin N0 × Fin N0) K) :=
  Submodule.span (unitBall K) (xMinors colN p hp)
def SBSat (K : Type) [NormedField K] [IsUltrametricDist K] {d N0 : ℕ} [NeZero d]
    (colN : ZMod d → ℕ) (p : ∀ s, Fin (colN s) → ℕ) (hp : ∀ s c, p s c ≤ N0) : Prop :=
  ∀ P ∈ nablaK (K := K) colN p hp, (∀ n, ‖MvPolynomial.coeff n P‖ ≤ 1) → P ∈ nablaO colN p hp
def CBMem : Prop :=
  ∀ (K : Type) [Field K] (d N0 N1 : ℕ) [NeZero d] (colN : ZMod d → ℕ)
    (p : ∀ s, Fin (colN s) → ℕ) (hp : ∀ s c, p s c ≤ N0) (I : ∀ s c, Fin (p s c) → Fin N1)
    (Th : MvPowerSeries (ZV d N0 N1) K), frameJet colN p hp I Th ∈ nablaK colN p hp
def ThmAWeyl : Prop :=
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
    ∀ c : ℂ_[l], ‖(l : ℂ_[l])‖ ^ ((∑ s ∈ TT, (topTerm l d TT nu1 nu2 s -
            gam l * (Wcap l d TT nu1 nu2 size s : ℝ))) +
          Fnum l d (fun s => (Dl d TT nu1 size s : ℝ)) -
          ((d : ℝ) * N0 * N1) * (Real.logb l (a : ℝ) + 1)) ≤ ‖c‖ →
      c⁻¹ • frameJet colN p hp I (thetaZ g U ε be) ∈ nablaO colN p hp
end Formalism.DworkPowerSeriesWeights


