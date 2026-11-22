-- Prove2me | Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_StatementAB
-- name    : Formalism_ThetaLogCoordinates_UniformThetaSubstitution_StatementAB
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T22:45:05.39814+00:00
-- url     : https://prove2.me/theorems/e89c58f2-9d9b-4a28-85f4-746cbb9e1600
-- title:
--   Statement AB
-- statement:
--   Definitions and structural lemmas for Statement AB, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/StatementAB.lean

import Mathlib
import Definitions.Def_Formalism_GrowthSums_StatementA
import Definitions.Def_Formalism_GaussJetBounds_StatementI
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
open Finset
namespace Formalism.InvariantFactorPaths.G7
open Formalism.DworkPowerSeriesWeights (jetPair)
open Formalism.GrowthSums (gamP rhoP gainG excessGain)
def linS {K ι : Type} [Field K] [Fintype ι] (b : ι → K) : MvPowerSeries ι K :=
  ∑ x, MvPowerSeries.C (b x) * MvPowerSeries.X x
def shiftPoly {K ι κ : Type} [Field K] [Fintype κ] (b : κ → ι → K) (Q : MvPolynomial ι K) :
    MvPolynomial κ (MvPolynomial ι K) :=
  MvPolynomial.aeval (fun x : ι => (MvPolynomial.C (MvPolynomial.X x) +
    ∑ k, MvPolynomial.C (MvPolynomial.C (b k x)) * MvPolynomial.X k :
      MvPolynomial κ (MvPolynomial ι K))) Q
def hasseDir {K ι κ : Type} [Field K] [Fintype κ] (b : κ → ι → K) (β : κ →₀ ℕ)
    (Q : MvPolynomial ι K) : MvPolynomial ι K :=
  MvPolynomial.coeff β (shiftPoly b Q)
def JetPairingHasseIdentity : Prop :=
  ∀ (K ι κ : Type) [Field K] [Fintype ι] [Fintype κ] (b : κ → ι → K) (β : κ →₀ ℕ)
    (Q : MvPolynomial ι K) (G : MvPowerSeries ι K),
    jetPair Q ((∏ k, linS (b k) ^ β k) * G) =
      ((∏ k, (β k).factorial : ℕ) : K) * jetPair (hasseDir b β Q) G
def HasseDerivIntegralHomogeneous : Prop :=
  ∀ (K ι κ : Type) [NormedField K] [IsUltrametricDist K] [Fintype κ] (b : κ → ι → K)
    (β : κ →₀ ℕ) (Q : MvPolynomial ι K),
    ((∀ n, ‖MvPolynomial.coeff n Q‖ ≤ 1) → (∀ k x, ‖b k x‖ ≤ 1) →
      ∀ n, ‖MvPolynomial.coeff n (hasseDir b β Q)‖ ≤ 1) ∧
    (∀ d, Q.IsHomogeneous d → (hasseDir b β Q).IsHomogeneous (d - ∑ k, β k)) ∧
    (∀ d, Q.IsHomogeneous d → d < ∑ k, β k → hasseDir b β Q = 0)
def HasseDerivProdVanish : Prop :=
  ∀ (K ι κ : Type) [Field K] [Fintype κ] (b : κ → ι → K) (C : ℕ)
    (f : Fin C → MvPolynomial ι K) (m : Fin C → ℕ) (S : Finset κ),
    (∀ c (β' : κ →₀ ℕ), m c < ∑ k ∈ S, β' k → hasseDir b β' (f c) = 0) →
    ∀ β : κ →₀ ℕ, ∑ c, m c < ∑ k ∈ S, β k → hasseDir b β (∏ c, f c) = 0
def colDir {K σ : Type} [Field K] [DecidableEq σ] {r0 r1 : ℕ} (s : σ) (ξ : Fin r0 → K) (b : Fin r1) :
    σ × Fin r0 × Fin r1 → K :=
  fun x => if x.1 = s ∧ x.2.2 = b then ξ x.2.1 else 0
def minorAt {K σ : Type} [Field K] {r0 r1 l : ℕ} (s : σ) (T : Fin l → Fin r0 → K)
    (I : Fin l → Fin r1) : MvPolynomial (σ × Fin r0 × Fin r1) K :=
  (Matrix.of fun (i c : Fin l) =>
    (∑ a, MvPolynomial.C (T i a) * MvPolynomial.X (s, a, I c) :
      MvPolynomial (σ × Fin r0 × Fin r1) K)).det
def MinorHits : Prop :=
  ∀ (K σ κ : Type) [Field K] [DecidableEq σ] [Fintype κ] (r0 r1 l : ℕ) (s : σ)
    (T : Fin l → Fin r0 → K) (I : Fin l → Fin r1) (pos : κ → σ) (ξ : κ → Fin r0 → K)
    (col : κ → Fin r1) (β : κ →₀ ℕ),
    ((∃ k, 2 ≤ β k) ∨
      (∃ k k', k ≠ k' ∧ 1 ≤ β k ∧ 1 ≤ β k' ∧ pos k = pos k' ∧ (ξ k = ξ k' ∨ col k = col k')) ∨
      (∃ k, 1 ≤ β k ∧ (pos k ≠ s ∨ col k ∉ Set.range I))) →
    hasseDir (fun k => colDir (pos k) (ξ k) (col k)) β (minorAt s T I) = 0
def HitsCap : Prop :=
  ∀ (K σ κ : Type) [Field K] [DecidableEq σ] [Fintype κ] (r0 r1 C : ℕ) (l : Fin C → ℕ)
    (sf : Fin C → σ) (T : ∀ c, Fin (l c) → Fin r0 → K) (I : ∀ c, Fin (l c) → Fin r1) (pos : κ → σ)
    (ξ : κ → Fin r0 → K) (col : κ → Fin r1) (S : Finset κ),
    (∀ k ∈ S, ∀ k' ∈ S, pos k = pos k' ∧ ξ k = ξ k') →
    ∀ β : κ →₀ ℕ, C < ∑ k ∈ S, β k →
      hasseDir (fun k => colDir (pos k) (ξ k) (col k)) β (∏ c, minorAt (sf c) (T c) (I c)) = 0
def HitsColumns : Prop :=
  ∀ (K σ κ : Type) [Field K] [DecidableEq σ] [Fintype κ] (r0 r1 C : ℕ) (l : Fin C → ℕ)
    (sf : Fin C → σ) (T : ∀ c, Fin (l c) → Fin r0 → K) (I : ∀ c, Fin (l c) → Fin r1) (pos : κ → σ)
    (ξ : κ → Fin r0 → K) (col : κ → Fin r1) (S : Finset κ) (J : Finset (Fin r1)),
    (∀ k ∈ S, ∀ k' ∈ S, pos k = pos k') → (∀ k ∈ S, col k ∈ J) →
    ∀ β : κ →₀ ℕ, ∑ c, ((univ.image (I c)) ∩ J).card < ∑ k ∈ S, β k →
      hasseDir (fun k => colDir (pos k) (ξ k) (col k)) β (∏ c, minorAt (sf c) (T c) (I c)) = 0
def EdgeScale : Prop :=
  ∀ (K σ : Type) [Field K] (r0 r1 l : ℕ) (s : σ) (T : Fin l → Fin r0 → K) (I : Fin l → Fin r1)
    (τ : Fin r1 → K),
    MvPolynomial.aeval (fun x : σ × Fin r0 × Fin r1 =>
        (MvPolynomial.C (τ x.2.2) * MvPolynomial.X x : MvPolynomial (σ × Fin r0 × Fin r1) K))
      (minorAt s T I) = MvPolynomial.C (∏ c, τ (I c)) * minorAt s T I
def ColumnCount : Prop :=
  ∀ (μ : YoungDiagram) (i : ℕ),
    ∑ a ∈ range i, μ.rowLen a = ∑ c ∈ range (μ.rowLen 0), min (μ.colLen c) i
def lgN (p x : ℕ) : ℕ := if x = 0 then 0 else Nat.log p x + 1
def FactorialLg : Prop :=
  ∀ (p m : ℕ), p.Prime → (m : ℝ) / ((p : ℝ) - 1) - lgN p m ≤ (padicValNat p m.factorial : ℝ)
def deLoss {S : Type} [Fintype S] (p r0 r1 : ℕ) (TT : Finset S) (al ls : S → ℕ) : ℝ :=
  ∑ s, ((r1 : ℝ) * lgN p (al s) + (r0 : ℝ) * r1 * lgN p (ls s)) + ∑ s ∈ TT, ((lgN p (al s) : ℝ)) ^ 2
def StarArith : Prop :=
  ∀ (S : Type) [Fintype S] (p r0 r1 : ℕ) (TT : Finset S) (al ls : S → ℕ)
    (e : S → Fin r1 → ℕ) (a : S → Fin r0 × Fin r1 → ℕ) (i : S → ℕ → ℕ) (E : Finset ℕ) (i0 i2 : ℕ),
    p.Prime → (∀ s, s ∉ TT → al s = 0) → (∀ s, ∑ b, e s b = al s) →
    (∀ s, ∑ x, a s x ≤ ls s) → (∀ s e', e' ∉ E → i s e' = 0) → (∀ s, s ∉ TT → ∀ e', i s e' = 0) →
    (∀ s e', p ^ (2 * e' + 1) * i s e' ≤ al s) →
    (∑ s, ∑ x, a s x + ∑ s, ∑ e' ∈ E, i s e' = ∑ s, ls s) → p * i2 ≤ ∑ s, ls s →
    gamP p * ∑ s ∈ TT, (al s : ℝ) - i0 - ∑ s ∈ TT, ∑ e' ∈ E, (i s e' : ℝ) - deLoss p r0 r1 TT al ls ≤
      (∑ s, ∑ b, (padicValNat p (e s b).factorial : ℝ)) +
        (∑ s, ∑ e' ∈ E, (padicValNat p (i s e').factorial : ℝ)) +
        (∑ s, ∑ x, (padicValNat p (a s x).factorial : ℝ)) -
        rhoP p * (∑ s, ((al s : ℝ) + ls s)) - (i0 + ∑ s, ∑ e' ∈ E, (i s e' : ℝ) + i2)
def ChargeLemma : Prop :=
  ∀ (n : ℕ) (s s' : ZMod n) (a a' d : ℕ), a' < a → s + (a : ZMod n) = s' + (a' : ZMod n) →
    IsLeast {e : ℕ | 1 ≤ e ∧ s + (e : ZMod n) = s'} d → d ≤ a
def ExcessGainBound : Prop :=
  ∀ (n : ℕ) (p : ℝ) (TT : Finset (ZMod n)) (D : ZMod n → Finset ℕ) (al cap : ZMod n → ℝ)
    (de v : ℝ) (i ch : ZMod n → ℕ → ℝ) (E : Finset ℕ),
    1 < p → (∀ s, 0 ≤ al s) → (∀ s, 0 ≤ cap s) → (∀ s e, 0 ≤ i s e) → (∀ s e, 0 ≤ ch s e) →
    (∀ s e, e ∉ E → i s e = 0 ∧ ch s e = 0) → (∀ s e, 2 * e + 1 ∉ D s → ch s e = 0) →
    gamP p * ∑ s ∈ TT, al s - ∑ s ∈ TT, ∑ e ∈ E, ch s e - ∑ s ∈ TT, ∑ e ∈ E, i s e - de ≤ v →
    (∀ s ∈ TT, ∀ e, 2 * e + 1 ∈ D s → ch s e + i s e ≤ al s / p ^ (2 * e + 1)) →
    (∀ s ∈ TT, ∀ e, 2 * e + 1 ∉ D s →
      i s e ≤ min (al s / p ^ (2 * e + 1)) (cap (s + ((2 * e + 1 : ℕ) : ZMod n)))) →
    excessGain p TT D al cap de ≤ v
def BCore : Prop :=
  ∀ (n : ℕ) (p : ℝ) (TT TTodd : Finset (ZMod n)) (al cap : ZMod n → ℝ) (de v paid : ℝ)
    (i : ZMod n → ℕ → ℝ) (E : Finset ℕ),
    1 < p → TTodd ⊆ TT → (∀ s, 0 ≤ al s) → (∀ s, 0 ≤ cap s) → (∀ s e, 0 ≤ i s e) →
    (∀ s e, e ∉ E → i s e = 0) →
    gamP p * ∑ s ∈ TT, al s - ∑ s ∈ TT, ∑ e ∈ E, i s e - de + paid ≤ v →
    ∑ s ∈ TT \ TTodd, ∑ e ∈ E, i s e ≤ paid →
    (∀ s ∈ TTodd, ∀ e,
      i s e ≤ min (al s / p ^ (2 * e + 1)) (cap (s + ((2 * e + 1 : ℕ) : ZMod n)))) →
    gainG p TT TTodd al cap de ≤ v
end Formalism.InvariantFactorPaths.G7


