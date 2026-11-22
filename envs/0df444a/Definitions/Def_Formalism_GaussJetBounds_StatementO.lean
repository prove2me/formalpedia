-- Prove2me | Definitions.Def_Formalism_GaussJetBounds_StatementO
-- name    : Formalism_GaussJetBounds_StatementO
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T20:45:32.097498+00:00
-- url     : https://prove2.me/theorems/fa1a5262-f43e-4411-9411-70077c972afb
-- title:
--   Statement O
-- statement:
--   Definitions and structural lemmas for Statement O, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/StatementO.lean

import Definitions.Def_Formalism_GaussJetBounds_GenLogInverse
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
namespace Formalism.DworkPowerSeriesWeights
open Formalism.IncomingBounds
def LemmaRWt : Prop :=
  ∀ (K : Type u) [NormedField K] [IsUltrametricDist K] [CharZero K] (l d N0 N1 : ℕ) [NeZero d],
    l.Prime → Odd l → 2 ≤ d → Even d → ‖(l : K)‖ < 1 →
    ∀ (K0 : Subfield K), Unram l K0 → ∀ ζ : K, IsPrimitiveRoot ζ (l ^ d - 1) →
    ∀ be : MvPowerSeries (ZMod d) K, BHyp l d K0 ζ be →
    ∀ (ι : Type v) [Fintype ι] [DecidableEq ι] (M : ZV d N0 N1 → ι → K), (∀ x i, ‖M x i‖ ≤ 1) →
    ∀ (ε : K), (ε = 1 ∨ ε = -1) → ∀ (sig : ι → ℝ), (∀ i, 0 ≤ sig i) → ∀ κ : ι →₀ ℕ,
      (∀ (i j : ι) (α β : ℕ), pureMon l i j α β ≤ κ →
        ¬ MonoWtGe ‖(l : K)‖ (fun _ => rho l) (1 / ((l : ℝ) - 1)) (pureMon l i j α β)
            (MvPowerSeries.coeff (pureMon l i j α β) (bSum M be)) →
        1 ≤ (l : ℝ) ^ α * sig i + (l : ℝ) ^ β * sig j) →
      MvPowerSeries.constantCoeff (ε • bSum M be) = 0 ∧
      ∀ n, n ≤ κ → MonoWtGe ‖(l : K)‖ (fun i => rho l + sig i) (1 / ((l : ℝ) - 1)) n
        (MvPowerSeries.coeff n (ε • bSum M be))
def UWt : Prop :=
  ∀ (K : Type u) [NormedField K] [IsUltrametricDist K] [CharZero K] (l : ℕ), l.Prime →
    ‖(l : K)‖ < 1 → ∀ (τ : Type w) [Finite τ] [DecidableEq τ] (p : τ → τ)
    (g : τ → MvPowerSeries τ K), (∀ x, MvPowerSeries.constantCoeff (g x) = 0) →
      (∀ x, MvPowerSeries.subst g (genLog (K := K) l p x) = MvPowerSeries.X x) →
    ∀ U : MvPowerSeries τ K, Integral U →
    ∀ (ι : Type v) [Fintype ι] (M : τ → ι → K), (∀ x i, ‖M x i‖ ≤ 1) →
    ∀ (sig : ι → ℝ), (∀ i, 0 ≤ sig i) →
      WtGe ‖(l : K)‖ (fun i => rho l + sig i) 0
        (MvPowerSeries.subst (fun x => (∑ i, MvPowerSeries.C (M x i) * MvPowerSeries.X i :
          MvPowerSeries ι K)) (MvPowerSeries.subst g U))
def RCoreA : Prop :=
  ∀ (K : Type u) [NormedField K] [IsUltrametricDist K] [CharZero K] (l : ℕ), l.Prime →
    ‖(l : K)‖ < 1 → ∀ (ι : Type v) [Fintype ι] (sig : ι → ℝ) (κ : ι →₀ ℕ) (a : ℕ), 1 ≤ a →
      (∀ i, κ i ≤ a) → ∀ (B U : MvPowerSeries ι K), MvPowerSeries.constantCoeff B = 0 →
      (∀ n, n ≤ κ → MonoWtGe ‖(l : K)‖ (fun i => rho l + sig i) (1 / ((l : ℝ) - 1)) n
        (MvPowerSeries.coeff n B)) →
      (∀ n, n ≤ κ → MonoWtGe ‖(l : K)‖ (fun i => rho l + sig i) 0 n (MvPowerSeries.coeff n U)) →
      ‖((mfact κ : ℕ) : K) * MvPowerSeries.coeff κ (U * mvExp B)‖ ≤
        ‖(l : K)‖ ^ ((∑ i, (κ i : ℝ) * (gam l - sig i)) -
          (Fintype.card ι : ℝ) * (Real.logb l (a : ℝ) + 1))
def OrbitsAddA : Prop :=
  ∀ (K : Type u) [NormedField K] [IsUltrametricDist K] [CharZero K] (l : ℕ), l.Prime →
    ‖(l : K)‖ < 1 → ∀ (ι₁ : Type v) (ι₂ : Type w) [Fintype ι₁] [Fintype ι₂] (sig₁ : ι₁ → ℝ)
      (sig₂ : ι₂ → ℝ) (κ : (ι₁ ⊕ ι₂) →₀ ℕ) (a : ℕ), 1 ≤ a → (∀ i, κ i ≤ a) →
    ∀ (B₁ : MvPowerSeries ι₁ K) (B₂ : MvPowerSeries ι₂ K) (U : MvPowerSeries (ι₁ ⊕ ι₂) K),
      MvPowerSeries.constantCoeff B₁ = 0 → MvPowerSeries.constantCoeff B₂ = 0 →
      (∀ n : ι₁ →₀ ℕ, (∀ i, n i ≤ κ (Sum.inl i)) →
        MonoWtGe ‖(l : K)‖ (fun i => rho l + sig₁ i) (1 / ((l : ℝ) - 1)) n
          (MvPowerSeries.coeff n B₁)) →
      (∀ n : ι₂ →₀ ℕ, (∀ i, n i ≤ κ (Sum.inr i)) →
        MonoWtGe ‖(l : K)‖ (fun i => rho l + sig₂ i) (1 / ((l : ℝ) - 1)) n
          (MvPowerSeries.coeff n B₂)) →
      (∀ n, n ≤ κ → MonoWtGe ‖(l : K)‖ (fun i => rho l + Sum.elim sig₁ sig₂ i) 0 n
        (MvPowerSeries.coeff n U)) →
      ‖((mfact κ : ℕ) : K) * MvPowerSeries.coeff κ (U * mvExp
          (MvPowerSeries.subst (fun i : ι₁ => (MvPowerSeries.X (Sum.inl i) : MvPowerSeries (ι₁ ⊕ ι₂) K)) B₁ +
            MvPowerSeries.subst (fun i : ι₂ => (MvPowerSeries.X (Sum.inr i) : MvPowerSeries (ι₁ ⊕ ι₂) K)) B₂))‖ ≤
        ‖(l : K)‖ ^ ((∑ i, (κ (Sum.inl i) : ℝ) * (gam l - sig₁ i)) +
          (∑ i, (κ (Sum.inr i) : ℝ) * (gam l - sig₂ i)) -
          ((Fintype.card ι₁ : ℝ) + Fintype.card ι₂) * (Real.logb l (a : ℝ) + 1))
end Formalism.DworkPowerSeriesWeights


