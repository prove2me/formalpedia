-- Prove2me | Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_NormNatCastLeOfDvd
-- name    : Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_NormNatCastLeOfDvd
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T23:02:32.186571+00:00
-- url     : https://prove2.me/theorems/b44a5d59-db70-4af6-a564-74b8021a6ff0
-- title:
--   Norm Nat Cast Le Of Dvd
-- statement:
--   Definitions and structural lemmas for Norm Nat Cast Le Of Dvd, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/NormNatCastLeOfDvd.lean

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_StatementE
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ConstantCoeffAevalLinP
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_jetPair_C_mul_right
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_jetPair_eq_sum
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_jetPair_sum_right

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
namespace ETerm
open Formalism.DworkPowerSeriesWeights (Integral jetPair mfact jetPair_eq_sum jetPair_C_mul_right jetPair_sum_right)
section Mono
variable {Tp Lw : Type}
def jn (e : Tp →₀ ℕ) (n : Lw →₀ ℕ) : Tp ⊕ Lw →₀ ℕ := e.mapDomain Sum.inl + n.mapDomain Sum.inr
end Mono
section Op
variable {K Tp Lw : Type} [Field K]
variable {κ : Type} [Fintype κ]
def ext0 (b : κ → Lw → K) (k : κ) : Tp ⊕ Lw → K := Sum.elim 0 (b k)
end Op
section Ser
variable {K σ : Type} [Field K]
def Agree (D : ℕ) (f f' : MvPowerSeries σ K) : Prop :=
  ∀ n : σ →₀ ℕ, n.degree ≤ D → MvPowerSeries.coeff n f = MvPowerSeries.coeff n f'
end Ser
section Low
variable {K Tp Lw : Type} [Field K] [Fintype Lw]
def LowGe (m : ℕ) (V : MvPowerSeries (Tp ⊕ Lw) K) : Prop :=
  ∀ n, MvPowerSeries.coeff n V ≠ 0 → m ≤ lowDeg n
end Low
section Norm
variable {K : Type} [NormedField K] [IsUltrametricDist K]
end Norm
section Main
variable {K Tp Lw Φ κ : Type} [NormedField K] [IsUltrametricDist K] [Fintype Tp] [Fintype Lw]
  [Fintype Φ] [Fintype κ]
def piece (p : ℕ) (Z Y : MvPowerSeries (Tp ⊕ Lw) K) (aA : Φ → K) (dA : Φ → Tp →₀ ℕ) (aB : κ → K)
    (dB : κ → Tp →₀ ℕ) (b : κ → Lw → K) : Φ ⊕ κ ⊕ Fin 2 → MvPowerSeries (Tp ⊕ Lw) K :=
  Sum.elim (fun φ => MvPowerSeries.C (aA φ) * topMonoS (dA φ))
    (Sum.elim (fun k => MvPowerSeries.C (aB k) * topMonoS (dB k) * lowLin (b k))
      (fun t => if t = 0 then Z else MvPowerSeries.C (p : K) * Y))
def dTot (dA : Φ → Tp →₀ ℕ) (dB : κ → Tp →₀ ℕ) (k : Φ ⊕ κ ⊕ Fin 2 → ℕ) : Tp ⊕ Lw →₀ ℕ :=
  ∑ φ, k (Sum.inl φ) • (dA φ).mapDomain Sum.inl +
    ∑ x, k (Sum.inr (Sum.inl x)) • (dB x).mapDomain Sum.inl
def cTot (p : ℕ) (aA : Φ → K) (aB : κ → K) (k : Φ ⊕ κ ⊕ Fin 2 → ℕ) : K :=
  (∏ φ, aA φ ^ k (Sum.inl φ)) * (∏ x, aB x ^ k (Sum.inr (Sum.inl x))) *
    (p : K) ^ k (Sum.inr (Sum.inr 1))
def valid (p : ℕ) (aA : Φ → K) (dA : Φ → Tp →₀ ℕ) (aB : κ → K) (dB : κ → Tp →₀ ℕ) (b : κ → Lw → K)
    (e : Tp →₀ ℕ) (Q : MvPolynomial Lw K) (w : (Φ → ℕ) × (κ →₀ ℕ) × ℕ × (Lw →₀ ℕ)) : Prop :=
  w.2.2.2 ∈ (hasseDir b w.2.1 Q).support ∧ (∀ φ, w.1 φ ≠ 0 → aA φ ≠ 0) ∧
    (∀ k, w.2.1 k ≠ 0 → aB k ≠ 0) ∧
    (∀ τ, ∑ φ, w.1 φ * dA φ τ + ∑ k, w.2.1 k * dB k τ ≤ e τ) ∧ p * w.2.2.1 ≤ w.2.2.2.degree
def bnd (K : Type) [NormedField K] (p : ℕ) (e : Tp →₀ ℕ)
    (w : (Φ → ℕ) × (κ →₀ ℕ) × ℕ × (Lw →₀ ℕ)) : ℝ :=
  (p : ℝ) ^ (∑ φ, w.1 φ + ∑ k, w.2.1 k + w.2.2.1) * ‖((mfact e : ℕ) : K)‖ *
    ‖(((∑ k, w.2.1 k).factorial : ℕ) : K)‖ * ‖((mfact w.2.2.2 : ℕ) : K)‖
end Main
end ETerm
open Formalism.DworkPowerSeriesWeights (Integral jetPair mfact)
end Formalism.InvariantFactorPaths.G7


