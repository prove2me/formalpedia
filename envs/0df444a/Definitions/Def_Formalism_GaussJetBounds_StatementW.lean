-- Prove2me | Definitions.Def_Formalism_GaussJetBounds_StatementW
-- name    : Formalism_GaussJetBounds_StatementW
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:26:44.164887+00:00
-- url     : https://prove2.me/theorems/b2ff89b7-6942-46fe-9c86-a7550091c6a6
-- title:
--   Statement W
-- statement:
--   Definitions and structural lemmas for Statement W, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/StatementW.lean

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
def HasJetBound {K : Type} [NormedField K] {ι σ : Type} (g : ι → MvPowerSeries ι K)
    (E : MvPowerSeries ι K) (P : MvPolynomial ι (MvPolynomial σ K)) (B : ℝ) : Prop :=
  ∀ U : MvPowerSeries ι K, Integral U → ∀ n : σ →₀ ℕ,
    ‖MvPolynomial.coeff n (jetPairPoly P (MvPowerSeries.subst g U * E))‖ ≤ B
def serAlong {K : Type} [Field K] {ι κ : Type} (e : ι → κ) (f : MvPowerSeries ι K) :
    MvPowerSeries κ K :=
  MvPowerSeries.subst (fun i => (MvPowerSeries.X (e i) : MvPowerSeries κ K)) f
def opAlong {K : Type} [Field K] {ι κ σ τ : Type} (e : ι → κ) (e' : σ → τ)
    (P : MvPolynomial ι (MvPolynomial σ K)) : MvPolynomial κ (MvPolynomial τ K) :=
  MvPolynomial.rename e (MvPolynomial.map (MvPolynomial.rename e' : MvPolynomial σ K →ₐ[K]
    MvPolynomial τ K).toRingHom P)
def OrbitsMul : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] (ι₁ ι₂ σ₁ σ₂ : Type) [Finite ι₁] [Finite ι₂]
    (g₁ : ι₁ → MvPowerSeries ι₁ K) (g₂ : ι₂ → MvPowerSeries ι₂ K),
    (∀ x, MvPowerSeries.constantCoeff (g₁ x) = 0) → (∀ x, MvPowerSeries.constantCoeff (g₂ x) = 0) →
    ∀ (E₁ : MvPowerSeries ι₁ K) (E₂ : MvPowerSeries ι₂ K)
      (P₁ : MvPolynomial ι₁ (MvPolynomial σ₁ K)) (P₂ : MvPolynomial ι₂ (MvPolynomial σ₂ K))
      (B₁ B₂ : ℝ), HasJetBound g₁ E₁ P₁ B₁ → HasJetBound g₂ E₂ P₂ B₂ →
      HasJetBound (ι := ι₁ ⊕ ι₂) (σ := σ₁ ⊕ σ₂)
        (Sum.elim (fun x => serAlong Sum.inl (g₁ x)) (fun x => serAlong Sum.inr (g₂ x)))
        (serAlong Sum.inl E₁ * serAlong Sum.inr E₂)
        (opAlong Sum.inl Sum.inl P₁ * opAlong Sum.inr Sum.inr P₂) (B₁ * B₂)
end Formalism.DworkPowerSeriesWeights


