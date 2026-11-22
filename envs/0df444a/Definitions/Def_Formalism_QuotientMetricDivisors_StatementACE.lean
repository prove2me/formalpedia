-- Prove2me | Definitions.Def_Formalism_QuotientMetricDivisors_StatementACE
-- name    : Formalism_QuotientMetricDivisors_StatementACE
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T17:41:50.132827+00:00
-- url     : https://prove2.me/theorems/08b19daa-1974-4bb7-b082-a8d4500ce8d2
-- title:
--   Statement ACE
-- statement:
--   Definitions and structural lemmas for Statement ACE, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/StatementACE.lean

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_Statement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder InnerProductSpace
noncomputable section
namespace Formalism.DivisionValues
def StepA : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (w : HeightOneSpectrum (𝓞 K))
    (n D : ℕ) (M : Submodule (𝓞 K) (Fin n → K)) (π : Matrix (Fin D) (Fin n) K)
    (ι : Matrix (Fin D) (Fin D) K)
    (B : (Fin D → K) →ₗ[K] K) (P : (Fin n → K) →ₗ[K] K) (ζ : K) (σ : ℤ),
    ζ ≠ 0 → vw w ζ = 0 →
    (∀ F : Fin n → K, P F = ζ * B (ι.mulVec (π.mulVec F))) →
    (∀ F ∈ M, P F = 0 ∨ σ ≤ vw w (P F)) →
    ∀ x ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (matLat ι (matLat π M)), B x = 0 ∨ σ ≤ vw w (B x)
def StepC : Prop :=
  ∀ (Φ Cs Q E : Type) [NormedAddCommGroup Φ] [InnerProductSpace ℂ Φ]
    [NormedAddCommGroup Cs] [InnerProductSpace ℂ Cs]
    [NormedAddCommGroup Q] [InnerProductSpace ℂ Q] [FiniteDimensional ℂ Q]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (ι : Q →ₗ[ℂ] E), Function.Surjective ι →
    ∀ (Ix : Type) [Fintype Ix] (Qp : Ix → Submodule ℂ Q), (⨆ p, Qp p) = ⊤ →
    ∀ (s : Ix → ℝ) (smin : ℝ), 0 < smin → (∀ p, smin ≤ s p) →
    (∀ p, ∀ x ∈ Qp p, ∀ y : Q, ⟪ι x, ι y⟫_ℂ = (s p : ℂ) * ⟪x, y⟫_ℂ) →
    ∀ (col : Φ → Cs) (k : ℝ), (∀ φ, ‖col φ‖ ≤ k * ‖φ‖) →
    ∀ (P : Cs → Q → ℂ) (p : ℝ), (∀ c F, ‖P c F‖ ≤ p * ‖c‖ * ‖F‖) →
    ∀ B : Φ → E → ℂ, (∀ φ F, B φ (ι F) = P (col φ) F) →
      0 ≤ k → 0 ≤ p → ∀ φ e, ‖B φ e‖ ≤ p * k / Real.sqrt smin * ‖φ‖ * ‖e‖
def StepCMean : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (nB p k s : InfinitePlace K → ℝ),
    (∀ v, 0 < nB v) → (∀ v, 0 < p v) → (∀ v, 0 < k v) → (∀ v, 0 < s v) →
    (∀ v, nB v ≤ p v * k v / Real.sqrt (s v)) →
      (1 / (Fintype.card (InfinitePlace K) : ℝ)) * ∑ v, Real.log (nB v ^ 2) ≤
        (1 / (Fintype.card (InfinitePlace K) : ℝ)) * ∑ v, (Real.log (p v ^ 2) + Real.log (k v ^ 2)) -
          (1 / (Fintype.card (InfinitePlace K) : ℝ)) * ∑ v, Real.log (s v)
def BoundsSum : Prop :=
  ∀ (Pl J : Type) [Fintype J] (S : Finset Pl) (D : ℕ), 0 < D →
    ∀ (lcvR logκ LG E3 : ℝ) (lcvM L E1 E2 : J → ℝ) (l ell vG g : Pl → ℝ)
      (I Ic jT F err Jx η : Pl → J → ℝ),
    (∀ w, 0 ≤ l w) →
    lcvR ≤ (D : ℝ) * logκ + ∑ j, lcvM j +
      ∑ w ∈ S, l w * (vG w + ∑ j, (I w j + Ic w j + jT w j)) →
    (∀ w ∈ S, vG w ≤ (D : ℝ) * g w) → ∑ w ∈ S, l w * g w ≤ LG →
    (∀ j, lcvM j / D ≤ L j) →
    (∀ w ∈ S, ∑ j, (I w j + Ic w j) ≤ (∑ j, (2 * F w j + err w j) + 2 / ell w ^ 2) * D) →
    (∀ w ∈ S, ∀ j, jT w j ≤ Jx w j * D + η w j) →
    (∀ j, ∑ w ∈ S, l w * (err w j + Jx w j) ≤ E1 j) →
    (∀ j, ∑ w ∈ S, l w * η w j / D ≤ E2 j) →
    ∑ w ∈ S, l w * (2 / ell w ^ 2) ≤ E3 →
      lcvR / D ≤ logκ + ∑ j, L j + 2 * ∑ j, ∑ w ∈ S, l w * F w j + LG + ∑ j, (E1 j + E2 j) + E3
end Formalism.DivisionValues


