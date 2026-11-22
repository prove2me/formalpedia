-- Prove2me | Definitions.Def_Formalism_MeanHeightDescent_StatementA
-- name    : Formalism_MeanHeightDescent_StatementA
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:08:29.544001+00:00
-- url     : https://prove2.me/theorems/15f0a90f-7439-4f56-92ff-001a80481199
-- title:
--   Statement A
-- statement:
--   Definitions and structural lemmas for Statement A, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MeanHeightDescent/StatementA.lean

import Mathlib
import Definitions.Def_Formalism_MeanHeightDescent_MuMaxMinkowski
import Definitions.Def_Formalism_MeanHeightDescent_BadRowsNumeric
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Module NumberField
noncomputable section
namespace Formalism.ExtensionFiltration
def SlopeLowerChain : Prop :=
  ∀ (Pl : Type) [Fintype Pl] (w c1 ua : Pl → ℝ)
    (muU muA muN muG muM mmax dA dB d dg db : ℝ)
    (C1 Cf LL0 L b rd m q' cfl ε δ Q P Λ G P9 : ℝ),

    -(2 * (C1 * LL0 * (∑ τ, ua τ) + b / 4)) ≤ muU →

    cfl = (∑ τ, w τ * c1 τ) - Cf * q' * Real.log rd * (∑ τ, w τ) - Cf * L →
    muU + 2 * cfl ≤ muA →

    0 < dA → dA ≤ dB → (1 - ε) * dB ≤ dA → 0 ≤ ε → 0 ≤ P →
    dA * (muA - P) + (dB - dA) * (-Λ) ≤ dB * muN →
    |2 * cfl| ≤ Q → Λ ≤ Q → ε * Q ≤ b / 4 →

    0 < d → d = dg + db → 0 ≤ db → db ≤ 3 * δ * d → 0 ≤ δ → δ ≤ 1 / 12 →
    d * muN ≤ dg * muG + db * (mmax + G) → |muN| ≤ Q → mmax ≤ Q → G ≤ Q →

    muG - P9 ≤ muM →
    P + 12 * δ * Q + P9 ≤ b →

    0 ≤ C1 → 0 ≤ Cf → 0 ≤ q' → q' ≤ m → (∀ τ, 0 ≤ w τ) → (∀ τ, m * w τ / 2 ≤ ua τ) →
    0 ≤ Real.log rd → Real.log rd ≤ LL0 → L ≤ LL0 → 1 ≤ (∑ τ, ua τ) → 0 ≤ b →
    2 * ((∑ τ, w τ * c1 τ) - (C1 + 3 * Cf) * LL0 * (∑ τ, ua τ) - b) ≤ muM
def CovolumeFromSlope : Prop :=
  ∀ (Pl : Type) [Fintype Pl] (w c1 ua : Pl → ℝ)
    (lcvD C Cc pq q' logOm x eps L b rd Lchi llx LL0 B0 f m k S η : ℝ),
    2 * ((∑ τ, w τ * c1 τ) - C * LL0 * (∑ τ, ua τ) - b) ≤ -lcvD →
    (∀ τ, |c1 τ + pq * logOm / 2| ≤ Cc * q' * (Real.log rd + Lchi)) →
    (∀ τ, 0 ≤ ua τ ∧ ua τ ≤ 2 * (m * w τ + k * S + k * η)) →
    (∀ τ, 0 ≤ w τ ∧ w τ ≤ 2 * b) → k * S ≤ b → k * η ≤ b →
    (Fintype.card Pl : ℝ) ≤ f → 1 ≤ m → 1 ≤ f → 0 ≤ q' → q' ≤ m →
    1 ≤ x → 0 < eps → L = x ^ eps → b = Real.exp L → 1 ≤ rd → Real.log rd ≤ L →
    0 ≤ Lchi → Lchi ≤ L → Real.log x ≤ L → 1 ≤ llx →
    LL0 = Real.log (b * rd) * llx + Lchi + Real.log x →
    B0 = f * m * b * x ^ eps → 0 ≤ C → 0 ≤ Cc →
    lcvD ≤ (∑ ρ, pq * w ρ * logOm) + (64 * C + 8 * Cc + 2) * B0 * llx
def CovolumeEstimateOfSlopeChain : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K] (d D : ℕ),
    0 < D → d = D →
    ∀ XW : InfinitePlace K → Matrix (Fin d) (Fin d) ℂ, (∀ v, IsUnit (XW v).det) →
    ∀ M : Submodule (𝓞 K) (Fin d → K), Submodule.IsLattice K M →
    ∀ (Pl : Type) [Fintype Pl] (w c1 ua : Pl → ℝ)
      (muU muA muN muG mmax dA dB dN dg db : ℝ)
      (C1 Cf Cc cfl ε δ Q P Λ G P9 : ℝ)
      (pq q' logOm x eps L b rd Lchi llx LL0 B0 f m k S η : ℝ),

    -(2 * (C1 * LL0 * (∑ τ, ua τ) + b / 4)) ≤ muU →

    cfl = (∑ τ, w τ * c1 τ) - Cf * q' * Real.log rd * (∑ τ, w τ) - Cf * L →
    muU + 2 * cfl ≤ muA →

    0 < dA → dA ≤ dB → (1 - ε) * dB ≤ dA → 0 ≤ ε → 0 ≤ P →
    dA * (muA - P) + (dB - dA) * (-Λ) ≤ dB * muN →
    |2 * cfl| ≤ Q → Λ ≤ Q → ε * Q ≤ b / 4 →

    0 < dN → dN = dg + db → 0 ≤ db → db ≤ 3 * δ * dN → 0 ≤ δ → δ ≤ 1 / 12 →
    dN * muN ≤ dg * muG + db * (mmax + G) → |muN| ≤ Q → mmax ≤ Q → G ≤ Q →

    muG - P9 ≤ Formalism.HN.muDef (Pi.basisFun K (Fin d)) XW M →
    P + 12 * δ * Q + P9 ≤ b →

    (∀ τ, |c1 τ + pq * logOm / 2| ≤ Cc * q' * (Real.log rd + Lchi)) →

    (∀ τ, m * w τ / 2 ≤ ua τ ∧ ua τ ≤ 2 * (m * w τ + k * S + k * η)) → 1 ≤ (∑ τ, ua τ) →
    (∀ τ, 0 ≤ w τ ∧ w τ ≤ 2 * b) → k * S ≤ b → k * η ≤ b →
    (Fintype.card Pl : ℝ) ≤ f → 1 ≤ m → 1 ≤ f → 0 ≤ q' → q' ≤ m →

    1 ≤ x → 0 < eps → L = x ^ eps → b = Real.exp L → 1 ≤ rd → Real.log rd ≤ L →
    0 ≤ Lchi → Lchi ≤ L → Real.log x ≤ L → 1 ≤ llx →
    LL0 = Real.log (b * rd) * llx + Lchi + Real.log x →
    B0 = f * m * b * x ^ eps → 0 ≤ C1 → 0 ≤ Cf → 0 ≤ Cc →
    Formalism.DivisionValues.lcv XW M / D ≤
      (∑ ρ, pq * w ρ * logOm) + (64 * (C1 + 3 * Cf) + 8 * Cc + 2) * B0 * llx
def WeightedSumBoundWithErrorTerm : Prop :=
  ∀ (J Pl : Type) [Fintype J] [Fintype Pl] (mu0 Fo LG E3 logOm B0 Nc llx xe m C3 Cn : ℝ)
    (Lj E1 E2 pq : J → ℝ) (w : J → Pl → ℝ),
    mu0 ≤ (∑ j, Lj j) + 2 * Fo + LG + (∑ j, (E1 j + E2 j)) + E3 →
    (∀ j, Lj j = (∑ ρ, pq j * w j ρ * logOm) + C3 * B0 * llx) →
    LG + (∑ j, (E1 j + E2 j)) + E3 ≤ Cn * m * xe * (B0 + Nc) →
    (Fintype.card J : ℝ) = m → llx ≤ xe → 0 ≤ B0 → 0 ≤ Nc → 0 ≤ C3 → 0 ≤ xe →
    ∃ Eb : ℝ, mu0 ≤ (∑ j, ∑ ρ, pq j * w j ρ * logOm) + 2 * Fo + Eb ∧
      Eb ≤ (C3 + Cn) * m * xe * (B0 + Nc)
end Formalism.ExtensionFiltration


