-- Prove2me | Definitions.Def_Formalism_MeanHeightDescent_StatementF
-- name    : Formalism_MeanHeightDescent_StatementF
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T01:37:12.675039+00:00
-- url     : https://prove2.me/theorems/9c363ecc-6308-4f3f-9122-16da5efdde73
-- title:
--   Statement F
-- statement:
--   Definitions and structural lemmas for Statement F, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MeanHeightDescent/StatementF.lean

import Mathlib
import Definitions.Def_Formalism_MeanHeightDescent_StatementA
import Definitions.Def_Formalism_MeanHeightDescent_CombinedAverageDegreeBound
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
def CovolumeEstimateOfAverageDegree : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K] (d D : ℕ),
    0 < D → d = D →
    ∀ XW : InfinitePlace K → Matrix (Fin d) (Fin d) ℂ, (∀ v, IsUnit (XW v).det) →
    ∀ M : Submodule (𝓞 K) (Fin d → K), Submodule.IsLattice K M →
    ∀ (Pl : Type) [Fintype Pl] (w c1 ua : Pl → ℝ)
      (ι : Type) [Fintype ι] [Nonempty ι] (T DY A cs X cc z ρ R1 R2 Bn δ' : ℝ)
      (h sl δc dc degc : ι → ℝ) (Ca Cb PPf e1 e2 : ℝ)
      (muU muA muN muG mmax dA dB dN dg db : ℝ)
      (Cf Cc cfl ε δ Q P Λ G P9 : ℝ)
      (pq q' logOm x eps L b rd Lchi llx LL0 B0 f m k S η : ℝ),

    0 ≤ DY → 3 * DY + 5 ≤ T → 0 < A → 0 ≤ cs → 0 ≤ X → 0 ≤ cc → 0 ≤ z → z < 1 → 0 ≤ ρ → ρ < 1 →
    0 ≤ R1 → 0 ≤ R2 → 0 < Bn → 0 < δ' →
    (∀ c, δ' ≤ δc c ∧ δc c ≤ δ' / (1 - ρ)) →
    (∀ c, Bn * δc c ≤ dc c ∧ (1 - z) * dc c ≤ Bn * δc c) →
    (∀ c, 0 ≤ h c + cs) →
    (∀ c, (1 - ρ) * max 0 (sl c + cs) ≤ h c + cs + cc) →
    -X ≤ (∑ c, sl c) / (Fintype.card ι : ℝ) →
    (∀ c, Bn * δc c *
        (T * h c - 3 * (DY + 1) * |h c| - A * Real.log (2 + |h c|) - R1 - 2 * z * R2) ≤ degc c) →
    T * X ≤ Ca * LL0 * (∑ τ, ua τ) + e1 → T * cc ≤ Cb * LL0 * (∑ τ, ua τ) + e2 →
    cs * (6 * DY + 10 + T * (z + 2 * ρ)) + (A * Real.log (max A 1) + 4) + R1 + 2 * z * R2 + PPf
      + e1 + e2 ≤ b / 4 →
    2 * ((∑ c, degc c) / (∑ c, dc c) - PPf) ≤ muU →

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
    B0 = f * m * b * x ^ eps → 0 ≤ Ca → 0 ≤ Cb → 0 ≤ Cf → 0 ≤ Cc →
    Formalism.DivisionValues.lcv XW M / D ≤
      (∑ ρ, pq * w ρ * logOm) + (64 * (Ca + Cb + 3 * Cf) + 8 * Cc + 2) * B0 * llx
end Formalism.ExtensionFiltration


