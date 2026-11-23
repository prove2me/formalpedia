-- Prove2me | Definitions.Def_Formalism_MeanHeightDescent_CombinedAverageDegreeBound
-- name    : Formalism_MeanHeightDescent_CombinedAverageDegreeBound
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T01:34:00.473355+00:00
-- url     : https://prove2.me/theorems/5edf5724-4d09-4643-a7d4-4609112857cb
-- title:
--   Combined Average Degree Bound
-- statement:
--   Definitions and structural lemmas for Combined Average Degree Bound, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MeanHeightDescent/CombinedAverageDegreeBound.lean

import Mathlib
import Definitions.Def_Formalism_MeanHeightDescent_BadRowsNumeric
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
namespace Formalism.ExtensionFiltration
def HSRearranged : Prop :=
  ∀ T D h J C0 lρ l0 lβ g lΛD lΛT zc z dc Bd degc : ℝ,
    0 ≤ T → 0 ≤ D → 0 ≤ C0 → 0 ≤ zc → zc ≤ z → z ≤ 1 / 2 → 0 < dc → dc * (1 - zc) = Bd →
    lρ ≤ l0 + C0 * Real.log (2 + |h|) →
    0 ≤ T * (Real.log 2 + l0 + lβ / 2) + lΛD + lΛT →
    (1 - zc) * (T * h - 3 * (D + 1) * |h| - J - C0 * D ^ 2 * (lρ + Real.log T) - (T + D + 1) * lβ
        - (T + D ^ 2) * (g + 2))
      - zc * (T * (Real.log 2 + lρ + lβ / 2) + lΛD + lΛT) ≤ degc / dc →
    Bd * (T * h - 3 * (D + 1) * |h| - (C0 * (C0 * D ^ 2 + 2 * z * T)) * Real.log (2 + |h|)
        - (J + C0 * D ^ 2 * (l0 + Real.log T) + (T + D + 1) * lβ + (T + D ^ 2) * (g + 2))
        - 2 * z * (T * (Real.log 2 + l0 + lβ / 2) + lΛD + lΛT)) ≤ degc
def CombinedAverageDegreeBound : Prop :=
  ∀ (ι : Type) [Fintype ι] [Nonempty ι] (T D A cs X cc z ρ R1 R2 Bn δ' : ℝ)
    (h sl δ dc degc : ι → ℝ) (LL0 U b Ca Cb PPf e1 e2 muU : ℝ),
    0 ≤ D → 3 * D + 5 ≤ T → 0 < A → 0 ≤ cs → 0 ≤ X → 0 ≤ cc → 0 ≤ z → z < 1 → 0 ≤ ρ → ρ < 1 →
    0 ≤ R1 → 0 ≤ R2 → 0 < Bn → 0 < δ' →
    (∀ c, δ' ≤ δ c ∧ δ c ≤ δ' / (1 - ρ)) →
    (∀ c, Bn * δ c ≤ dc c ∧ (1 - z) * dc c ≤ Bn * δ c) →

    (∀ c, 0 ≤ h c + cs) →
    (∀ c, (1 - ρ) * max 0 (sl c + cs) ≤ h c + cs + cc) →
    -X ≤ (∑ c, sl c) / (Fintype.card ι : ℝ) →

    (∀ c, Bn * δ c * (T * h c - 3 * (D + 1) * |h c| - A * Real.log (2 + |h c|) - R1 - 2 * z * R2)
      ≤ degc c) →

    T * X ≤ Ca * LL0 * U + e1 → T * cc ≤ Cb * LL0 * U + e2 →
    cs * (6 * D + 10 + T * (z + 2 * ρ)) + (A * Real.log (max A 1) + 4) + R1 + 2 * z * R2 + PPf
      + e1 + e2 ≤ b / 4 →

    2 * ((∑ c, degc c) / (∑ c, dc c) - PPf) ≤ muU →
    -(2 * ((Ca + Cb) * LL0 * U + b / 4)) ≤ muU
end Formalism.ExtensionFiltration


