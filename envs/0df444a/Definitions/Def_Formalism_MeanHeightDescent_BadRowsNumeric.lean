-- Prove2me | Definitions.Def_Formalism_MeanHeightDescent_BadRowsNumeric
-- name    : Formalism_MeanHeightDescent_BadRowsNumeric
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:06:40.949935+00:00
-- url     : https://prove2.me/theorems/586415f0-64f8-4019-9362-540049e885a2
-- title:
--   Bad Rows Numeric
-- statement:
--   Definitions and structural lemmas for Bad Rows Numeric, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MeanHeightDescent/BadRowsNumeric.lean

import Mathlib
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
def SizesSZ : Prop :=
  ∀ (kc m : ℕ) (c : Fin kc → ℝ) (y : Fin m → ℝ) (w S N t η : ℝ),
    (∀ i, |c i| ≤ S + N + t + 1) → (∀ i, |y i + w| ≤ η + 1) →
    0 ≤ S → 0 ≤ η → N + t + 1 ≤ S + η → η + 1 ≤ w →
    (m : ℝ) * (w - η - 1) ≤ (∑ i, |c i|) + ∑ i, |y i| ∧
    (∑ i, |c i|) + ∑ i, |y i| ≤ 2 * ((m : ℝ) * w + ((kc : ℝ) + 1) * S + ((kc : ℝ) + 1) * η) ∧
    (2 * (η + 1) ≤ w → (m : ℝ) * w / 2 ≤ (∑ i, |c i|) + ∑ i, |y i|)
def MeanHeights : Prop :=
  ∀ (ι : Type) [Fintype ι] [Nonempty ι] (h sl : ι → ℝ) (cs cc ρ X : ℝ),
    0 ≤ ρ → ρ ≤ 1 → 0 ≤ X →
    (∀ c, 0 ≤ h c + cs) →
    (∀ c, (1 - ρ) * max 0 (sl c + cs) ≤ h c + cs + cc) →
    -X ≤ (∑ c, sl c) / (Fintype.card ι : ℝ) →
    max 0 ((1 - ρ) * cs - X - cc) ≤ (∑ c, (h c + cs)) / (Fintype.card ι : ℝ)
def ElemLogA : Prop :=
  ∀ A t : ℝ, 0 < A → 0 ≤ t →
    A * Real.log (2 + t) ≤ 2 * t + A * Real.log (max A 1) + 4
def ElemLogB : Prop :=
  ∀ T D A cs h : ℝ, 0 ≤ D → 0 ≤ cs → -cs ≤ h → 0 < A →
    (T - 3 * D - 5) * (h + cs) - (T + 3 * D + 5) * cs - (A * Real.log (max A 1) + 4) ≤
      T * h - 3 * (D + 1) * |h| - A * Real.log (2 + |h|)
def SumComponents : Prop :=
  ∀ (ι : Type) [Fintype ι] [Nonempty ι] (T D A cs X cc z ρ R1 R2 Bn δ' : ℝ)
    (h δ dc degc : ι → ℝ),
    0 ≤ D → 3 * D + 5 ≤ T → 0 < A → 0 ≤ cs → 0 ≤ X → 0 ≤ cc → 0 ≤ z → z < 1 → 0 ≤ ρ → ρ < 1 →
    0 ≤ R1 → 0 ≤ R2 → 0 < Bn → 0 < δ' →
    (∀ c, δ' ≤ δ c ∧ δ c ≤ δ' / (1 - ρ)) →
    (∀ c, Bn * δ c ≤ dc c ∧ (1 - z) * dc c ≤ Bn * δ c) →
    (∀ c, -cs ≤ h c) →
    (∀ c, Bn * δ c * (T * h c - 3 * (D + 1) * |h c| - A * Real.log (2 + |h c|) - R1 - 2 * z * R2)
      ≤ degc c) →
    max 0 ((1 - ρ) * cs - X - cc) ≤ (∑ c, (h c + cs)) / (Fintype.card ι : ℝ) →
    -(T * (X + cc)) - cs * (6 * D + 10 + T * (z + 2 * ρ)) - (A * Real.log (max A 1) + 4) - R1
        - 2 * z * R2 ≤ (∑ c, degc c) / (∑ c, dc c)
def DescentNumeric : Prop :=
  ∀ dA dB muA muN cfl X P Λ Q ε : ℝ,
    0 < dA → dA ≤ dB → (1 - ε) * dB ≤ dA → 0 ≤ ε → 0 ≤ X → 0 ≤ P →
    dA * (muA - P) + (dB - dA) * (-Λ) ≤ dB * muN →
    cfl - X ≤ muA → |cfl| ≤ Q → Λ ≤ Q →
    cfl - X - P - 2 * ε * Q ≤ muN
def BadRowsNumeric : Prop :=
  ∀ d dg db muN muG mmax G Q δ : ℝ,
    0 < d → d = dg + db → 0 ≤ db → db ≤ 3 * δ * d → 0 ≤ δ → δ ≤ 1 / 12 →
    d * muN ≤ dg * muG + db * (mmax + G) →
    |muN| ≤ Q → mmax ≤ Q → G ≤ Q →
    muN - 12 * δ * Q ≤ muG
end Formalism.ExtensionFiltration


