-- Prove2me | Definitions.Def_KLSModular_LevyStochCalc_Brownian_CrossVariation
-- name    : KLSModular_LevyStochCalc_Brownian_CrossVariation
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-25T17:10:49.043229+00:00
-- url     : https://prove2.me/theorems/1ab4e629-ed7f-48bb-b1cc-41ccac0e463c
-- title:
--   One-cell and two-cell simple integrands
-- statement:
--   Vendored from the LevyStochCalc library at https://github.com/cgarryZA/LevyStochCalc, commit 984dbf0b790031eac05d56fe5a84b65e15e1e932. `twoCell` is the simple predictable integrand with coefficient $0$ on the first tile $(0,a]$ and coefficient $Z$ on $(a,b]$, assuming $0<a<b$, measurability, boundedness, and the required left-endpoint adaptedness. `oneCell` is the analogous single-cell integrand with coefficient $Z$ on $(0,b]$; `twoCell_adapted` and `oneCell_adapted` state their coefficient adaptedness.
--
--   **Original module imports**
--
--   ```lean
--   import LevyStochCalc.Brownian.ItoAlgebra
--   import LevyStochCalc.Brownian.CrossOrthogonality
--   ```
--
--   **Original declaration excerpt**
--
--   Shown in the original module context. Body omitted.
--
--   ```lean
--   noncomputable def twoCell {a b : ℝ} (ha : 0 < a) (hab : a < b) (Z : Ω → ℝ)
--       (hZm : Measurable Z) {M : ℝ} (hZb : ∀ ω, |Z ω| ≤ M) : SimplePredictable Ω b
--   ```
--
--   **Module navigation**
--
--   Direct project imports: [`LevyStochCalc/Brownian/ItoAlgebra`](https://prove2.me/theorems/602bc476-bf93-48d5-972e-3d6b80e662e4), [`LevyStochCalc/Brownian/CrossOrthogonality`](https://prove2.me/theorems/85db9236-d8b7-4cbd-8596-d4ebab2e8b3e).
--
--   Theorems in source order:
--
--   - [`integral_mul_cross_increment_eq_zero`](https://prove2.me/theorems/a33f4ff0-a082-4e43-a699-dd56f6c0e63a)
--   - [`condExp_mul_cross_increment_eq_zero`](https://prove2.me/theorems/99d0dc79-016a-4aa6-9626-db8a484a0275)
--
--   Project result: [The KLS conjecture](https://prove2.me/theorems/c4e9e57c-586c-4945-927e-7f33933f1111).
--
--   [Original module](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/vendor/LevyStochCalc/LevyStochCalc/Brownian/CrossVariation.lean) · `LevyStochCalc.Brownian.CrossVariation` · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Brownian/CrossVariation.lean (repository human-ai-mathematics/kls-lean, commit 408915f, module `LevyStochCalc.Brownian.CrossVariation`, definition bundle `KLSModular_LevyStochCalc_Brownian_CrossVariation`; the repository is private at upload time); vendored copy patched by formalization/vendor/port.patch (project file formalization/vendor/LevyStochCalc/LevyStochCalc/Brownian/CrossVariation.lean, lines 33-133). Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0; upstream copyright notice retained in the Lean text).

import Definitions.Def_KLSModular_LevyStochCalc_Brownian_ItoAlgebra
import Definitions.Def_KLSModular_LevyStochCalc_Brownian_CrossOrthogonality

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Modified 2026-10-12 by the KLS formalization project: ported to Lean v4.33.0 and
-- Mathlib db584cd. The changes are listed in vendor/README.md and vendor/port.patch.
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/CrossVariation.lean; Apache-2.0; locally patched, see formalization/vendor/port.patch; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal
namespace LevyStochCalc
namespace Brownian
namespace Ito
universe u
variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
section TwoCell
/-- The simple integrand carrying a coefficient on one cell `(a, b]` and nothing before it. -/
noncomputable def twoCell {a b : ℝ} (ha : 0 < a) (hab : a < b) (Z : Ω → ℝ)
    (hZm : Measurable Z) {M : ℝ} (hZb : ∀ ω, |Z ω| ≤ M) : SimplePredictable Ω b where
  N := 2
  partition := ![0, a, b]
  partition_zero := rfl
  partition_le_T := le_rfl
  partition_strictMono := by
    refine Fin.strictMono_iff_lt_succ.mpr fun i => ?_
    fin_cases i
    · simpa using ha
    · simpa using hab
  ξ := ![fun _ => 0, Z]
  ξ_bounded := by
    intro i
    fin_cases i
    · exact ⟨0, fun ω => by simp⟩
    · exact ⟨M, hZb⟩
  ξ_measurable := by
    intro i
    fin_cases i
    · simp
    · simpa using hZm
theorem twoCell_adapted {a b : ℝ} (ha : 0 < a) (hab : a < b) {Z : Ω → ℝ} (hZm : Measurable Z)
    {M : ℝ} (hZb : ∀ ω, |Z ω| ≤ M) (hZa : StronglyMeasurable[ℱ a] Z) :
    ∀ i : Fin (twoCell ha hab Z hZm hZb).N,
      StronglyMeasurable[ℱ ((twoCell ha hab Z hZm hZb).partition i.castSucc)]
        ((twoCell ha hab Z hZm hZb).ξ i) := by
  intro i
  fin_cases i
  · change StronglyMeasurable[ℱ 0] fun _ : Ω => (0 : ℝ)
    exact stronglyMeasurable_const
  · change StronglyMeasurable[ℱ a] Z
    exact hZa
/-- The simple integrand carrying a coefficient on the single cell `(0, b]`. -/
noncomputable def oneCell {b : ℝ} (hb : 0 < b) (Z : Ω → ℝ)
    (hZm : Measurable Z) {M : ℝ} (hZb : ∀ ω, |Z ω| ≤ M) : SimplePredictable Ω b where
  N := 1
  partition := ![0, b]
  partition_zero := rfl
  partition_le_T := le_rfl
  partition_strictMono := by
    refine Fin.strictMono_iff_lt_succ.mpr fun i => ?_
    fin_cases i
    simpa using hb
  ξ := ![Z]
  ξ_bounded := by
    intro i
    fin_cases i
    exact ⟨M, hZb⟩
  ξ_measurable := by
    intro i
    fin_cases i
    simpa using hZm
theorem oneCell_adapted {b : ℝ} (hb : 0 < b) {Z : Ω → ℝ} (hZm : Measurable Z)
    {M : ℝ} (hZb : ∀ ω, |Z ω| ≤ M) (hZ0 : StronglyMeasurable[ℱ 0] Z) :
    ∀ i : Fin (oneCell hb Z hZm hZb).N,
      StronglyMeasurable[ℱ ((oneCell hb Z hZm hZb).partition i.castSucc)]
        ((oneCell hb Z hZm hZb).ξ i) := by
  intro i
  fin_cases i
  change StronglyMeasurable[ℱ 0] Z
  exact hZ0
end TwoCell
end Ito
end Brownian
end LevyStochCalc


