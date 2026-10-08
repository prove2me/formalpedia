-- Prove2me | Definitions.Def_SamuelCahnProphet_Median_Setting
-- name    : SamuelCahnProphet_Median_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T15:16:55.126358+00:00
-- url     : https://prove2.me/theorems/1cd5a3f0-bcb9-4a9f-9ed4-a337ef79c203
-- title:
--   §1, pp. 1213–1214 — maximum, threshold rules, positive stopped rewards, median, and β
-- statement:
--   Let $X_1,\ldots,X_n$ be real observations, where $n\ge1$, and set $X_n^*=\max_i X_i$. For a real threshold $c$, $t(c)$ stops at the first index before $n$ with $X_i\ge c$; $s(c)$ uses $X_i>c$. Both stop at $n$ if no earlier observation qualifies. Write $E^+X_{t(c)}$ and $E^+X_{s(c)}$ for the stopped expectation restricted to the respective threshold event.
--
--   A median $m$ of $X_n^*$ satisfies
--   $$
--   P(X_n^*<m)\le\tfrac12,\qquad P(X_n^*>m)\le\tfrac12.
--   $$
--   The excess sum is $\beta(m)=\sum_{i=1}^n E(X_i-m)^+$. The setting also defines $E X_\tau$ for a stopping index $\tau$ and the supremum of $E X_{t(c)}$ and $E X_{s(c)}$ over $c\ge0$, used in Remark 1.
--
--   These definitions give the shared objects for Theorem 1 and its companion results. Extended nonnegative expectations retain infinite values.
-- source:
--   Samuel-Cahn, Comparison of threshold stop rules and maximum for independent nonnegative random variables, Ann. Probab. 12 (1984), pp. 1213–1215, §1, (1.1), (1.2), and §2, T*n

import Mathlib

namespace SamuelCahnProphet.Median

open MeasureTheory

/-- The maximum of the `n` observations, with `n ≥ 1`. -/
noncomputable def maxX {Ω : Type*} {n : ℕ} [NeZero n]
    (X : Fin n → Ω → ℝ) (ω : Ω) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun i => X i ω)

/-- Stop at the first index before the last whose value is at least `c`,
or at the last index if there is no such earlier index. -/
noncomputable def tRule {Ω : Type*} {n : ℕ} [NeZero n]
    (X : Fin n → Ω → ℝ) (c : ℝ) (ω : Ω) : Fin n := by
  classical
  exact (Finset.univ.filter (fun i : Fin n => c ≤ X i ω ∨ i = ⊤)).min'
    ⟨⊤, by simp⟩

/-- Stop at the first index before the last whose value exceeds `c`,
or at the last index if there is no such earlier index. -/
noncomputable def sRule {Ω : Type*} {n : ℕ} [NeZero n]
    (X : Fin n → Ω → ℝ) (c : ℝ) (ω : Ω) : Fin n := by
  classical
  exact (Finset.univ.filter (fun i : Fin n => c < X i ω ∨ i = ⊤)).min'
    ⟨⊤, by simp⟩

/-- The nonnegative expectation of the stopped value. -/
noncomputable def expStop {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) {n : ℕ} (X : Fin n → Ω → ℝ) (τ : Ω → Fin n) : ENNReal :=
  ∫⁻ ω, ENNReal.ofReal (X (τ ω) ω) ∂P

/-- The part of the `t(c)` stopped value that reaches the weak threshold. -/
noncomputable def EplusT {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) {n : ℕ} [NeZero n] (X : Fin n → Ω → ℝ) (c : ℝ) : ENNReal :=
  ∫⁻ ω, (if c ≤ X (tRule X c ω) ω
    then ENNReal.ofReal (X (tRule X c ω) ω) else 0) ∂P

/-- The part of the `s(c)` stopped value that exceeds the strict threshold. -/
noncomputable def EplusS {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) {n : ℕ} [NeZero n] (X : Fin n → Ω → ℝ) (c : ℝ) : ENNReal :=
  ∫⁻ ω, (if c < X (sRule X c ω) ω
    then ENNReal.ofReal (X (sRule X c ω) ω) else 0) ∂P

/-- Both tail probabilities of a median are at most one half. -/
def IsMedian {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (Y : Ω → ℝ) (m : ℝ) : Prop :=
  P {ω | Y ω < m} ≤ (1 / 2 : ENNReal) ∧
    P {ω | m < Y ω} ≤ (1 / 2 : ENNReal)

/-- The sum of expected positive parts above the threshold. -/
noncomputable def beta {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) {n : ℕ} (X : Fin n → Ω → ℝ) (m : ℝ) : ENNReal :=
  ∑ i : Fin n, ∫⁻ ω, ENNReal.ofReal (X i ω - m) ∂P

/-- The best expected stopped value among the nonnegative weak and strict thresholds. -/
noncomputable def supThreshold {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) {n : ℕ} [NeZero n] (X : Fin n → Ω → ℝ) : ENNReal :=
  ⨆ (c : ℝ) (_ : 0 ≤ c), max (expStop P X (tRule X c))
    (expStop P X (sRule X c))

end SamuelCahnProphet.Median


