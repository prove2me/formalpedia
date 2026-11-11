-- Prove2me | Definitions.Def_OrderSelProphet_Kernel_Scores
-- name    : OrderSelProphet_Kernel_Scores
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T01:57:25.203789+00:00
-- url     : https://prove2.me/theorems/f03ce8ba-4a5c-46b5-b264-4b7a3afd96c1
-- title:
--   Randomized tie-breaking scores (187) and the score construction of Appendix H
-- statement:
--   For an input $F_1,\dots,F_n$: $F_{\rm mix}(v)=n^{-1}\sum_iF_i(v)$ and its left limit $F_{\rm mix}(v^-)=n^{-1}\sum_iP(V_i<v)$. The **score** of value $v$ with tie-break $z$ is (187)
--   $$X=F_{\rm mix}(v^-)+z\,\big(F_{\rm mix}(v)-F_{\rm mix}(v^-)\big).$$
--   `scoreLaw F i` is the law of $X_i$ when $V_i\sim F_i$ and $Z_i\sim U[0,1]$ are independent. A **score run** (`IsScoreRun`) is a probability space with $V_i\sim F_i$, $Z_i\sim U[0,1]$, and arrival times $T_i$ distributed as the arrival laws of the kernel construction at ratio $\Gamma$ with kernel $K$ **on the score laws**, all $3n$ variables mutually independent. The accepted item (`scoreIndex`) is that of the kernel construction on the score laws applied to the realized scores $X_i=\mathrm{score}(V_i,Z_i)$; the collected value is the original $V_I$.
-- source:
--   Peng and Tang, Order-selection Prophet Inequality (Almost) Goes I.I.D., arXiv:2610.34892 (held file SHA-256 2f111b85…22dd), Appendix H, eq. (187), p. 75

import Mathlib
import Definitions.Def_OrderSelProphet_Kernel_Profiles

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace OrderSelProphet.Kernel

/-! # Randomized tie-breaking scores (Appendix H, p. 75)

Peng and Tang (2026), arXiv:2610.34892, Appendix H, eq. (187). The arrival construction is run on
the atomless scores `X_i`; the value collected is the original value `V_I`. -/

/-- `F_mix(v) = n⁻¹ ∑_i F_i(v)` (Appendix H, p. 75). -/
noncomputable def Fmix {n : ℕ} (F : Fin n → Measure ℝ) (v : ℝ) : ℝ :=
  (n : ℝ)⁻¹ * ∑ i, distFn (F i) v

/-- The left limit `F_mix(v⁻) = n⁻¹ ∑_i P(V_i < v)`. -/
noncomputable def FmixLeft {n : ℕ} (F : Fin n → Measure ℝ) (v : ℝ) : ℝ :=
  (n : ℝ)⁻¹ * ∑ i, (F i (Iio v)).toReal

/-- The **score** (eq. (187), p. 75) of value `v` with tie-break `z`:
`X = F_mix(v⁻) + z (F_mix(v) - F_mix(v⁻))`. -/
noncomputable def score {n : ℕ} (F : Fin n → Measure ℝ) (v z : ℝ) : ℝ :=
  FmixLeft F v + z * (Fmix F v - FmixLeft F v)

/-- The uniform law on `[0,1]` of a tie-breaking variable. -/
noncomputable def uniformUnit : Measure ℝ :=
  volume.restrict (Icc (0 : ℝ) 1)

/-- The law of the score `X_i` of item `i` when `V_i ~ F_i` and `Z_i ~ U[0,1]` are independent. -/
noncomputable def scoreLaw {n : ℕ} (F : Fin n → Measure ℝ) (i : Fin n) : Measure ℝ :=
  ((F i).prod uniformUnit).map (fun p : ℝ × ℝ => score F p.1 p.2)

/-- Score laws are finite measures (images of finite measures). -/
theorem scoreLaw_isFinite {n : ℕ} (F : Fin n → Measure ℝ) [∀ i, IsFiniteMeasure (F i)]
    (i : Fin n) : IsFiniteMeasure (scoreLaw F i) := by
  unfold scoreLaw uniformUnit
  infer_instance

attribute [instance] scoreLaw_isFinite

/-- A probability space carrying the **score construction** of Appendix H at ratio `Γ` with
kernel `K` on an arbitrary input `F` (atoms allowed): values `V_i ~ F_i`, tie-breaks
`Z_i ~ U[0,1]`, and arrival times `T_i` with the laws `G_i` of the kernel construction for the
score laws, the `3n` variables `V_1..V_n, Z_1..Z_n, T_1..T_n` mutually independent. -/
def IsScoreRun {Ω : Type*} [MeasurableSpace Ω] (Γ : ℝ) (K : ℝ → ℝ → ℝ) {n : ℕ}
    (F : Fin n → Measure ℝ) [∀ i, IsFiniteMeasure (F i)] (P : Measure Ω) (V Z : Fin n → Ω → ℝ)
    (T : Fin n → Ω → WithTop ℝ) : Prop :=
  IsProbabilityMeasure P ∧ (∀ i, Measurable (V i)) ∧ (∀ i, Measurable (Z i)) ∧
    (∀ i, Measurable (T i)) ∧ (∀ i, P.map (V i) = F i) ∧ (∀ i, P.map (Z i) = uniformUnit) ∧
    (∀ i, P.map (T i) = inputArrivalLaw Γ K (scoreLaw F) i) ∧
    iIndep (fun k : Fin n ⊕ Fin n ⊕ Fin n =>
      Sum.elim (fun i => MeasurableSpace.comap (V i) inferInstance)
        (Sum.elim (fun i => MeasurableSpace.comap (Z i) inferInstance)
          (fun i => MeasurableSpace.comap (T i) inferInstance)) k) P

/-- The accepted index of the score construction: the kernel arrival construction on the score
laws, applied to the realized scores `X_i = score(V_i, Z_i)`. Item `i`'s test reads only
`(T_i, V_i, Z_i)`. -/
noncomputable def scoreIndex (K : ℝ → ℝ → ℝ) {n : ℕ} (F : Fin n → Measure ℝ)
    [∀ i, IsFiniteMeasure (F i)] (T : Fin n → WithTop ℝ) (V Z : Fin n → ℝ) : Option (Fin n) :=
  kernelIndex K (scoreLaw F) T (fun i => score F (V i) (Z i))

end OrderSelProphet.Kernel


