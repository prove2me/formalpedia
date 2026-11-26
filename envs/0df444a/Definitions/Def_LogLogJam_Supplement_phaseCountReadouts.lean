-- Prove2me | Definitions.Def_LogLogJam_Supplement_phaseCountReadouts
-- name    : LogLogJam_Supplement_phaseCountReadouts
-- status  : Definition
-- author  : @Senrui Chen
-- created : 2026-11-26T09:22:18.412393+00:00
-- url     : https://prove2.me/theorems/4bef7ab4-18ab-4b6a-aeb4-ed752435df96
-- title:
--   The two single-copy measurement settings
-- statement:
--   For $r\geq0$, the one-mode centered Gaussian state has Siegel parameter $\tanh(r)e^{2i\theta}$. The measurement schedule is history-independent. Its first $\lfloor m/2\rfloor$ settings have the canonical phase effects on even Fock occupations and its remaining settings have the photon-number spectral effects. Outcomes are real.
-- source:
--   https://arxiv.org/html/2607.12983v1#S8.SS3 — Definition 8.17 and §§8.3.3–8.3.4.

import Mathlib
import Definitions.Def_LogLogJam_Supplement_IsGaussQP
import Definitions.Def_BosonicLearn_AdaptiveScheme

open MeasureTheory
open QAlgorithms.Papers.Independent.Dependency50.P33 (State)
open QAlgorithms.Papers.Independent.Claimed50.P47 (Occupation)
open scoped Classical

namespace LogLogJam.Supplement

/-- Fock-space meaning of the squeezing coordinates of one centered pure mode. -/
def squeezedAt (ρ : State (Occupation (Fin 1))) (r θ : ℝ) : Prop :=
  0 ≤ r ∧ IsGaussQP ρ 0 (VK
    (Matrix.of fun _ _ : Fin 1 => (Real.tanh r : ℂ) * Complex.exp ((2 * θ : ℝ) * Complex.I)))

/-- The two fixed single-copy readouts in §8.3. The even compression of the first
is Eq. (146). Odd sectors may be completed arbitrarily to a physical POVM. The
second measures photon number, with an integer recorded as a real observation. -/
def phaseCountReadouts {N : ℕ} (S : BosonicLearn.AdaptiveScheme 1 N ℝ) : Prop :=
  (∀ (t : Fin N) (x y : Fin t → ℝ), S.povm t x = S.povm t y) ∧
  (∀ (t : Fin N), t.val < N / 2 → ∀ h (B : Set ℝ), MeasurableSet B → ∀ k l : ℕ,
    (S.povm t h).effect B (fun _ => 2 * k) (fun _ => 2 * l) =
      (∫ α in B ∩ Set.Ico 0 (2 * Real.pi),
        Complex.exp (Complex.I * (((k : ℝ) - l) * α))) / (2 * Real.pi : ℝ)) ∧
  (∀ (t : Fin N), N / 2 ≤ t.val → ∀ h (B : Set ℝ), MeasurableSet B → ∀ i j,
    (S.povm t h).effect B i j = if i = j ∧ (i 0 : ℝ) ∈ B then 1 else 0)

end LogLogJam.Supplement


