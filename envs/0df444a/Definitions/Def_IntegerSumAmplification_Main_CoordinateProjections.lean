-- Prove2me | Definitions.Def_IntegerSumAmplification_Main_CoordinateProjections
-- name    : IntegerSumAmplification_Main_CoordinateProjections
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T04:02:03.825446+00:00
-- url     : https://prove2.me/theorems/669e6705-11b4-496c-b968-c51b07f3c803
-- title:
--   Product laws and averaged coordinate projections
-- statement:
--   For a probability law $D$ on any measurable space $W$, write $D^k$ for the law of $k$ independent samples. Given $F:W^k\to\mathbb R$, define
--   $$g_i(w)=\int F(z_1,\ldots,z_{i-1},w,z_{i+1},\ldots,z_k)\,dD^k(z),\qquad
--    g_I(w)=\frac{1}{|I|}\sum_{i\in I}g_i(w).$$
--   The replaced coordinate is unused in the integrand, so integration over that extra coordinate leaves the section integral unchanged. For square-integrable $F$, these are the almost-everywhere coordinate projections of Lemma 6.4. The definition is total; the theorem requires square integrability and nonempty $I$, preventing division-by-zero or undefined-integral defaults from entering its claim. No finiteness assumption is imposed on $W$.
-- source:
--   Farhan Ali and Weiqiang Yuan, Optimal Black-Box Hardness Amplification for Integer Sums, held manuscript dated November 3, 2026 (STOC 2027 submission; acceptance not asserted); citation_basis: published. Lemma 6.4, printed p. 14 / PDF p. 17. PDF SHA256 181fd8ae5069b0c062ebccc0aa72d5a78ec0c836e6d8f6f99dd60464c0b746d7.

import Mathlib
open MeasureTheory ProbabilityTheory

namespace IntegerSumAmplification.Main

noncomputable def productLaw {W : Type*} [MeasurableSpace W]
    (D : Measure W) (k : ℕ) : Measure (Fin k → W) :=
  Measure.pi (fun _ => D)

noncomputable def coordinateProjection {W : Type*} [MeasurableSpace W]
    {k : ℕ} (D : Measure W) (F : (Fin k → W) → ℝ) (i : Fin k) (w : W) : ℝ :=
  ∫ z, F (Function.update z i w) ∂productLaw D k

noncomputable def averagedProjection {W : Type*} [MeasurableSpace W]
    {k : ℕ} (D : Measure W) (F : (Fin k → W) → ℝ) (I : Finset (Fin k)) (w : W) : ℝ :=
  (∑ i ∈ I, coordinateProjection D F i w) / (I.card : ℝ)

end IntegerSumAmplification.Main


