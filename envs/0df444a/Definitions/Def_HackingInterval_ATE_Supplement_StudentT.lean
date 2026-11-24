-- Prove2me | Definitions.Def_HackingInterval_ATE_Supplement_StudentT
-- name    : HackingInterval_ATE_Supplement_StudentT
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T22:53:48.030534+00:00
-- url     : https://prove2.me/theorems/a24bc9f6-be67-4a4b-bbd4-64fa8fb59eb9
-- title:
--   Student-t law and its lower inverse CDF
-- statement:
--   Let $\nu$ be a positive integer. Let $Z_0,Z_1,\ldots,Z_\nu$ be independent standard normal random variables. The **Student-t law** with $\nu$ degrees of freedom is the distribution of
--
--   $$T_\nu=\frac{Z_0}{\sqrt{\nu^{-1}\sum_{j=1}^{\nu}Z_j^2}}.$$
--
--   Write $F_\nu$ for its cumulative distribution function. Its lower quantile at a level $u\in(0,1)$ is
--
--   $$Q_\nu(u)=\inf\{z\in\mathbb R:u\le F_\nu(z)\}.$$
--
--   This defines the actual probability law and quantile used by Theorems 2 and 5. Normalization is proved by the finite Gaussian product and measurable pushforward instances. The calibration theorems additionally assert positivity and the CDF identity at $u=1-\alpha/2$; these are conclusions, never assumed inputs.
--
--   **Formalization Note** The numerator is the last coordinate of a vector indexed by $\operatorname{Fin}(\nu+1)$, and the preceding coordinates form the denominator. For $\nu>0$, the event where every denominator coordinate vanishes has probability zero; assigning value zero there does not change the Student-t distribution. Outside the stated domain, $\nu=0$ gives the point mass at zero and inverse-CDF infima may have default values. Every theorem uses $\nu>0$ and $0<\alpha<1$.
-- source:
--   Coker, Rudin & King, A Theory of Statistical Inference for Ensuring the Robustness of Scientific Results, Management Science (Articles in Advance, 2021), DOI 10.1287/mnsc.2020.3818, p. 11 (PDF 12), Theorem 2, quantile convention; p. 14 (PDF 15), Theorem 5

import Mathlib
open MeasureTheory ProbabilityTheory
noncomputable section

namespace HackingInterval.ATE.Supplement

/-- Independent standard normals, one numerator and ν denominator coordinates. -/
def studentNormalLaw (ν : ℕ) : Measure (Fin (ν + 1) → ℝ) :=
  Measure.pi (fun _ => gaussianReal 0 1)

instance studentNormalLaw_probability (ν : ℕ) : IsProbabilityMeasure (studentNormalLaw ν) := by
  unfold studentNormalLaw
  infer_instance

/-- The normal / independent chi-radius construction of Student's t statistic.
For ν > 0, the zero denominator is a null event. -/
def studentStatistic (ν : ℕ) (z : Fin (ν + 1) → ℝ) : ℝ :=
  z (Fin.last ν) / Real.sqrt ((∑ j : Fin ν, z j.castSucc ^ 2) / (ν : ℝ))

/-- Student-t law with ν degrees of freedom (used only for ν > 0). -/
def studentLaw (ν : ℕ) : Measure ℝ :=
  (studentNormalLaw ν).map (studentStatistic ν)

instance studentLaw_probability (ν : ℕ) : IsProbabilityMeasure (studentLaw ν) := by
  unfold studentLaw
  apply Measure.isProbabilityMeasure_map
  apply Measurable.aemeasurable
  unfold studentStatistic
  fun_prop

/-- Lower generalized inverse of the actual Student-t CDF. Uses have 0 < u < 1, ν > 0. -/
def studentQuantile (ν : ℕ) (u : ℝ) : ℝ :=
  sInf {z : ℝ | u ≤ cdf (studentLaw ν) z}

end HackingInterval.ATE.Supplement


