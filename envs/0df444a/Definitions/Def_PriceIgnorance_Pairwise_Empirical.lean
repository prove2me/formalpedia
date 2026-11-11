-- Prove2me | Definitions.Def_PriceIgnorance_Pairwise_Empirical
-- name    : PriceIgnorance_Pairwise_Empirical
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T06:12:26.136896+00:00
-- url     : https://prove2.me/theorems/b6102ff5-fca7-4172-8299-06a16bcaa1c8
-- title:
--   Expectation under a discrete distribution, sup norm, empirical distribution and support size
-- statement:
--   Discrete distributions on a set $\Omega$ are probability mass functions. The total variation distance
--   $$d_{TV}(D,\widehat D)=\frac12\sum_{\omega\in\Omega}\big|D(\omega)-\widehat D(\omega)\big|$$
--   is the published definition `QCSepTotal.tv`. The law of $C$ i.i.d. samples is `QCSepTotal.iidLaw`.
--
--   1. $\mathbb E_{X\sim D}[f(X)]=\sum_{\omega}D(\omega)f(\omega)$. For bounded $f$ this sum converges absolutely.
--   2. $\|f\|_\infty=\sup_{\omega}|f(\omega)|$.
--   3. For $C\ge1$ samples $Y_1,\dots,Y_C$ the **empirical distribution** is
--   $$\widehat D(x)=\frac1C\sum_{i=1}^C\mathbf 1[Y_i=x],$$
--   the image of the uniform law on the sample indices under $i\mapsto Y_i$.
--   4. The **support size** of $D$ is $s=|\{x: D(x)>0\}|$.
--
--   These are the objects of Lemmas 2.7 and 2.8, which control how well the empirical distribution of many samples imitates the witness distribution in Theorem 3.16.
--
--   **Formalization Note** Distributions are `PMF`s. The expectation is a `tsum`, which is the finite sum of the paper on finite spaces. $C\ge1$ is the instance `[NeZero C]`.
-- source:
--   Abdallah, Wajc, Price of Ignorance in Pairwise-Independent Prophet Inequalities, STOC 2027 submission (manuscript sha256 c79626fd…), p. 4 (total variation distance, Lemmas 2.7, 2.8)

import Mathlib
import Definitions.Def_QCSepTotal_tv

/-!
# Expectations under discrete distributions, the sup norm and the empirical distribution

Abdallah, Wajc, *Price of Ignorance in Pairwise-Independent Prophet Inequalities*, STOC 2027
submission (manuscript sha256 c79626fd…), p. 4 (total variation, Lemmas 2.7, 2.8).

Discrete distributions are `PMF`s. The total variation distance
`d_TV(D, D̂) = ½ Σ_ω |D(ω) − D̂(ω)|` is the published `QCSepTotal.tv`, and the law of `C` i.i.d.
samples is the published `QCSepTotal.iidLaw`.

* `pmfExp P f = E_{X∼P}[f(X)] = Σ_ω P(ω) f(ω)` (a `tsum`; for bounded `f` it is summable).
* `supNorm f = ‖f‖_∞ = sup_ω |f(ω)|`.
* `empirical Y` for samples `Y_1, …, Y_C` (`C ≥ 1`): `D̂(x) = (1/C) Σ_i 1[Y_i = x]`, i.e. the image
  of the uniform law on the sample indices under `Y`.
* `supportSize D = |supp(D)|`.
-/

namespace PriceIgnorance.Pairwise

/-- `E_{X∼P}[f(X)] = Σ_ω P(ω) f(ω)`. -/
noncomputable def pmfExp {Ω : Type*} (P : PMF Ω) (f : Ω → ℝ) : ℝ :=
  ∑' ω, (P ω).toReal * f ω

/-- The sup norm `‖f‖_∞ = sup_ω |f(ω)|`. -/
noncomputable def supNorm {Ω : Type*} (f : Ω → ℝ) : ℝ :=
  ⨆ ω, |f ω|

/-- The empirical distribution of the samples `Y_1, …, Y_C`:
`D̂(x) = (1/C) Σ_{i=1}^C 1[Y_i = x]`. -/
noncomputable def empirical {α : Type*} {C : ℕ} [NeZero C] (Y : Fin C → α) : PMF α :=
  (PMF.uniformOfFintype (Fin C)).map Y

/-- The support size `s = |supp(D)|` of a distribution `D`. -/
noncomputable def supportSize {α : Type*} (D : PMF α) : ℕ :=
  D.support.ncard

end PriceIgnorance.Pairwise


