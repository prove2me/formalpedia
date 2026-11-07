-- Prove2me | Definitions.Def_EffRobustLearn_rademacherD
-- name    : EffRobustLearn_rademacherD
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:32:22.928472+00:00
-- url     : https://prove2.me/theorems/5fa81d19-108d-46cf-80f6-8e7f45ac1e12
-- title:
--   Rademacher complexity $R_{|S|,D}$ (Definition C.2)
-- statement:
--   For a class $F$ of functions from $X$ to $[-1,1]$, a distribution $D$ and $|S|\ge1$,
--   $$R_{|S|,D}(F)=\mathbb E\Big[\sup_{f\in F}\frac1{|S|}\sum_{i=1}^{|S|}\sigma_if(X_i)\Big],$$
--   where the $X_i$ are drawn independently from $D$ and the $\sigma_i$ are independent uniform signs.
--
--   **Formalization Note** This is the integral over $D^n$ of the published empirical complexity, which takes the supremum over exactly $F$. A non-measurable integrand gives the Bochner value $0$. Fact C.3 item 6, whose content depends on the value of $R$, therefore carries measurability and separability.
-- source:
--   Klivans, Stavropoulos, Tikhonov, Vasilyan, Efficient Robust Learning at the Information-Theoretic Limit, arXiv:2609.17655 (held version, sha256 312a0857…), Definition C.2, p.41 (PDF p.42)

import Mathlib
import Definitions.Def_FoundationsML_SVM_EmpiricalRademacherComplexity_v2

open MeasureTheory

namespace EffRobustLearn

/-- The Rademacher complexity `R_{n,D}(F)`, Definition C.2, Klivans, Stavropoulos, Tikhonov, Vasilyan, *Efficient Robust Learning at the Information-Theoretic Limit*, arXiv:2609.17655 (held version, sha256 312a0857…), p.41:
`R_{|S|,D}(F) = E[ sup_{f∈F} (1/|S|) ∑_i σ_i f(X_i) ]`, with `X_1, …, X_n` i.i.d. from `D` and `σ_i` independent uniform signs.

**Formalization Note.** The expectation over the signs and the supremum over exactly `F` are those of the published
`FoundationsML.SVM.EmpiricalRademacherComplexity` (v2, real `sSup` of the image of `F`, not clipped at `0`). The expectation over the sample
is a Bochner integral over `D^n`. It is `0` when its integrand is not measurable, which is possible for an uncountable class.
Measurable functions and pointwise separability (`PointwiseSeparableReal`) make the integrand measurable, and Fact C.3 item 6, whose content depends on the value of `R`, carries them. -/
noncomputable def rademacherD {X : Type*} [MeasurableSpace X] (D : Measure X) (n : ℕ)
    (F : Set (X → ℝ)) : ℝ :=
  ∫ s : Fin n → X, FoundationsML.SVM.EmpiricalRademacherComplexity F s
    ∂(Measure.pi fun _ : Fin n => D)

end EffRobustLearn


