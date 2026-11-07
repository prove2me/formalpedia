-- Prove2me | Definitions.Def_EffRobustLearn_errD
-- name    : EffRobustLearn_errD
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:31:40.48071+00:00
-- url     : https://prove2.me/theorems/f0c506b7-a981-4d27-b67b-20272d2818d6
-- title:
--   Randomized 0-1 error $\mathrm{err}_D$ and $\widehat{\mathrm{err}}_{S_{\mathrm{ref}}}$ (Definition 2.1)
-- statement:
--   For $\bar h:X\to[-1,1]$, $q:X\to\mathbb R$, a distribution $D$ and a reference sample $S_{\mathrm{ref}}$,
--   $$\mathrm{err}_D(\bar h,q)=\mathbb E_{x\sim D}\Big[\frac{1-\bar h(x)q(x)}2\Big],\qquad \widehat{\mathrm{err}}_{S_{\mathrm{ref}}}(\bar h,q)=\frac1{|S_{\mathrm{ref}}|}\sum_{x\in S_{\mathrm{ref}}}\frac{1-\bar h(x)q(x)}2.$$
--   When $q$ is not $[-1,1]$-valued these denote the linear extension.
--
--   For $h(x)\sim\mathrm{Rad}(\bar h(x))$, the probability of error of $h$ against $c^\star$ equals $\mathrm{err}_D(\bar h,c^\star)$.
--
--   **Formalization Note** $\mathrm{err}_D$ is a Bochner integral, hence $0$ on a non-integrable integrand. The mission applies it only to bounded measurable integrands.
-- source:
--   Klivans, Stavropoulos, Tikhonov, Vasilyan, Efficient Robust Learning at the Information-Theoretic Limit, arXiv:2609.17655 (held version, sha256 312a0857…), Definition 2.1, p.11 (PDF p.12)

import Mathlib

open MeasureTheory

namespace EffRobustLearn

/-- The randomized 0-1 error under `D`, Definition 2.1, Klivans, Stavropoulos, Tikhonov, Vasilyan, *Efficient Robust Learning at the Information-Theoretic Limit*, arXiv:2609.17655 (held version, sha256 312a0857…), p.11:
`err_D(h̄, q) = E_{x∼D}[(1 - h̄(x) q(x)) / 2]`, including the paper's linear extension to real-valued `q`.

**Formalization Note.** This is a Bochner integral, hence `0` on a non-integrable integrand. Every statement of the mission
applies it to a bounded measurable integrand: `h̄` and `q` are built from measurable concepts, and the verification
file proves the output `h̄_T` measurable. -/
noncomputable def errD {X : Type*} [MeasurableSpace X] (D : Measure X) (h q : X → ℝ) : ℝ :=
  ∫ x, (1 - h x * q x) / 2 ∂D

/-- The empirical randomized 0-1 error on the reference sample, Definition 2.1, p.11:
`err̂_{Sref}(h̄, q) = (1/|Sref|) ∑_{x∈Sref} (1 - h̄(x) q(x)) / 2`.

**Formalization Note.** The sample is an indexed family, so repeated points stay distinct instances (§2, Sample conventions). -/
noncomputable def errHat {X : Type*} {m : ℕ} (Sref : Fin m → X) (h q : X → ℝ) : ℝ :=
  (1 / (m : ℝ)) * ∑ j, (1 - h (Sref j) * q (Sref j)) / 2

end EffRobustLearn


