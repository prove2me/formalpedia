-- Prove2me | Definitions.Def_HellingerSubadd_hellingerSq
-- name    : HellingerSubadd_hellingerSq
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T02:47:00.571691+00:00
-- url     : https://prove2.me/theorems/b5fe0f2d-9040-4b6c-8f2d-14d5179e20c5
-- title:
--   Squared Hellinger distance $D^2_{\mathrm H}(\mu,\nu)=\int(\sqrt{d\mu}-\sqrt{d\nu})^2$
-- statement:
--   Let $\mu$ and $\nu$ be measures on a measurable space $(\Omega,\mathcal F)$. The **squared Hellinger distance** is
--
--   $$
--   D^2_{\mathrm H}(\mu,\nu)=\int_\Omega\left(\sqrt{\frac{d\mu}{d(\mu+\nu)}}-\sqrt{\frac{d\nu}{d(\mu+\nu)}}\right)^2 d(\mu+\nu),
--   $$
--
--   the paper's $\int(\sqrt{d\mathbb P}-\sqrt{d\mathbb Q})^2$ computed with densities against the dominating measure $\mu+\nu$. There is no factor $1/2$: for probability measures $D^2_{\mathrm H}\in[0,2]$, with value $2$ exactly for mutually singular measures.
--
--   This is the divergence in which every result of the mission is stated: Lemma A.5 compares it with KL divergence, Lemmas A.10 and A.11 use it to control KL divergence and expectations, and Lemma A.13 bounds it for laws of sequential processes.
--
--   **Formalization Note** The paper (footnote 4) computes (5) with densities against any common dominating measure and notes that the value does not depend on that choice; $\mu+\nu$ is one such measure and always exists. The value lies in $[0,\infty]$ (a Lebesgue integral of a non-negative function), like Mathlib's KL divergence `klDiv`.
-- source:
--   Foster, Kakade, Qian & Rakhlin, The Statistical Complexity of Interactive Decision Making, arXiv:2112.13487v3, Section 2, eq. (5) and footnote 4, p. 10

import Mathlib

open MeasureTheory
open scoped ENNReal

namespace HellingerSubadd

/-- **Squared Hellinger distance** `D²_H(μ, ν) = ∫ (√dμ − √dν)²`.
Foster, Kakade, Qian & Rakhlin, *The Statistical Complexity of Interactive Decision Making*,
arXiv:2112.13487v3, Section 2, eq. (5) and footnote 4, p. 10.

The densities of `μ` and `ν` are taken against the dominating measure `μ + ν`:
`D²_H(μ, ν) = ∫ (√(dμ/d(μ+ν)) − √(dν/d(μ+ν)))² d(μ+ν)`.

**Formalization Note.** Footnote 4 of the paper computes (5) through densities against any common
dominating measure and notes that the value does not depend on that choice; `μ + ν` dominates both
`μ` and `ν`, so it is one admissible choice. There is no factor `1/2`: for probability measures the
value lies in `[0, 2]` and equals `2` for mutually singular measures, as in (5). The value is taken
in `ℝ≥0∞` (a `lintegral`), like Mathlib's `klDiv`. The definition is stated for all measures; every
theorem of the mission applies it to probability (or finite) measures, for which the densities are
finite almost everywhere. -/
noncomputable def hellingerSq {α : Type*} [MeasurableSpace α] (μ ν : Measure α) : ℝ≥0∞ :=
  ∫⁻ x, ENNReal.ofReal ((Real.sqrt (μ.rnDeriv (μ + ν) x).toReal
      - Real.sqrt (ν.rnDeriv (μ + ν) x).toReal) ^ 2) ∂(μ + ν)

end HellingerSubadd


