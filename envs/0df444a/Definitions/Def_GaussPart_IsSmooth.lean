-- Prove2me | Definitions.Def_GaussPart_IsSmooth
-- name    : GaussPart_IsSmooth
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T11:27:17.517337+00:00
-- url     : https://prove2.me/theorems/58ac6d40-e60e-4b7b-a901-bdabe7fd0336
-- title:
--   $(q,\sigma)$-smoothness of a distribution with respect to another
-- statement:
--   Let $P,Q$ be probability measures on a measurable space $\Omega$, and let $q\ge 1$, $\sigma\in(0,1]$. The measure $Q$ is **$(q,\sigma)$-smooth with respect to $P$** if for every measurable event $E$
--   $$Q(E)\le \frac1\sigma\,P(E)^{1/q}.$$
--
--   For $q=1$ this says that $Q$ is obtained from $P$ by rejection sampling with acceptance probability at least $\sigma$; for $q>1$ the density ratio $dQ/dP$ may be unbounded while events that are rare under $P$ stay rare under $Q$. This is the distributional assumption of every result of the paper, with $P=N(0,I_d)$.
--
--   **Formalization Note** The inequality is stated in $[0,\infty]$; for probability measures it is the real inequality of the paper. The ranges $q\ge1$, $\sigma\in(0,1]$ are hypotheses of the theorems that use the definition, as on the page.
-- source:
--   Diakonikolas, Iakovidis, Kane, Ma, Gaussian Partitioning for Reliable Learning of Multi-Index Models, arXiv:2611.05264 (sha256 7e0ca6d4…), Definition 1.1, p.1 (PDF p.3)

import Mathlib

open MeasureTheory

namespace GaussPart

/-- **Definition 1.1** (`(q, σ)`-smoothness).

I. Diakonikolas, G. Iakovidis, D. M. Kane, M. Ma, *Gaussian Partitioning for Reliable Learning of
Multi-Index Models*, arXiv:2611.05264 (copy with sha256 7e0ca6d4…), Definition 1.1, p.1 (PDF p.3):
"for every measurable event `E ⊆ ℝᵈ`, `Q(E) ≤ (1/σ) P(E)^{1/q}`".

**Formalization Note.** The inequality is written in `ℝ≥0∞`, which agrees with the real form for
probability measures. The ranges `q ≥ 1`, `σ ∈ (0, 1]` are binders of the theorems that use it, as
on the page. The definition is stated for any measurable space because Lemmas 3.5 and 3.8 use it
on `ℝ` and on "the same measurable space". -/
def IsSmooth {Ω : Type*} [MeasurableSpace Ω] (P Q : Measure Ω) (q σ : ℝ) : Prop :=
  ∀ E : Set Ω, MeasurableSet E → Q E ≤ ENNReal.ofReal (1 / σ) * P E ^ (1 / q)

end GaussPart


