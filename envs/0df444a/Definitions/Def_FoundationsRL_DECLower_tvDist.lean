-- Prove2me | Definitions.Def_FoundationsRL_DECLower_tvDist
-- name    : FoundationsRL_DECLower_tvDist
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T00:06:49.35395+00:00
-- url     : https://prove2.me/theorems/db6dee02-05f6-4b0e-aebe-6e444722742e
-- title:
--   Total variation distance $D_{\mathrm{TV}}(P,Q)=\sup_{A}|P(A)-Q(A)|$
-- statement:
--   Let $P$ and $Q$ be measures on a measurable space $(\Omega,\mathcal F)$. The **total variation distance** is
--
--   $$
--   D_{\mathrm{TV}}(P,Q)=\sup_{A\in\mathcal F}\,|P(A)-Q(A)| .
--   $$
--
--   For probability measures it equals $\tfrac12\int|dP/d\nu-dQ/d\nu|\,d\nu$ for any common dominating measure $\nu$ (the $f$-divergence with $f(t)=\tfrac12|t-1|$), and it lies in $[0,1]$.
--
--   It is used in Lemma 19, in the data-processing step for the average action distribution, and in (6.40).
--
--   **Formalization Note** The measures of sets are taken as real numbers; the mission applies the definition only to probability measures, where the supremum is over a nonempty set bounded by $1$.
-- source:
--   Foster & Rakhlin, Foundations of Reinforcement Learning and Interactive Decision Making, arXiv:2312.16730v1, §6.2, p. 96 (total variation distance)

import Mathlib

open MeasureTheory

namespace FoundationsRL.DECLower

/-- **Total variation distance** `D_TV(P, Q) = sup_{A ∈ F} |P(A) − Q(A)|`.
Foster & Rakhlin, *Foundations of Reinforcement Learning and Interactive Decision Making*,
arXiv:2312.16730v1, §6.2, p. 96 ("which can also be written as D_TV(P, Q) = sup_{A∈F} |P(A) − Q(A)|").

**Formalization Note.** The supremum ranges over the measurable sets of the space (the paper's
`F`), and the measures of sets are converted to real numbers. The theorems of the mission apply
`tvDist` only to probability measures, for which every term lies in `[0, 1]`, so the supremum is
over a nonempty (`∅` is measurable) set bounded by `1` and is the true supremum. -/
noncomputable def tvDist {α : Type*} [MeasurableSpace α] (μ ν : Measure α) : ℝ :=
  ⨆ s : {s : Set α // MeasurableSet s}, |(μ s.1).toReal - (ν s.1).toReal|

end FoundationsRL.DECLower


