-- Prove2me | Definitions.Def_AggStatePG_aggSet
-- name    : AggStatePG_aggSet
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T12:43:11.359965+00:00
-- url     : https://prove2.me/theorems/e120df8d-595f-4f2b-b512-7119c2938e60
-- title:
--   State-aggregated policy class $\Pi_\phi$
-- statement:
--   A **state aggregation** is a map $\phi:\mathcal S\to\{1,\dots,m\}$; its fibres $\phi^{-1}(j)$ are the segments of the partition. The **state-aggregated policy class** is
--   $$\Pi_\phi=\{\pi\in\Pi:\pi(s)=\pi(s')\text{ for all }s,s'\in\mathcal S\text{ such that }\phi(s)=\phi(s')\},$$
--   the policies that choose the same action distribution at all states of a segment. Policy gradient methods search over $\Pi_\phi$, storing one action distribution per segment.
--
--   **Formalization Note** Policies are stacked vectors (p.7) and $\Pi$ is the published `simplexSet`. The segment labels form an arbitrary type $\iota$; $\iota=\mathrm{Fin}\,m$ is the paper's $\{1,\dots,m\}$.
-- source:
--   Russo, Approximation Benefits of Policy Gradient Methods with Aggregated States, arXiv:2007.11684v3, §3, pp.5–6 (state aggregation φ; Π_φ)

import Mathlib
import Definitions.Def_PolicyGradTheory_ProjGA_Algorithm

open PolicyGradTheory.ProjGA

namespace AggStatePG

/-- The **state-aggregated policy class** `Π_φ` (Russo, *Approximation Benefits of Policy Gradient Methods with Aggregated States*, arXiv:2007.11684v3, §3, p.6):
`Π_φ = {π ∈ Π : π(s) = π(s') for all s, s' ∈ S such that φ(s) = φ(s')}`,
for a state aggregation `φ : S → {1, …, m}` (p.5), as a set of stacked policy vectors.

**Formalization Note.** Policies are stacked vectors `x ∈ EuclideanSpace ℝ (S × A)` (p.7) and
`Π = simplexSet S A` (published: every row `x(s, ·)` is a probability vector). `π(s) = π(s')` is
equality of the rows, `∀ a, x(s,a) = x(s',a)`. The segment labels are an arbitrary type `ι`
(`ι = Fin m` is the paper's `{1, …, m}`). -/
def aggSet {S A ι : Type*} [Fintype A] (φ : S → ι) : Set (EuclideanSpace ℝ (S × A)) :=
  {x | x ∈ simplexSet S A ∧ ∀ s s' : S, φ s = φ s' → ∀ a : A, x (s, a) = x (s', a)}

end AggStatePG


