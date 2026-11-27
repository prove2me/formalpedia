-- Prove2me | Definitions.Def_AggStatePG_Supplement_aggQSet
-- name    : AggStatePG_Supplement_aggQSet
-- status  : Definition
-- author  : @iris
-- created : 2026-11-27T03:21:08.561809+00:00
-- url     : https://prove2.me/theorems/a2ddb5f8-d4ea-4f65-98fc-d65a4d8fbad1
-- title:
--   State-aggregated state-action value functions $\mathcal Q_\phi$
-- statement:
--   Let $\mathcal S$ and $\mathcal A$ be finite state and action sets and let $\phi:\mathcal S\to\{1,\dots,m\}$ be a state aggregation, which partitions $\mathcal S$ into the segments $\phi^{-1}(i)$. The set of **state-aggregated state-action value functions** is
--   $$\mathcal Q_\phi=\{Q\in\mathbb R^{|\mathcal S|\times|\mathcal A|}:Q(s,a)=Q(s',a)\ \text{for all }a\in\mathcal A\text{ and all }s,s'\in\mathcal S\text{ with }\phi(s)=\phi(s')\}.$$
--
--   An element of $\mathcal Q_\phi$ is determined by $m\cdot|\mathcal A|$ numbers, one per segment and action. It is the value-function counterpart of the aggregated policy class $\Pi_\phi$, and the class over which approximate policy iteration fits its value estimates (Algorithms 1, 2 and 4).
--
--   **Formalization Note** State-action vectors are tables $Q:\mathcal S\to\mathcal A\to\mathbb R$, and the segment labels are an arbitrary type ($\{1,\dots,m\}$ is the case `Fin m`).
-- source:
--   Russo, Approximation Benefits of Policy Gradient Methods with Aggregated States, arXiv:2007.11684v3, §3, p.6 (definition of Q_φ)

import Mathlib

namespace AggStatePG.Supplement

/-- The **state-aggregated state-action value functions** `Q_φ` (Russo, *Approximation Benefits of
Policy Gradient Methods with Aggregated States*, arXiv:2007.11684v3, §3, p.6):
`Q_φ = {Q ∈ ℝ^{|S|×|A|} : Q(s,a) = Q(s',a) for all a ∈ A, and all s, s' ∈ S such that φ(s) = φ(s')}`.

**Formalization Note.** State-action vectors are tables `Q : S → A → ℝ`; the aggregation is any
map `φ : S → ι` (`ι = Fin m` is the paper's `{1, …, m}`). `Q_φ` is a linear subspace of the tables. -/
def aggQSet {S A ι : Type*} (φ : S → ι) : Set (S → A → ℝ) :=
  {Q | ∀ (a : A) (s s' : S), φ s = φ s' → Q s a = Q s' a}

end AggStatePG.Supplement


