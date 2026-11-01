-- Prove2me | Definitions.Def_GuhaBroadcast_mutualInfo
-- name    : GuhaBroadcast_mutualInfo
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T15:23:15.095648+00:00
-- url     : https://prove2.me/theorems/50896180-6ed7-44e2-a104-e70e62087844
-- title:
--   Shannon mutual information $I(X;Y)$ of a finite joint law
-- statement:
--   For a joint probability law $P(x,y)$ on finite sets $X\times Y$ with marginals $P_X(x)=\sum_y P(x,y)$, $P_Y(y)=\sum_x P(x,y)$, the **Shannon mutual information** (in nats) is
--
--   $$
--   I(X;Y)=\sum_{x,y}P(x,y)\log\frac{P(x,y)}{P_X(x)P_Y(y)},
--   $$
--
--   with $0\log 0=0$. It equals $H(Y)-H(Y\mid X)$, the form in which the paper defines it after (14), and is the left side of Holevo's bound (footnote 3).
--
--   **Formalization Note** A term with $P(x,y)=0$ vanishes and a term with $P(x,y)>0$ has positive marginals, so Lean's total `Real.log` and division give exactly the convention $0\log0=0$.
-- source:
--   Guha & Shapiro, Classical Information Capacity of the Bosonic Broadcast Channel, arXiv:0704.1901v2, Section III, after eq. (14) and footnote 3, p.3

import Mathlib

namespace GuhaBroadcast

/-- Guha & Shapiro, *Classical Information Capacity of the Bosonic Broadcast Channel*, arXiv:0704.1901v2, Section III, p.3 (PDF page; the paper prints no page numbers), after (14) and footnote 3: the
Shannon mutual information `I(X; Y) ≡ H(Y) − H(Y|X)` of a finite joint law, in nats, written as
`I(X;Y) = Σ_{x,y} P(x,y) log( P(x,y) / (P_X(x) P_Y(y)) )` with marginals `P_X(x) = Σ_y P(x,y)` and
`P_Y(y) = Σ_x P(x,y)`.

**Formalization Note.** The convention `0 log 0 = 0` is automatic: a term with `P(x,y) = 0` is `0`, and
a term with `P(x,y) > 0` has positive marginals. The definition is total on real arrays; the mission
applies it to probability arrays only. Natural logarithm (nats), as for every entropy of the mission. -/
noncomputable def mutualInfo {X Y : Type} [Fintype X] [Fintype Y] (P : X → Y → ℝ) : ℝ :=
  ∑ x, ∑ y, P x y * Real.log (P x y / ((∑ y', P x y') * (∑ x', P x' y)))

end GuhaBroadcast


