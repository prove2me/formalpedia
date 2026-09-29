-- Prove2me | Definitions.Def_FoundationsRL_GeneralDM_Divergences
-- name    : FoundationsRL_GeneralDM_Divergences
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-19T20:20:06.754348+00:00
-- url     : https://prove2.me/theorems/51eadc48-8eb3-45f9-aed3-e04370c20c08
-- title:
--   Squared Hellinger, total variation and KL divergence for discrete distributions (Eq. 6.5-6.7 specialized)
-- statement:
--   This bundle formalizes the three information-theoretic divergences used throughout Chapter 6
--   (Foster & Rakhlin, *Foundations of Reinforcement Learning and Interactive Decision Making*,
--   arXiv:2312.16730v1, §6.2, pp. 95-96), specialized from the book's general dominating-measure
--   formula (Eq. (6.5)) to the counting measure on a finite outcome type $Y$ — i.e. to discrete
--   probability distributions $P, Q : Y \to \mathbb{R}$ (nonnegative, summing to $1$).
--
--   The **squared Hellinger distance** is
--   $$
--   D_H^2(P, Q) := \sum_{y \in Y} \bigl(\sqrt{P(y)} - \sqrt{Q(y)}\bigr)^2.
--   $$
--   The **total variation distance** is
--   $$
--   D_{TV}(P, Q) := \frac{1}{2} \sum_{y \in Y} |P(y) - Q(y)|.
--   $$
--   The **Kullback-Leibler divergence** is
--   $$
--   D_{KL}(P \| Q) := \sum_{y \in Y} P(y) \log\!\left(\frac{P(y)}{Q(y)}\right)
--   $$
--   when $P$ is absolutely continuous with respect to $Q$ (i.e. $Q(y) = 0 \Rightarrow P(y) = 0$
--   for every $y$), and $+\infty$ otherwise, matching the book's own two-case definition.
--
--   `hellingerSq` and `totalVariationDiscrete` return a real number; `klDivDiscrete` returns an
--   `ENNReal` (Lean's extended nonnegative reals) so that its $+\infty$ case is represented
--   honestly rather than truncated to a real default.
--
--   **Formalization Note** The book states Lemma 19/20 for distributions over a general
--   measurable space $(\Omega, \mathcal{F})$; this mission specializes to discrete distributions
--   on a finite type (the counting-measure instance of the book's own general Eq. (6.5)), matching
--   the finite decision/observation spaces used throughout this series. This is disclosed as a
--   scope restriction in `STATUS.md`.
-- source:
--   Foster & Rakhlin, Foundations of Reinforcement Learning and Interactive Decision Making, arXiv:2312.16730v1, §6.2, pp. 95-96

import Mathlib

namespace FoundationsRL.GeneralDM

/-- Squared Hellinger distance between two discrete probability distributions `P`, `Q` over a
finite outcome type `Y` (Foster & Rakhlin, *Foundations of Reinforcement Learning and Interactive
Decision Making*, arXiv:2312.16730v1, p. 96, Eq. (6.6) discussion, specializing the general
dominating-measure formula (6.5) to the counting measure on the finite type `Y`):

`D²_H(P, Q) := Σ_y (√(P y) − √(Q y))²`. -/
noncomputable def hellingerSq {Y : Type*} [Fintype Y] (P Q : Y → ℝ) : ℝ :=
  ∑ y, (Real.sqrt (P y) - Real.sqrt (Q y)) ^ 2

/-- Total variation distance between two discrete probability distributions `P`, `Q` over a
finite outcome type `Y` (Foster & Rakhlin, arXiv:2312.16730v1, p. 96, specializing (6.5) to the
counting measure): `D_TV(P, Q) := (1/2) · Σ_y |P y − Q y|`. -/
noncomputable def totalVariationDiscrete {Y : Type*} [Fintype Y] (P Q : Y → ℝ) : ℝ :=
  (1 / 2) * ∑ y, |P y - Q y|

/-- Kullback-Leibler divergence between two discrete probability distributions `P`, `Q` over a
finite outcome type `Y` (Foster & Rakhlin, arXiv:2312.16730v1, p. 96, specializing (6.5) to the
counting measure): `D_KL(P ∥ Q) := Σ_y P y · log(P y / Q y)` when `P` is absolutely continuous
with respect to `Q` (i.e. `Q y = 0 → P y = 0` for every `y`), and `+∞` (Lean's `⊤` in `ENNReal`)
otherwise, matching the book's own two-case definition of `D_KL` on p. 96. -/
noncomputable def klDivDiscrete {Y : Type*} [Fintype Y] (P Q : Y → ℝ) : ENNReal :=
  if ∀ y, Q y = 0 → P y = 0 then
    ENNReal.ofReal (∑ y, P y * Real.log (P y / Q y))
  else
    ⊤

end FoundationsRL.GeneralDM


