-- Prove2me | Definitions.Def_SilverRateLB_V
-- name    : SilverRateLB_V
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:21:15.438261+00:00
-- url     : https://prove2.me/theorems/4c54aa28-a6c6-422d-b64d-cba3f5f11ef0
-- title:
--   Checkpoint cost $Q_\Lambda(T;H)$ (13), its minimum $V_\Lambda(H)$, tight sets
-- statement:
--   For constants $a,c$ and $\Lambda\ge a$, the **checkpoint cost** of an admissible checkpoint set $T$ of $H$ is
--   $$Q_\Lambda(T;H) := c(\Lambda+s_{k+1})\prod_{i=1}^k\frac{c(a+s_i)}{b_i-2},$$
--   with $b_i,s_i$ as in (4). The **optimal checkpoint cost** is
--   $$V_\Lambda(H) := \min_{T\ \text{admissible}} Q_\Lambda(T;H),$$
--   and an admissible set attaining it is **tight**. The empty set is always admissible, so the minimum is over a nonempty finite family; for the empty schedule $V_\mu(\varnothing)=c\mu$.
--
--   By (14), a small $V_\Lambda(H)$ gives a large lower bound $\mathscr R_n(H)\ge c^2(\Lambda-1)/V_\Lambda(H)^2$.
--
--   **Formalization Note** $a$ and $c$ are parameters (the paper's are those of Lemma 2.4). The minimum ranges over admissible sets only, which is the paper's convention that an inadmissible set has cost $+\infty$ (§B, p. 26); this keeps a factor with $b_i\le2$ out of the minimum.
-- source:
--   Ye, Liu, Silver Rate Is (Almost) Optimal for Gradient Descent, arXiv:2609.09152 (sha256 6797dde3…), §3.2, (13), p. 13; tightness p. 14; conventions §B, p. 26

import Mathlib
import Definitions.Def_SilverRateLB_gapMass

namespace SilverRateLB

/-- **Checkpoint cost** (13): `Q_Λ(T; H) := c(Λ + s_{k+1}) ∏_{i=1}^k c(a + s_i)/(b_i − 2)`.

Ye, Liu, *Silver Rate Is (Almost) Optimal for Gradient Descent*, arXiv:2609.09152, §3.2, (13),
p. 13: "define the checkpoint cost by QΛ(T;H) := c(Λ+sk+1) ∏_{i=1}^k c(a+si)/(bi−2), Λ ≥ a."

**Formalization Note** The constants `a`, `c` are parameters (the paper's are those of Lemma 2.4).
The cost is meaningful only for admissible `T` (every `b_i > 2`); the paper sets the cost of an
inadmissible set to `+∞` (§B, p. 26), which `V` realizes by minimizing over admissible sets only. -/
noncomputable def ckptCost (a c Λ : ℝ) (H : List ℝ) (T : Finset ℕ) : ℝ :=
  c * (Λ + gapMass H T (T.card + 1)) *
    ∏ i ∈ Finset.Icc 1 T.card, c * (a + gapMass H T i) / (ckptStep H T i - 2)

open Classical in
/-- The admissible checkpoint sets of `H`: subsets of `{1, …, n}` all of whose elements have
stepsize `> 2`. The empty set is always one of them. -/
noncomputable def admissibleSets (H : List ℝ) : Finset (Finset ℕ) :=
  (Finset.Icc 1 H.length).powerset.filter (IsAdmissible H)

/-- **Optimal checkpoint cost** `V_Λ(H) := min_{T admissible} Q_Λ(T; H)`.

Ye, Liu, *Silver Rate Is (Almost) Optimal for Gradient Descent*, arXiv:2609.09152, §3.2, p. 13:
"We therefore define VΛ(H) := min_{T admissible} QΛ(T;H)."; Lemma 3.3, p. 14: "Vµ(∅) = cµ".

**Formalization Note** A minimum over the finite, nonempty family `admissibleSets H` (it contains
`∅`). Inadmissible sets are excluded, which is the paper's convention that their cost is `+∞`;
an unfiltered minimum would let Lean's `x / 0 = 0` and negative factors from `b_i ≤ 2` enter.
For the empty schedule `V a c μ [] = c μ`. -/
noncomputable def V (a c Λ : ℝ) (H : List ℝ) : ℝ :=
  (admissibleSets H).inf' ⟨∅, by simp [admissibleSets, IsAdmissible]⟩ (ckptCost a c Λ H)

/-- **Tight checkpoint set**: an admissible set attaining `V_Λ(H)` (§3.2, p. 14: "A checkpoint set
attaining VΛ(H) is called tight."). -/
def IsTight (a c Λ : ℝ) (H : List ℝ) (T : Finset ℕ) : Prop :=
  IsAdmissible H T ∧ ckptCost a c Λ H T = V a c Λ H

end SilverRateLB


