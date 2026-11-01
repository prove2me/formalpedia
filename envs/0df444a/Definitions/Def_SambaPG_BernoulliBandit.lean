-- Prove2me | Definitions.Def_SambaPG_BernoulliBandit
-- name    : SambaPG_BernoulliBandit
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:37:01.060201+00:00
-- url     : https://prove2.me/theorems/8e5f5305-6750-4430-aae3-a11e8bd5dfb6
-- title:
--   Bernoulli bandit with a unique optimal arm, $r^\star$ and the gap $\Delta$
-- statement:
--   A **Bernoulli multi-armed bandit** has a finite set of arms $\mathcal A$ with $N:=|\mathcal A|\ge 2$. Arm $a$ pays a reward $R_a(t)\in\{0,1\}$ with mean $r_a\in[0,1]$. The **optimal arm** $a^\star=\operatorname{argmax}_{a}r_a$ is assumed unique, $r^\star=r_{a^\star}$ is the optimal mean, and the **gap** between the best and the next best arm is
--
--   $$
--   \Delta:=r^\star-\max_{a\neq a^\star}r_a>0 .
--   $$
--
--   These are the data on which SAMBA, its regret and condition (2) are defined.
--
--   **Formalization Note** The structure carries the means, the optimal arm, uniqueness of the optimum and $N\ge2$ (with one arm $\Delta$ would be a maximum over the empty set). The reward random variables are part of `SambaNoise`.
-- source:
--   Denisov & Walton, Regret Analysis of a Markov Policy Gradient Algorithm for Multi-arm Bandits, arXiv:2007.10229v3, §3.1, p.6

import Mathlib

namespace SambaPG

/-- **A Bernoulli multi-armed bandit with a unique optimal arm.**
Denisov & Walton, *Regret Analysis of a Markov Policy Gradient Algorithm for Multi-arm Bandits*,
arXiv:2007.10229v3, §3.1, p.6.

The arms form the finite set `A` (`N := |A|`). Arm `a` pays a Bernoulli reward with mean
`r a ∈ [0, 1]`. The optimal arm `aStar` (`a⋆`) is unique: every other arm has a strictly smaller
mean.

**Formalization Note.** `A` is a `Fintype` with at least two elements (`two_le_card`): with one
arm the gap `∆ = r⋆ − max_{a ≠ a⋆} r_a` of p.6 is a maximum over the empty set and undefined.
The reward random variables themselves live in `SambaPG.SambaNoise`. -/
structure BernoulliBandit (A : Type*) [Fintype A] where
  /-- The mean reward `r_a ∈ [0, 1]` of arm `a`. -/
  r : A → ℝ
  r_mem : ∀ a, r a ∈ Set.Icc (0 : ℝ) 1
  /-- The optimal arm `a⋆ = argmax_a r_a`. -/
  aStar : A
  /-- "We assume the optimal arm is unique." -/
  aStar_unique : ∀ a, a ≠ aStar → r a < r aStar
  /-- At least two arms, so that the gap `∆` is defined. -/
  two_le_card : 2 ≤ Fintype.card A

namespace BernoulliBandit

variable {A : Type*} [Fintype A] [DecidableEq A]

/-- The optimal mean reward `r⋆ = max_a r_a = r_{a⋆}` (arXiv:2007.10229v3, §3.1, p.6). -/
def rStar (B : BernoulliBandit A) : ℝ := B.r B.aStar

/-- The suboptimal arms `A ∖ {a⋆}` form a nonempty set (`N ≥ 2`). -/
theorem erase_aStar_nonempty (B : BernoulliBandit A) :
    (Finset.univ.erase B.aStar).Nonempty := by
  rw [← Finset.card_pos, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ]
  have := B.two_le_card
  omega

/-- The gap `∆ := r⋆ − max_{a : a ≠ a⋆} r_a` between the best and the next best arm
(arXiv:2007.10229v3, §3.1, p.6). -/
def gap (B : BernoulliBandit A) : ℝ :=
  B.rStar - (Finset.univ.erase B.aStar).sup' B.erase_aStar_nonempty B.r

end BernoulliBandit

end SambaPG


