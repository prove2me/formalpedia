-- Prove2me | Definitions.Def_PersonalizedAssortment_IB_Supplement_PhaseInstance
-- name    : PersonalizedAssortment_IB_Supplement_PhaseInstance
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T10:27:13.238978+00:00
-- url     : https://prove2.me/theorems/943a3791-e098-4bb1-8b49-f04152678ea6
-- title:
--   Lemma 3's construction, p. 1539 — equally-liked-set customers, the phase sequences $z^\sigma$ and $\rho_n$
-- statement:
--   These are the objects of the construction in the proof of Lemma 3 (p. 1539), and the constant of Lemma 3 (p. 1538).
--
--   1. **Choice model of a type $\Theta$.** A customer type is a set $\Theta$ of products that the customer likes equally. Offered an assortment $S$, she picks each $i\in S\cap\Theta$ with probability
--   $$\varphi_i^\Theta(S)=\frac{1}{|S\cap\Theta|},$$
--   and buys nothing if $S\cap\Theta=\emptyset$. Every other product has probability $0$. This is the multinomial logit model with weight $1$ on $\Theta$, weight $0$ off $\Theta$, and no-purchase probability $0$ when a liked product is offered.
--
--   2. **Phase sequences.** Fix $n$ products and a phase length $k$, so the horizon is $T=nk$. For a permutation $\sigma$ of the products, the sequence $z^\sigma$ has $n$ phases of $k$ customers each. Every customer of phase $j\in\{0,\dots,n-1\}$ (periods $jk,\dots,jk+k-1$) has type
--   $$\Theta_j=\{\sigma(j),\sigma(j+1),\dots,\sigma(n-1)\}.$$
--   Phase $0$ likes every product, and each later phase loses interest in one product of the previous phase. The paper's stochastic process draws $\sigma$ uniformly from the $n!$ permutations.
--
--   3. **The constant**
--   $$\rho_n=\frac1n\sum_{j=1}^n\min\Big\{\sum_{t=1}^j\frac{1}{n-t+1},\,1\Big\}.$$
--   For example $\rho_2=3/4$, and $\rho_n\to1-1/e$ as $n\to\infty$.
--
--   This instance is the hard input of the paper's upper bound on the competitive ratio. The inventories in Lemma 3 are $c_i=k=T/n$, and every revenue equals $1$.
--
--   **Formalization Note** Products and phases are indexed from $0$. A type is any finite set of products. The empty set is allowed in the type space but never arrives, while the paper counts $2^n-1$ nonempty types. $\rho_n$ is computed in the reals, so $n-t+1$ involves no natural-number subtraction.
-- source:
--   Golrezaei, Nazerzadeh, Rusmevichientong, Real-Time Optimization of Personalized Assortments, Management Sci. 60(6), 2014, https://doi.org/10.1287/mnsc.2014.1939, p. 1539, paragraph "In the proof of Lemma 3, we construct a stochastic process …"; p. 1538, Lemma 3 (ρ_n)

import Mathlib
import Definitions.Def_PersonalizedAssortment_IB_ChoiceModel

namespace PersonalizedAssortment.IB.Supplement

open PersonalizedAssortment.IB

/-- The choice model of a customer type `Θ` in the construction of Lemma 3 (p. 1539): the customer
likes the products of `Θ` equally and always buys when offered one of them. Offered `S`, she picks
each `i ∈ S ∩ Θ` with probability `1 / |S ∩ Θ|` (multinomial logit with weight 1 on `Θ`, weight 0
off `Θ` and no-purchase weight 0); if `S ∩ Θ = ∅` she buys nothing. -/
noncomputable def phaseChoice {n : ℕ} (Θ : Finset (Fin n)) : ChoiceModel n where
  prob S i := if i ∈ S ∩ Θ then 1 / ((S ∩ Θ).card : ℝ) else 0
  prob_nonneg S i := by
    split_ifs <;> positivity
  prob_eq_zero_of_not_mem S i hi := by
    simp [Finset.mem_inter, hi]
  sum_prob_le_one S := by
    rw [← Finset.sum_filter]
    have h : S.filter (fun i => i ∈ S ∩ Θ) = S ∩ Θ := by
      ext i; simp [Finset.mem_inter]
    rw [h, Finset.sum_const, nsmul_eq_mul]
    rcases Nat.eq_zero_or_pos (S ∩ Θ).card with h0 | h0
    · simp [h0]
    · rw [mul_one_div_cancel (by exact_mod_cast h0.ne')]

/-- The arrival sequence `z^σ` of Lemma 3's construction (p. 1539) with `n` products, phase length
`k` and horizon `T = n k`, for a permutation `σ` of the products. Periods are indexed from 0 and
period `t` belongs to phase `j = ⌊t / k⌋ ∈ {0, …, n-1}`; every customer of phase `j` has type
`Θ_j = {σ(j), σ(j+1), …, σ(n-1)}`. So phase 0 likes all products and each later phase drops one
product of the previous phase. The stochastic process of the construction draws `σ` uniformly
from the `n!` permutations. -/
def phaseSeq {n : ℕ} (k : ℕ) (σ : Equiv.Perm (Fin n)) (t : Fin (n * k)) : Finset (Fin n) :=
  (Finset.univ.filter (fun m : Fin n => t.val / k ≤ m.val)).image σ

/-- `ρ_n = (1/n) ∑_{j=1}^n min{∑_{t=1}^j 1/(n - t + 1), 1}` (Lemma 3, p. 1538). -/
noncomputable def rhoN (n : ℕ) : ℝ :=
  (1 / (n : ℝ)) * ∑ j ∈ Finset.Icc 1 n,
    min (∑ t ∈ Finset.Icc 1 j, 1 / ((n : ℝ) - (t : ℝ) + 1)) 1

end PersonalizedAssortment.IB.Supplement


