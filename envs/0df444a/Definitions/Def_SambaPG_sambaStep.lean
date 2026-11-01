-- Prove2me | Definitions.Def_SambaPG_sambaStep
-- name    : SambaPG_sambaStep
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:37:02.060751+00:00
-- url     : https://prove2.me/theorems/eb28d3c7-6b28-4b85-87c2-4fc617c8f3a0
-- title:
--   The SAMBA update (6)
-- statement:
--   Let $p=(p_a)_{a\in\mathcal A}$ be the current probability vector, $\ell$ the **leading arm** (an arm of maximal probability), $i$ the arm played and $x$ its reward. Write $I_a=1$ if $a=i$ and $I_a=0$ otherwise. The **SAMBA update** moves every arm $a\neq\ell$ to
--
--   $$
--   p_a' = p_a+\alpha p_a^2\Big[\frac{I_a\,x}{p_a}-\frac{I_\ell\,x}{p_\ell}\Big],
--   $$
--
--   and gives the leading arm the remaining mass, $p_\ell'=1-\sum_{a\neq\ell}p_a'$. This is a stochastic-gradient step with learning rate $\alpha p_a^2$ and an importance-weighted estimate of the reward.
--
--   **Formalization Note** The importance weight $x/p_a$ is only used for the arm that was played, so the division is never by zero on the open simplex, which the update preserves (Lemma 10).
-- source:
--   Denisov & Walton, Regret Analysis of a Markov Policy Gradient Algorithm for Multi-arm Bandits, arXiv:2007.10229v3, §3.4, p.7, eq. (6); algorithm box, p.4

import Mathlib

namespace SambaPG

/-- **One SAMBA update, equation (6).**
Denisov & Walton, arXiv:2007.10229v3, §3.4, p.7, eq. (6), and the algorithm box on p.4.

Given the current probability vector `p`, the leading arm `ℓ` (`a⋆(t)`), the arm played `i` and
the reward `x` it returned, every arm `a ≠ ℓ` is updated by
`p_a ← p_a + α p_a² (I_a x / p_a − I_ℓ x / p_ℓ)`, with `I_b = 1` if `b = i` and `0` otherwise,
and the leading arm receives the remaining mass `p_ℓ ← 1 − Σ_{a ≠ ℓ} p_a`.

**Formalization Note.** The indicator `I_a(t)` of (6) is `if i = a then 1 else 0`, so the
importance weight `x / p_a` only appears for the arm actually played. Lean's `x / 0 = 0` is never
reached on the open simplex, which the update preserves (Lemma 10). -/
noncomputable def sambaStep {A : Type*} [Fintype A] [DecidableEq A] (α : ℝ) (p : A → ℝ)
    (ℓ i : A) (x : ℝ) : A → ℝ :=
  let upd : A → ℝ := fun b =>
    p b + α * p b ^ 2 * ((if i = b then x / p b else 0) - (if i = ℓ then x / p ℓ else 0))
  fun a => if a = ℓ then 1 - ∑ b ∈ Finset.univ.erase ℓ, upd b else upd a

end SambaPG


