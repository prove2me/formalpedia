-- Prove2me | Definitions.Def_SecretaryWD_DiscLower_DiscountedSecretary
-- name    : SecretaryWD_DiscLower_DiscountedSecretary
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T05:13:09.496841+00:00
-- url     : https://prove2.me/theorems/feee7ec1-ccec-4b8e-865e-005669a60fc9
-- title:
--   The discounted secretary problem: randomized online stopping rules, E[A] and E[OPT]
-- statement:
--   This file sets up the **discounted secretary problem** of Babaioff, Dinitz, Gupta, Immorlica and Talwar (§2).
--
--   There are $n$ elements $e\in\{0,\dots,n-1\}$ with values $v(e)\in\mathbb R$ and a discount function $d$ on the times $0,\dots,n-1$ (time index $t$ is the paper's time $t+1$). The elements arrive in a uniformly random order $\pi$, a permutation read as *time $\mapsto$ element*: $\pi(t)$ arrives at time $t$. Write $h_\pi=(v(\pi(0)),\dots,v(\pi(n-1)))$ for the values in arrival order.
--
--   A **randomized online stopping rule** $A$ is a family of numbers $p_t(h)\in[0,1]$, one for each time $t$ and each arrival-ordered value sequence $h$, such that $p_t(h)$ depends only on $h_0,\dots,h_t$, the values seen so far including the current one. If $A$ has not stopped before time $t$, it stops at $t$ and selects $\pi(t)$ with probability $p_t(h_\pi)$; it selects at most one element and may select none. The probability that $A$ stops exactly at $t$ is
--
--   $$P_A(t\mid h)=p_t(h)\prod_{s<t}\bigl(1-p_s(h)\bigr).$$
--
--   The rule sees values only, never the identities of the elements or the future, and it is not told which instance it faces; it may depend on $n$ and $d$, which are inputs.
--
--   With the order uniform over all $n!$ permutations, the expected value of $A$, the expected offline optimum, and the probability of stopping among the first $m$ arrivals are
--
--   $$\mathbb E[A]=\frac1{n!}\sum_\pi\sum_t d(t)\,v(\pi(t))\,P_A(t\mid h_\pi),\qquad \mathbb E[\mathrm{OPT}]=\frac1{n!}\sum_\pi\max_t d(t)\,v(\pi(t)),$$
--
--   $$\Pr[A\text{ stops by } m]=\frac1{n!}\sum_\pi\sum_{t<m}P_A(t\mid h_\pi).$$
--
--   $A$ is $\alpha$-competitive on a set of instances when $\mathbb E[\mathrm{OPT}]\le\alpha\,\mathbb E[A]$ on each of them (the paper's ratio $\mathbb E[\mathrm{OPT}]/\mathbb E[A]\le\alpha$, written multiplicatively).
--
--   **Formalization Note** Times and elements are `Fin n`. The rule is the structure `StoppingRule n`; the field `adapted` is the non-anticipation condition. The maximum in OPT is a supremum over the finite type `Fin n` (a maximum for $n\ge 1$).
-- source:
--   Babaioff, Dinitz, Gupta, Immorlica and Talwar, Secretary Problems: Weights and Discounts, SODA 2009 (authors' version), pp. 3–4, Section 2 (Discounted Secretary Problems; competitive ratio)

import Mathlib

namespace SecretaryWD.DiscLower

open Finset

/-- A randomized online stopping rule for the discounted secretary problem with `n` arrivals
(Babaioff et al., SODA 2009, §2, pp. 3–4).

Times are `Fin n`; index `t` is the paper's time `t + 1`. The argument `h : Fin n → ℝ` is the
sequence of values in arrival order, `h s = v (π s)`. If the rule has not stopped before time
`t`, it stops at `t` (selecting the element arriving at `t`) with probability `stop t h`.
`adapted` says this probability depends only on the values observed up to and including time
`t`: the rule observes values only, online, and never looks ahead. The rule may depend on the
horizon `n` and the discount function (fixed inputs), but it is not given the instance. -/
structure StoppingRule (n : ℕ) where
  /-- probability of stopping at time `t`, given the arrival-ordered values `h` -/
  stop : Fin n → (Fin n → ℝ) → ℝ
  stop_nonneg : ∀ t h, 0 ≤ stop t h
  stop_le_one : ∀ t h, stop t h ≤ 1
  adapted : ∀ (t : Fin n) (h h' : Fin n → ℝ), (∀ s, s ≤ t → h s = h' s) → stop t h = stop t h'

/-- The values in arrival order under the order `π` (read *time ↦ element*):
the element `π t` arrives at time `t`. -/
def arrivalValues {n : ℕ} (v : Fin n → ℝ) (π : Equiv.Perm (Fin n)) : Fin n → ℝ :=
  fun t => v (π t)

/-- Probability that the rule `A` stops exactly at time `t` on the arrival-ordered values `h`:
`p_t(h) · ∏_{s < t} (1 − p_s(h))`. -/
def stopProb {n : ℕ} (A : StoppingRule n) (h : Fin n → ℝ) (t : Fin n) : ℝ :=
  A.stop t h * ∏ s ∈ univ.filter (fun s => s < t), (1 - A.stop s h)

/-- Expected discounted value `E_π[d(π⁻¹(e_A)) · v(e_A)]` of the rule `A` on values `v` with
discount `d`, the order `π` uniform over all `n!` permutations. Selecting nothing earns `0`. -/
noncomputable def expectedValue {n : ℕ} (d v : Fin n → ℝ) (A : StoppingRule n) : ℝ :=
  (1 / (n.factorial : ℝ)) * ∑ π : Equiv.Perm (Fin n), ∑ t : Fin n,
    d t * v (π t) * stopProb A (arrivalValues v π) t

/-- Expected offline optimum `E_π[max_e d(π⁻¹(e)) · v(e)] = E_π[max_t d(t) · v(π(t))]`, the order
`π` uniform. (The supremum is over the finite type `Fin n`; it is a maximum for `n ≥ 1`.) -/
noncomputable def expectedOPT {n : ℕ} (d v : Fin n → ℝ) : ℝ :=
  (1 / (n.factorial : ℝ)) * ∑ π : Equiv.Perm (Fin n), ⨆ t : Fin n, d t * v (π t)

/-- Probability, over the uniform order and the rule's randomness, that `A` selects an element
among the first `m` arrivals (paper times `1, …, m`, i.e. indices `t < m`). -/
noncomputable def stopByProb {n : ℕ} (v : Fin n → ℝ) (A : StoppingRule n) (m : ℕ) : ℝ :=
  (1 / (n.factorial : ℝ)) * ∑ π : Equiv.Perm (Fin n),
    ∑ t ∈ univ.filter (fun t : Fin n => t.val < m), stopProb A (arrivalValues v π) t

end SecretaryWD.DiscLower


