-- Prove2me | Definitions.Def_FlexMargin_InQ
-- name    : FlexMargin_InQ
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T03:38:05.115375+00:00
-- url     : https://prove2.me/theorems/c652e818-fdba-406c-a762-cb8497cd4bd5
-- title:
--   The set $Q$ of feasible parameter sets
-- statement:
--   A **parameter set** is a family $K=\{k_{tr}\in\mathbb Z_+ : t=1,\dots,T,\ r=0,\dots,t-1\}$ of nonnegative integers. It belongs to $Q$ if
--
--   $$
--   0\le\sum_{r=0}^{t-1}k_{tr}\le|S_t|\qquad\text{for every }t ,
--   $$
--
--   so that one can choose, inside each category $S_t$, disjoint groups of $k_{tr}$ products whose price is $\beta_{tr}$.
--
--   **Formalization Note** $K$ is a function of the 0-based category $t$ and of $r\in\{0,\dots,t\}$ (the paper's $k_{t+1,r}$).
-- source:
--   Wang, Wang and Zhang, Robust Optimization Approach to Process Flexibility Designs with Contribution Margin Differentials, SSRN 3233721 (version of 2020-05-22), §3.2, p. 18

import Mathlib

open Finset

namespace FlexMargin

/-- **The set `Q` of feasible parameter sets.**
Wang, Wang and Zhang, *Robust Optimization Approach to Process Flexibility Designs with
Contribution Margin Differentials*, SSRN 3233721 (version of 2020-05-22), §3.2, p. 18: "For a given parameter set K = {ktr ∈ Z+ : t = 1,...,T, r = 0,...,t − 1} where
0 ≤ Σ_{r=0}^{t−1} ktr ≤ |St| [...] Let Q denote the set of feasible non-negative integer parameter
sets K = {ktr ∈ Z+ : t = 1,...,T, r = 0,...,t − 1} such that 0 ≤ Σ_{r=0}^{t−1} ktr ≤ |St|."

A parameter set is `K : (t : Fin T) → Fin (t + 1) → ℕ`: for the 0-based category `t` (the paper's
`t + 1`) and `r ∈ {0, …, t}` (the paper's `r = 0, …, (t+1) − 1`), `K t r` is the paper's
`k_{t+1, r}`. `InQ cat K` says `Σ_r K t r ≤ |S_t|` for every category, with `S_t = {i | cat i = t}`.

**Formalization Note.** Entries are natural numbers, the paper's `ℤ^+` (nonnegative integers, as
"non-negative integer parameter sets" says). -/
def InQ {n T : ℕ} (cat : Fin n → Fin T) (K : (t : Fin T) → Fin (t.val + 1) → ℕ) : Prop :=
  ∀ t, ∑ r, K t r ≤ (univ.filter (fun i => cat i = t)).card

end FlexMargin


