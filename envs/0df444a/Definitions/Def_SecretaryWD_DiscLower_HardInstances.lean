-- Prove2me | Definitions.Def_SecretaryWD_DiscLower_HardInstances
-- name    : SecretaryWD_DiscLower_HardInstances
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T05:13:11.461914+00:00
-- url     : https://prove2.me/theorems/356f03c1-88d0-4f92-8d35-6cf3ea68fdae
-- title:
--   The step discount and the instances $\mathcal I_1,\dots,\mathcal I_{2c}$ of §4.1.1
-- statement:
--   This file fixes the construction of §4.1.1 of Babaioff, Dinitz, Gupta, Immorlica and Talwar.
--
--   Let $c\ge 1$ be an integer and $L=c$. The horizon is $n=L^{4c}$, the block ends are $n_t=L^{2t}$ for $t\le 2c$ (so $n_{2c}=n$), and $K=n^2$.
--
--   1. **Discount.** For paper times $j=1,\dots,n$, $d(j)=L^{-1}$ if $1\le j\le n_1$, and $d(j)=L^{-t}$ if $n_{t-1}<j\le n_t$, $2\le t\le 2c$.
--   2. **Instances.** For $1\le t\le 2c$, element $e\in\{0,\dots,n-1\}$ of $\mathcal I_t$ has value $K^s$, where $s$ is the largest $s\le t$ with $e<n/n_s$, and value $0$ if $e\ge n/n_1$. Thus $\mathcal I_1$ consists of $n/n_1$ copies of $K$ and zeroes, $\mathcal I_{t+1}$ arises from $\mathcal I_t$ by raising $n/n_{t+1}$ of its $n/n_t$ values $K^t$ to $K^{t+1}$ (a fraction $n_t/n_{t+1}=L^{-2}$ of them), and $\mathcal I_t$ has exactly $n/n_t$ values $K^t$.
--
--   These are the instances on which no online rule can be better than $c/10$-competitive on all of $\mathcal I_1,\dots,\mathcal I_{2c}$.
--
--   **Formalization Note** Times are 0-based: index $j$ is paper time $j+1$, so the paper's block $(n_{t-1},n_t]$ is the index range $[n_{t-1},n_t)$. The discount class of index $j$ is computed as $1+\#\{s\in\{1,\dots,2c\}: n_s<j+1\}$, and the value level of $e$ as $\#\{s\in\{1,\dots,t\}: e\,n_s<n\}$; both equal the paper's indices because the $n_s$ increase for $L\ge 2$ (for $c=1$ everything is $1$). $K=n^2$ is the value the paper suggests ("say $n^2$").
-- source:
--   Babaioff, Dinitz, Gupta, Immorlica and Talwar, Secretary Problems: Weights and Discounts, SODA 2009 (authors' version), p. 6, Section 4.1.1 (Instance Size, Discount Function, Instances)

import Mathlib

namespace SecretaryWD.DiscLower

open Finset

/-- The horizon `n = L^{4c}` with `L = c` (§4.1.1, p. 6). -/
def horizon (c : ℕ) : ℕ := c ^ (4 * c)

/-- The block ends `n_t = L^{2t}` (§4.1.1, p. 6), `L = c`; `n_{2c} = n`. -/
def blockEnd (c t : ℕ) : ℕ := c ^ (2 * t)

/-- The large value `K = n²` (§4.1.1, p. 6: "say n²"). -/
def bigK (c : ℕ) : ℕ := horizon c ^ 2

/-- The discount class of the 0-based time index `j` (paper time `j + 1`): `1` if
`j + 1 ≤ n_1`, and `t` if `n_{t−1} < j + 1 ≤ n_t` (`2 ≤ t ≤ 2c`). Computed as one plus the
number of `s ∈ {1, …, 2c}` with `n_s < j + 1`. -/
def discountClass (c j : ℕ) : ℕ :=
  1 + ((Icc 1 (2 * c)).filter (fun s => c ^ (2 * s) < j + 1)).card

/-- The step discount function of §4.1.1 (p. 6): `d(j) = L^{−1}` for `1 ≤ j ≤ n_1` and
`d(j) = L^{−t}` for `n_{t−1} < j ≤ n_t`, here on 0-based indices. -/
noncomputable def discount (c : ℕ) : Fin (horizon c) → ℝ :=
  fun j => ((c : ℝ) ^ discountClass c j.val)⁻¹

/-- The value level of the 0-based element `e` in instance `I_t`: the largest `s ≤ t` with
`e < n / n_s` (equivalently `e · n_s < n`), or `0` if there is none (`e ≥ n / n_1`). -/
def valueLevel (c t e : ℕ) : ℕ :=
  ((Icc 1 t).filter (fun s => e * c ^ (2 * s) < horizon c)).card

/-- The instance `I_t` of §4.1.1 (p. 6), `1 ≤ t ≤ 2c`: element `e` has value `K^s` where
`s = valueLevel c t e`, and value `0` if that level is `0`. Thus `I_t` has `n / n_t` elements of
value `K^t`, `n / n_s − n / n_{s+1}` of value `K^s` for `1 ≤ s < t`, and the rest are `0`;
`I_{t+1}` arises from `I_t` by raising `n / n_{t+1}` of its `K^t`'s to `K^{t+1}`. -/
noncomputable def hardInstance (c t : ℕ) : Fin (horizon c) → ℝ :=
  fun e => if valueLevel c t e.val = 0 then 0 else (bigK c : ℝ) ^ valueLevel c t e.val

end SecretaryWD.DiscLower


