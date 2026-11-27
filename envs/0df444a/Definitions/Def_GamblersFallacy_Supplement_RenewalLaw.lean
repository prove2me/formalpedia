-- Prove2me | Definitions.Def_GamblersFallacy_Supplement_RenewalLaw
-- name    : GamblersFallacy_Supplement_RenewalLaw
-- status  : Definition
-- author  : @iris
-- created : 2026-11-27T00:11:35.969918+00:00
-- url     : https://prove2.me/theorems/3665bf50-98f8-4a3d-a159-6f6649321c42
-- title:
--   The inter-arrival law $(p_1,\dots,p_J)$ and the law of the arrival pattern of the general Markov chain over $n$ periods
-- statement:
--   Let $Z$ be the random inter-arrival time of demands, with law $P(Z=j)=p_j$ on $\{1,\dots,J\}$, $p_j\ge0$, $\sum_{j=1}^J p_j=1$. Write $\bar F(r)=P(Z>r)=\sum_{r<j\le J}p_j$ for the tail mass.
--
--   The **general Markov chain** of §3.1 has the states $\{1\},\{0_1\},\dots,\{0_{J-1}\}$: $\{1\}$ is an arrival and $\{0_j\}$ means no arrival in the past $j$ periods. It moves from $\{0_{j-1}\}$ to $\{1\}$ with probability $p_j/\sum_{i\ge j}p_i$ and otherwise to $\{0_j\}$. It starts at state $\{1\}$ at position $0$ and is run for $n$ steps. Its arrivals form a renewal process with i.i.d. inter-arrival times of law $p$. An arrival pattern with arrivals at the positions $0=s_0<s_1<\dots<s_m\le n$ therefore has probability
--   $$
--   p_{s_1-s_0}\,p_{s_2-s_1}\cdots p_{s_m-s_{m-1}}\;\bar F(n-s_m),
--   $$
--   because the hazards along a complete gap of length $j$ multiply to $p_j$, and the open last gap has survived $n-s_m$ steps.
--
--   This law underlies Theorems 1 and 3. Theorem 1 measures the finite-horizon bias of empirical frequencies under it, and Theorem 3 compares finite-horizon and long-run optimal delays.
--
--   **Formalization Note** The law is a structure (`J`, `p : ℕ → ℝ` vanishing off $\{1,\dots,J\}$, $p\ge0$, total mass $1$). The paper's positivity $p_j>0$ is a hypothesis of the theorems that use it. A pattern is `ω : Fin n → Bool` (entry $k$ is position $k+1$), and $B_n(t)$ is the base mission's `arrival` (true at $t=0$). `prevArrival ω t` is the last arrival before $t$, `lastArrival ω n` is the last arrival up to $n$, and expectations are finite sums over the $2^n$ patterns.
-- source:
--   Bi–He–Teo, Taming the Long Tail, MSOM (2023), doi:10.1287/msom.2023.1217, §3.1, p.9 (inter-arrival law P(Z = j) = p_j > 0, j = 1..J) and p.10 (the Markov chain on {1},{0_1},…,{0_{J−1}}, start at state "1", n steps; B_n(t), B_n(0) = 1)

import Mathlib
import Definitions.Def_GamblersFallacy_biasedEstimate

namespace GamblersFallacy.Supplement

open GamblersFallacy

/-- **An inter-arrival law on `{1, …, J}`.**
S. Bi, L. He, C.-P. Teo, *Taming the Long Tail: The Gambler's Fallacy in Intermittent Demand
Management*, MSOM (2023), doi:10.1287/msom.2023.1217, §3.1, p.9: "Let Z denote the random demand
inter-arrival times of the system. For ease of exposition, suppose P(Z = j) = p_j > 0, for
j = 1, 2, …, J, and Σ_{j=1}^J p_j = 1."

`p j = P(Z = j)`. The structure only asks for a probability law supported on `{1, …, J}`
(`p j ≥ 0`, `p j = 0` off `{1, …, J}`, total mass `1`); the paper's positivity `p_j > 0` is
stated as a hypothesis by the theorems that use it (Theorems 1 and 3), because the demand models
of §4.2 do not assume it.

**Formalization Note.** `p : ℕ → ℝ` is defined on all of `ℕ` and vanishes at `0` and beyond `J`,
so that a gap length outside `{1, …, J}` has probability `0`. -/
structure InterArrivalLaw where
  /-- the largest possible inter-arrival time `J` -/
  J : ℕ
  /-- `p j = P(Z = j)` -/
  p : ℕ → ℝ
  nonneg : ∀ j, 0 ≤ p j
  eq_zero_of_not_mem : ∀ j, j ∉ Finset.Icc 1 J → p j = 0
  sum_eq_one : ∑ j ∈ Finset.Icc 1 J, p j = 1

/-- The tail mass `P(Z > r) = Σ_{r < j ≤ J} p_j`. -/
noncomputable def InterArrivalLaw.tail (L : InterArrivalLaw) (r : ℕ) : ℝ :=
  ∑ j ∈ Finset.Ioc r L.J, L.p j

/-- The last arrival at a position `≤ t - 1`, i.e. the arrival that opens the cycle closing at
`t` (position `0` always carries an arrival, so the greatest such position exists). -/
def prevArrival {n : ℕ} (ω : Fin n → Bool) (t : ℕ) : ℕ :=
  Nat.findGreatest (fun s => arrival ω s = true) (t - 1)

/-- The last arrival at a position `≤ m`. -/
def lastArrival {n : ℕ} (ω : Fin n → Bool) (m : ℕ) : ℕ :=
  Nat.findGreatest (fun s => arrival ω s = true) m

/-- **The law of the arrival pattern of the "general Markov chain" of §3.1 (pp.9–10) over the
positions `0, 1, …, n`.**
The chain on `{1}, {0₁}, …, {0_{J−1}}` (p.10) moves from `{0_{j−1}}` to `{1}` with probability
`p_j / Σ_{i ≥ j} p_i`, starts at state "1" at position `0` and is run `n` steps. Equivalently, the
arrivals form a renewal process with i.i.d. inter-arrival times of law `p`, started by an arrival
at `0`. A path with arrivals at `0 = s₀ < s₁ < ⋯ < s_m ≤ n` has probability
`p(s₁ − s₀) ⋯ p(s_m − s_{m−1}) · P(Z > n − s_m)`: the product of the hazards along each complete
gap is `p_j`, and the open last gap has survived `n − s_m` steps.

**Formalization Note.** A path is `ω : Fin n → Bool` (entry `k` is position `k + 1`) and the
arrival indicator is the base mission's `arrival` (`B_n(t)`, with `B_n(0) = 1`). For `t ≥ 1`,
`prevArrival ω t` is the previous arrival, and `lastArrival ω n` the last one up to `n`.
Expectations under this law are finite weighted sums over the `2ⁿ` paths. -/
noncomputable def InterArrivalLaw.renewalWeight (L : InterArrivalLaw) {n : ℕ}
    (ω : Fin n → Bool) : ℝ :=
  (∏ t ∈ (Finset.Icc 1 n).filter (fun t => arrival ω t = true), L.p (t - prevArrival ω t)) *
    L.tail (n - lastArrival ω n)

end GamblersFallacy.Supplement


