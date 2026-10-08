-- Prove2me | Definitions.Def_MultiSecretary_NonAdaptive_Policy
-- name    : MultiSecretary_NonAdaptive_Policy
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T08:03:17.171222+00:00
-- url     : https://prove2.me/theorems/133f60f0-f275-41c3-a331-96350f95c1de
-- title:
--   Sec. 5 — non-adaptive policies, their value V^π_on, V*_na, the index policy (33), and Bernoulli sums
-- statement:
--   A **non-adaptive policy** is a matrix $\pi=\{p_{j,t}\in[0,1]: j\in[m],\ t\in[n]\}$: at time $t$, if budget remains and $X_t=a_j$, the candidate is selected with probability $p_{j,t}$, independently of the past. Formally, with independent uniforms $U_t$, let $B_t=\sum_j\mathbb 1(U_t\le p_{j,t},X_t=a_j)$; the $B_t$ are independent Bernoulli variables with $\mathbb E[B_t\mid X_t=a_j]=p_{j,t}$ and
--   $$q_t=\mathbb E[B_t]=\sum_{j\in[m]}p_{j,t}f_j.$$
--   The policy selects the candidate at time $t$ when $B_t=1$ and fewer than $k$ earlier coins were $1$, i.e. it selects until the budget is exhausted. Its value $V^\pi_{\mathrm{on}}(n,k)$ is the expected total ability of the selected candidates, and
--   $$V^*_{\mathrm{na}}(n,k)=\sup_{\pi\in\Pi_{\mathrm{na}}}V^\pi_{\mathrm{on}}(n,k)$$
--   is the value of the best non-adaptive policy.
--
--   The **index policy** (33) uses the time-independent probabilities $\mathfrak p_{j,t}=1$ for $j<j_{\mathrm{id}}$, $\mathfrak p_{j_{\mathrm{id}},t}=(k/n-\bar F(a_{j_{\mathrm{id}}}))/f_{j_{\mathrm{id}}}$ and $0$ for $j>j_{\mathrm{id}}$, where $j_{\mathrm{id}}$ is the index with $\bar F(a_{j_{\mathrm{id}}})\le k/n<\bar F(a_{j_{\mathrm{id}}+1})$.
--
--   For Lemma 5, independent Bernoulli variables $B_t$ with success probabilities $q_t$ have centred sum $N_n=\sum_t(B_t-q_t)$ and variance $\varsigma_n^2=\sum_t q_t(1-q_t)$.
--
--   These objects state Theorem 3 and its auxiliary lemmas.
--
--   **Formalization Note** Lean index $j\in\{0,\dots,m-1\}$ is the paper's index $j+1$, so `a 0` is the largest value $a_1$, `f 0` is $f_1$ and `f (Fin.rev 0)` is $f_m$. An outcome is $\omega:\mathrm{Fin}\,n\to\mathrm{Fin}\,m\times\mathrm{Bool}$, the pair $(X_t,B_t)$, with weight $\prod_t f_{x_t}\,(p_{x_t,t}\text{ if }b_t\text{ else }1-p_{x_t,t})$; this is the joint law the uniforms generate. The selection rule "coin is $1$ and fewer than $k$ earlier coins were $1$" equals the paper's "select up to the stopping time $\nu=\min\{r\ge1:\sum_{t\le r}B_t\ge k\text{ or }r\ge n\}$" for $k\ge1$; at $k=0$ the printed $\nu=1$ would allow one selection with no budget, and the feasible rule (no selection) is used instead. $V^*_{\mathrm{na}}$ is `sSup` over all matrices with entries in $[0,1]$; the set of values is nonempty and bounded. $j_{\mathrm{id}}$ is the largest (0-based) $j\le m-1$ with $\bar F(a_{j+1})\le k/n$: as printed the defining inequality has no solution at $k=n$, and the largest-index reading gives $j_{\mathrm{id}}=m$ and $\mathfrak p_{m,t}=1$ there.
-- source:
--   Arlotto, Gurvich, Uniformly Bounded Regret in the Multi-Secretary Problem, arXiv:1710.07719v2, Sec. 5, p. 24 (non-adaptive policies, V^π_on, V*_na, eq. (33)); Lemma 5, p. 26 (N_n, ς_n)

import Mathlib
import Definitions.Def_MultiSecretary_NonAdaptive_Model

namespace MultiSecretary.NonAdaptive

open Finset

/-- A non-adaptive policy (Sec. 5, p. 24) is a matrix `p j t ∈ [0, 1]`: the probability of selecting
the candidate at time `t` when its ability is `a_j` and budget remains. -/
def IsNAPolicy {m n : ℕ} (p : Fin m → Fin n → ℝ) : Prop :=
  ∀ j t, p j t ∈ Set.Icc (0 : ℝ) 1

/-- Joint law of `(X_t, B_t)_{t}` under the non-adaptive policy `p`: an outcome `ω t = (x_t, b_t)`
records the ability index and the coin `B_t = 1(U_t ≤ p_{x_t, t})`; the pairs are independent
across `t`, `X_t` has masses `f`, and `P(B_t = 1 | X_t = a_j) = p j t`. -/
noncomputable def naWeight {m n : ℕ} (f : Fin m → ℝ) (p : Fin m → Fin n → ℝ)
    (ω : Fin n → Fin m × Bool) : ℝ :=
  ∏ t, f (ω t).1 * (if (ω t).2 then p (ω t).1 t else 1 - p (ω t).1 t)

/-- The candidate at time `t` is selected iff its coin is `1` and fewer than `k` earlier coins were
`1`, i.e. budget remains: the policy selects up to the stopping time `ν` (p. 24). -/
def selected {m n : ℕ} (k : ℕ) (ω : Fin n → Fin m × Bool) (t : Fin n) : Bool :=
  (ω t).2 && decide ((univ.filter (fun s : Fin n => s < t ∧ (ω s).2 = true)).card < k)

/-- `V^π_on(n, k)` for the non-adaptive policy `π = p` (p. 24): the expected total ability of the
selected candidates. -/
noncomputable def Vna {m n : ℕ} (a f : Fin m → ℝ) (k : ℕ) (p : Fin m → Fin n → ℝ) : ℝ :=
  ∑ ω : Fin n → Fin m × Bool, naWeight f p ω *
    ∑ t, (if selected k ω t then a (ω t).1 else 0)

/-- `V*_na(n, k) = sup_{π ∈ Π_na} V^π_on(n, k)`, the supremum over all non-adaptive policies (p. 24). -/
noncomputable def VstarNa {m : ℕ} (a f : Fin m → ℝ) (n k : ℕ) : ℝ :=
  sSup ((fun p : Fin m → Fin n → ℝ => Vna a f k p) '' {p | IsNAPolicy p})

/-- `q_t = E[B_t] = ∑_j p_{j,t} f_j`, the marginal selection probability at time `t` (p. 24). -/
noncomputable def selProb {m n : ℕ} (f : Fin m → ℝ) (p : Fin m → Fin n → ℝ) (t : Fin n) : ℝ :=
  ∑ j, p j t * f j

open Classical in
/-- The index `j_id` of (33), 0-based: the largest `j ≤ m - 1` with `F̄(a_{j+1}) ≤ k/n`
(paper: `F̄(a_{j_id}) ≤ k/n < F̄(a_{j_id + 1})`; at `k = n` the largest-index reading gives `j_id = m`). -/
noncomputable def jid {m : ℕ} (f : Fin m → ℝ) (n k : ℕ) : ℕ :=
  Nat.findGreatest (fun j => Fbar f j ≤ (k : ℝ) / n) (m - 1)

/-- The non-adaptive index policy (33), p. 24: select `a_j`-candidates with probability `1` for
`j` before `j_id`, `(k/n - F̄(a_{j_id}))/f_{j_id}` at `j_id`, and `0` after. -/
noncomputable def idxPolicy {m : ℕ} (f : Fin m → ℝ) (n k : ℕ) : Fin m → Fin n → ℝ :=
  fun j _ =>
    if j.val < jid f n k then 1
    else if j.val = jid f n k then ((k : ℝ) / n - Fbar f j.val) / f j
    else 0

/-- Law of independent Bernoulli variables `B_t` with success probabilities `q t` (Lemma 5, p. 26). -/
noncomputable def bernWeight {n : ℕ} (q : Fin n → ℝ) (b : Fin n → Bool) : ℝ :=
  ∏ t, if b t then q t else 1 - q t

/-- `N_n = ∑_t (B_t - q_t)` (Lemma 5, p. 26). -/
noncomputable def centeredSum {n : ℕ} (q : Fin n → ℝ) (b : Fin n → Bool) : ℝ :=
  ∑ t, ((if b t then (1 : ℝ) else 0) - q t)

/-- `ς² = ∑_t q_t (1 - q_t)` (Lemma 5, p. 26; Lemma 7, p. 27). -/
noncomputable def varSum {n : ℕ} (q : Fin n → ℝ) : ℝ :=
  ∑ t, q t * (1 - q t)

end MultiSecretary.NonAdaptive


