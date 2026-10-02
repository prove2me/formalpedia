-- Prove2me | Definitions.Def_MDPFinance_DividendProblems_BandPolicy
-- name    : MDPFinance_DividendProblems_BandPolicy
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T23:11:51.917306+00:00
-- url     : https://prove2.me/theorems/30d594a8-e3f9-4187-aa9f-6fbecd6f8a3c
-- title:
--   Band-policy and barrier-policy (Definition 9.2.5)
-- statement:
--   Definition 9.2.5 describes the combinatorial shape the goal theorem proves the optimal dividend policy has: an alternating sequence of $n$ "waves" $\{c_{k-1},\dots,d_k\}$ on which nothing is paid, separated by intervals $(c_k,d_{k+1})$ on which the reserve is paid down to exactly $c_k$, with the gap condition $d_k-c_{k-1}\ge2$ ensuring every wave has genuine positive width. A **barrier-policy** (pay down to a single threshold $c$ whenever above it, pay nothing otherwise) is the $n=0$ special case.
--
--   **Formalization Note.** `IsBandPolicy` is rendered existentially over the witnessing $(n,c,d)$ rather than as one closed-form `f`, since the book's own four branch conditions case-split on $k$ in a way a single Lean `if`-expression would either duplicate or obscure; this is a faithful transcription; not a weakening.
--
--   **Moderation note.** Checked against Definition 9.2.5 and the barrier-policy paragraph; unchanged.
-- source:
--   Bäuerle and Rieder, Markov Decision Processes with Applications to Finance, Universitext, Springer 2011, DOI 10.1007/978-3-642-18324-9, p. 275-276, PDF 285-286, Definition 9.2.5 and the barrier-policy paragraph immediately following it

import Mathlib

namespace MDPFinance.DividendProblems

/-- **Definition 9.2.5 a)** (Bäuerle–Rieder, p. 275, PDF 285): a stationary policy `f^\infty` is a
**band-policy** if there exist `n \in \mathbb N_0` and `c_0,\dots,c_n,d_1,\dots,d_n \in
\mathbb N_0` with `d_k - c_{k-1} \ge 2` for `k=1,\dots,n` and `0 \le c_0 < d_1 \le c_1 < d_2 \le
\dots < d_n \le c_n`, and `f(x) = 0` if `x \le c_0`; `f(x) = x - c_k` if `c_k < x < d_{k+1}`;
`f(x) = 0` if `d_k \le x \le c_k`; `f(x) = x - c_n` if `x > c_n`. Rendered existentially over the
witnessing `n,c,d` (a total function `ℕ → ℕ`, only its values at `0,\dots,n` constrained) rather
than as a closed-form `f`, since the four branch conditions of the book's own piecewise formula
overlap in their case-splitting on `k` in a way a single closed-form Lean `if`-expression would
either duplicate or obscure. -/
def IsBandPolicy (f : ℕ → ℕ) : Prop :=
  ∃ (n : ℕ) (c d : ℕ → ℕ),
    (∀ k, 1 ≤ k → k ≤ n → d k - c (k - 1) ≥ 2) ∧
    c 0 < d 1 ∧
    (∀ k, 1 ≤ k → k < n → c k < d (k + 1)) ∧
    (∀ k, 1 ≤ k → k ≤ n → d k ≤ c k) ∧
    (∀ x, x ≤ c 0 → f x = 0) ∧
    (∀ k, k < n → ∀ x, c k < x → x < d (k + 1) → f x = x - c k) ∧
    (∀ k, 1 ≤ k → k ≤ n → ∀ x, d k ≤ x → x ≤ c k → f x = 0) ∧
    (∀ x, c n < x → f x = x - c n)

/-- The **waves** of a band-policy: the sets `\{c_{k-1},\dots,d_k\}`, `k=1,\dots,n`, and the
**length of wave `k`** is `d_k - c_{k-1}` (Bäuerle–Rieder, Definition 9.2.5 b), p. 275-276). -/
def waveLength (c d : ℕ → ℕ) (k : ℕ) : ℕ := d k - c (k - 1)

/-- **Barrier-policy** (Bäuerle–Rieder, p. 276, PDF 286): `f(x)=0` for `x \le c`, `f(x)=x-c` for
`x>c` — the `n=0`, `c_0=c_n=c` special case of a band-policy. -/
def IsBarrierPolicy (f : ℕ → ℕ) : Prop :=
  ∃ c : ℕ, (∀ x, x ≤ c → f x = 0) ∧ ∀ x, c < x → f x = x - c

end MDPFinance.DividendProblems


