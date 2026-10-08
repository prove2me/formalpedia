-- Prove2me | Definitions.Def_MultiSecretary_NonAdaptive_Model
-- name    : MultiSecretary_NonAdaptive_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T07:43:08.960819+00:00
-- url     : https://prove2.me/theorems/4a6ad239-2ff8-4875-84bb-b5e28d0692f5
-- title:
--   Sec. 2–3 — the multi-secretary model: values a₁ > ⋯ > aₘ > 0, masses fⱼ > 0, offline value V*_off, counts, deterministic relaxation DR and s*
-- statement:
--   A decision maker sees $n$ candidates with abilities $X_1,\dots,X_n$, drawn independently from a distribution supported on $m$ values $0<a_m<a_{m-1}<\dots<a_1$, with masses $f_j=\mathbb P(X_1=a_j)>0$ summing to one, and may select at most $k\le n$ of them. Write $\epsilon=\tfrac12\min_j f_j$ and $\bar F(a_j)=f_1+\dots+f_{j-1}$ (so $\bar F(a_1)=0$ and $\bar F(a_{m+1})=1$).
--
--   The **offline value** is the expected best total ability of at most $k$ candidates chosen with full knowledge of the sequence:
--   $$V^*_{\mathrm{off}}(n,k)=\mathbb E\Big[\max\Big\{\textstyle\sum_{t\in[n]}X_t\sigma_t:\sigma\in\{0,1\}^n,\ \sum_t\sigma_t\le k\Big\}\Big].$$
--   With $Z^r_j=\#\{t\le r:X_t=a_j\}$, the **offline counts** are $\mathfrak S^n_j=\min\{Z^n_j,(k-\sum_{i<j}Z^n_i)_+\}$ (eq. (3)).
--
--   The **deterministic relaxation** replaces the counts by their means $\mathbb E[Z^n_j]=nf_j$ in the linear program (2):
--   $$DR(n,k)=\sup\Big\{\textstyle\sum_j a_js_j:\ 0\le s_j\le nf_j\ \text{for all } j,\ \sum_j s_j\le k\Big\},$$
--   and the candidate solution (16) is $s^*_j=\min\{nf_j,(k-n\bar F(a_j))_+\}$.
--
--   These objects are shared by every statement of the mission: the regret of a policy is measured against $V^*_{\mathrm{off}}$, and $DR$ is the intermediate benchmark of Lemma 3 and Proposition 6.
--
--   **Formalization Note** Lean index $j\in\{0,\dots,m-1\}$ is the paper's index $j+1$, so `a 0` is the largest value $a_1$, `f 0` is $f_1$ and `f (Fin.rev 0)` is $f_m$. The predicates `IsValues a` and `IsMasses f` carry the standing assumptions of Sec. 2 ($a$ strictly decreasing and positive; all masses positive, summing to one). Outcomes are sequences $x:\mathrm{Fin}\,n\to\mathrm{Fin}\,m$ with probability $\prod_t f_{x_t}$, and expectations are finite sums, which is exactly the i.i.d. law. `Fbar f j` takes a natural-number argument $j\in\{0,\dots,m\}$ and equals the paper's $\bar F(a_{j+1})$. The offline count uses natural-number subtraction, which is the positive part. $DR$ is the supremum of the LP objective over its feasible set (nonempty and bounded), not the formula $\sum_j a_js^*_j$; that identity is Remark 2.
-- source:
--   Arlotto, Gurvich, Uniformly Bounded Regret in the Multi-Secretary Problem, arXiv:1710.07719v2, Sec. 2, pp. 3–5 (model, V*_off); Sec. 3, eqs. (2)–(3), p. 7; Remark 2, eqs. (15)–(16), pp. 10–11

import Mathlib

namespace MultiSecretary.NonAdaptive

open Finset

/-- The ability values of the multi-secretary model (Arlotto–Gurvich, Sec. 2, pp. 3–4):
`0 < a_m < a_{m-1} < ⋯ < a_1`. Lean index `j : Fin m` is the paper's index `j + 1`, so `a 0` is the
largest value `a_1` and the values strictly decrease in the index. -/
def IsValues {m : ℕ} (a : Fin m → ℝ) : Prop :=
  StrictAnti a ∧ ∀ j, 0 < a j

/-- The probability masses `f_j = P(X_1 = a_j)` (Sec. 2, pp. 3–4): every mass is strictly positive
(the paper's `f_m = F(a_m) < F(a_{m-1}) < ⋯ < F(a_1) = 1`) and they sum to one. -/
def IsMasses {m : ℕ} (f : Fin m → ℝ) : Prop :=
  (∀ j, 0 < f j) ∧ ∑ j, f j = 1

/-- `ϵ = ½ min{f_m, …, f_1}`. -/
noncomputable def eps {m : ℕ} [NeZero m] (f : Fin m → ℝ) : ℝ :=
  (univ.inf' univ_nonempty f) / 2

/-- The survival function at the support points: `Fbar f j = f 0 + ⋯ + f (j-1)` for `j ∈ {0, …, m}`.
In the paper's 1-based notation, `Fbar f j = F̄(a_{j+1})`; in particular `Fbar f 0 = F̄(a_1) = 0` and
`Fbar f m = F̄(a_{m+1}) = 1` for masses summing to one. -/
noncomputable def Fbar {m : ℕ} (f : Fin m → ℝ) (j : ℕ) : ℝ :=
  ∑ i ∈ univ.filter (fun i : Fin m => i.val < j), f i

/-- The probability of the outcome sequence `x` (the `t`-th candidate has ability `a (x t)`) when
abilities are i.i.d. with masses `f`. -/
noncomputable def prob {m n : ℕ} (f : Fin m → ℝ) (x : Fin n → Fin m) : ℝ :=
  ∏ t, f (x t)

/-- Expectation of `g (X_1, …, X_n)` under the i.i.d. law with masses `f`, as a finite sum. -/
noncomputable def expect {m n : ℕ} (f : Fin m → ℝ) (g : (Fin n → Fin m) → ℝ) : ℝ :=
  ∑ x, prob f x * g x

/-- `Z^r_j = #{t ≤ r : X_t = a_j}`, the number of `a_j`-candidates among the first `r` (Sec. 3, p. 7). -/
def count {m n : ℕ} (x : Fin n → Fin m) (r : ℕ) (j : Fin m) : ℕ :=
  (univ.filter (fun t : Fin n => t.val < r ∧ x t = j)).card

/-- The offline number of selected `a_j`-candidates, eq. (3), p. 7:
`𝔖^n_j = min{Z^n_j, (k - ∑_{i < j} Z^n_i)_+}` (natural-number subtraction is the positive part). -/
def offCount {m n : ℕ} (k : ℕ) (x : Fin n → Fin m) (j : Fin m) : ℕ :=
  min (count x n j) (k - ∑ i ∈ univ.filter (fun i : Fin m => i < j), count x n i)

/-- The offline optimum for one realisation: the largest total ability of at most `k` of the
`n` candidates, `max {∑_t X_t σ_t : σ ∈ {0,1}^n, ∑_t σ_t ≤ k}` (Sec. 2, p. 5). -/
noncomputable def offMax {m n : ℕ} (a : Fin m → ℝ) (k : ℕ) (x : Fin n → Fin m) : ℝ :=
  (univ.filter (fun S : Finset (Fin n) => S.card ≤ k)).sup' ⟨∅, by simp⟩
    (fun S => ∑ t ∈ S, a (x t))

/-- The offline value `V*_off(n, k)`, the expected offline optimum (Sec. 2, p. 5). -/
noncomputable def Voff {m : ℕ} (a f : Fin m → ℝ) (n k : ℕ) : ℝ :=
  expect f (fun x : Fin n → Fin m => offMax a k x)

/-- The deterministic relaxation `DR(n, k) = φ(E[Z^n_1], …, E[Z^n_m], k)`, eq. (15), p. 10, where
`φ(z, k) = max {∑_j a_j s_j : 0 ≤ s_j ≤ z_j, ∑_j s_j ≤ k}` is the linear program (2), p. 7, and
`E[Z^n_j] = n f_j`. Written as the supremum of the objective over the feasible set. -/
noncomputable def DR {m : ℕ} (a f : Fin m → ℝ) (n k : ℕ) : ℝ :=
  sSup {v : ℝ | ∃ s : Fin m → ℝ, (∀ j, 0 ≤ s j ∧ s j ≤ (n : ℝ) * f j) ∧
    ∑ j, s j ≤ (k : ℝ) ∧ v = ∑ j, a j * s j}

/-- The candidate solution (16), p. 11: `s*_j = min{n f_j, (k - n F̄(a_j))_+}`. -/
noncomputable def sStar {m : ℕ} (f : Fin m → ℝ) (n k : ℕ) (j : Fin m) : ℝ :=
  min ((n : ℝ) * f j) (max 0 ((k : ℝ) - n * Fbar f j.val))

end MultiSecretary.NonAdaptive


