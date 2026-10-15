-- Prove2me | Definitions.Def_SecretaryAdvice_SamplesDual_GreedyDual
-- name    : SecretaryAdvice_SamplesDual_GreedyDual
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-15T00:41:11.381455+00:00
-- url     : https://prove2.me/theorems/e9b16243-bbbe-4eb3-a1ff-c6628bf4ce7c
-- title:
--   Eq. (8), p. 13 — the greedy backward-induction solution of the dual LP, and its un-clipped variant
-- statement:
--   Fix a number of rounds $n$, a finite signal space $\mathcal S$, and real coefficients $a(i,s)$ and $c(j,s',i,s)$ for rounds $i,j$ and signals $s,s'\in\mathcal S$. These are the data of the dual linear program
--
--   $$\min \sum_i\sum_s u(i,s)\quad\text{s.t.}\quad u(i,s)+\sum_{j>i}\sum_{s'}u(j,s')\,c(j,s',i,s)\ge a(i,s),\qquad u(i,s)\ge 0 .$$
--
--   The **greedy solution** of equation (8) is computed by backward induction over the rounds: $u(n,s)=a(n,s)$ for every signal $s$, and for $i<n$, once $u(j,s')$ is known for all $j>i$ and all $s'$,
--
--   $$u(i,s)=\max\Bigl\{0,\; a(i,s)-\sum_{j=i+1}^{n}\sum_{s'\in\mathcal S}u(j,s')\,c(j,s',i,s)\Bigr\}.$$
--
--   The **un-clipped recursion** $v$ is the same backward induction without the $\max\{0,\cdot\}$: $v(n,s)=a(n,s)$ and $v(i,s)=a(i,s)-\sum_{j=i+1}^{n}\sum_{s'}v(j,s')\,c(j,s',i,s)$ for $i<n$.
--
--   The greedy solution is a feasible point of the dual LP; for the secretary problem with samples it is the optimal dual solution, and Theorem 17 gives it in closed form. The un-clipped recursion is the object the paper's proof of Theorem 17 actually manipulates.
--
--   **Formalization Note** Rounds are natural numbers and the paper's rounds are $1,\dots,n$; the definitions also return values at rounds $i>n$ and $i=0$ (namely $a(i,s)$, resp. the recursion), which are never used. The recursion is by well-founded recursion on $n-i$.
-- source:
--   Dütting et al., Secretaries with Advice, arXiv:2011.06726v1, p. 13, equation (8)

import Mathlib

namespace SecretaryAdvice.SamplesDual

/-!
Equation (8), p. 13 of Dütting, Lattanzi, Paes Leme, Vassilvitskii, *Secretaries with Advice*
(arXiv:2011.06726v1): the greedy (backward-induction) solution of the dual LP
`min Σ_i Σ_s u(i,s)` s.t. `u(i,s) + Σ_{j>i} Σ_{s'} u(j,s')·c(j,s',i,s) ≥ a(i,s)`, `u ≥ 0`.

Rounds are the naturals `1, …, n`; signals range over a finite type `S`.
`a i s` is the coefficient `a(i,s)` and `c j s' i s` is the coefficient `c(j,s',i,s)`.
Values at rounds `i > n` (and `i = 0`) are never used by the paper.
-/

/-- The greedy solution (8): `u(n,s) = a(n,s)`, and for `i < n`
`u(i,s) = max {0, a(i,s) − Σ_{j>i} Σ_{s'} u(j,s')·c(j,s',i,s)}`, the sum over rounds
`j ∈ {i+1, …, n}`. Defined by recursion on `n − i`. -/
noncomputable def greedyDual (n : ℕ) {S : Type*} [Fintype S]
    (a : ℕ → S → ℝ) (c : ℕ → S → ℕ → S → ℝ) (i : ℕ) (s : S) : ℝ :=
  if i < n then
    max 0 (a i s - ∑ j ∈ (Finset.Ioc i n).attach, ∑ s' : S,
      greedyDual n a c j.1 s' * c j.1 s' i s)
  else a i s
termination_by n - i
decreasing_by
  have hj := Finset.mem_Ioc.mp j.2
  omega

/-- The same backward recursion with the clipping `max {0, ·}` removed:
`v(n,s) = a(n,s)` and, for `i < n`, `v(i,s) = a(i,s) − Σ_{j>i} Σ_{s'} v(j,s')·c(j,s',i,s)`.
This is the recursion the paper's proof of Theorem 17 works with ("we can ignore the max"). -/
noncomputable def unclippedDual (n : ℕ) {S : Type*} [Fintype S]
    (a : ℕ → S → ℝ) (c : ℕ → S → ℕ → S → ℝ) (i : ℕ) (s : S) : ℝ :=
  if i < n then
    a i s - ∑ j ∈ (Finset.Ioc i n).attach, ∑ s' : S,
      unclippedDual n a c j.1 s' * c j.1 s' i s
  else a i s
termination_by n - i
decreasing_by
  have hj := Finset.mem_Ioc.mp j.2
  omega

end SecretaryAdvice.SamplesDual


