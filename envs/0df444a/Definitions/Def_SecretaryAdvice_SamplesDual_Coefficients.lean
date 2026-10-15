-- Prove2me | Definitions.Def_SecretaryAdvice_SamplesDual_Coefficients
-- name    : SecretaryAdvice_SamplesDual_Coefficients
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-15T00:41:50.981733+00:00
-- url     : https://prove2.me/theorems/52df9eb9-fa84-4325-a9c1-eaee2591b171
-- title:
--   §5, p. 15 — the dual LP coefficients a(i,s), c(j,s′,i,s) for secretaries with k samples, and the greedy solution
-- statement:
--   In the secretary problem with $k$ samples there are $n$ secretaries arriving in rounds $i=1,\dots,n$, and the signal of a secretary is $s\in\{0,1,\dots,k\}$, the number of sample elements smaller than it. The coefficients of the dual LP of §5 are
--
--   $$a(i,s)=\frac{1}{k+1}\prod_{t=1}^{n-1}\frac{s+t}{k+t+1},$$
--
--   which does not depend on $i$, and, for $j>i$,
--
--   $$c(j,s',i,s)=\begin{cases}\dfrac{1}{s'+1}\displaystyle\prod_{t=1}^{i-1}\frac{s+t}{s'+t+1}, & s'\ge s,\\[2mm] 0, & s'<s,\end{cases}$$
--
--   which does not depend on $j$. Products with an empty range ($n=1$, resp. $i=1$) equal $1$.
--
--   With these coefficients, $u(i,s)$ denotes the greedy solution of equation (8) and $v(i,s)$ the same backward recursion without the clipping $\max\{0,\cdot\}$, both over the signal space $\{0,\dots,k\}$.
--
--   These are the objects of Theorem 17: its explicit formula describes exactly this $u$.
--
--   **Formalization Note** The signal is a term of `Fin (k + 1)` in the recursion and a natural number $s\le k$ in the coefficient formulas; all arithmetic is in $\mathbb R$ after casting. The dual LP on p. 15 writes the sum as $\sum_{s'\ge s}$; here it is written as a sum over all signals with $c=0$ for $s'<s$, which is the same sum.
-- source:
--   Dütting et al., Secretaries with Advice, arXiv:2011.06726v1, p. 15, §5 LP Formulation (coefficients a(i,s), c(i,s,j,s′) and the dual LP); p. 13, equation (8)

import Mathlib
import Definitions.Def_SecretaryAdvice_SamplesDual_GreedyDual

namespace SecretaryAdvice.SamplesDual

/-!
§5 *LP Formulation*, p. 15 of Dütting et al., *Secretaries with Advice* (arXiv:2011.06726v1):
the coefficients of the dual LP for the secretary problem with `k` samples and `n` secretaries,
and the greedy solution (8), p. 13, with these coefficients.

Rounds `i` are the naturals `1, …, n` (1-based, as in the paper); the signal `s ∈ {0, 1, …, k}`
is the number of samples smaller than the current secretary, encoded as `s : Fin (k + 1)`
in the recursion and as a natural number `s ≤ k` in the formulas.
-/

/-- `a(i,s) = 1/(k+1) · ∏_{t=1}^{n−1} (s+t)/(k+t+1)` (it does not depend on `i`). -/
noncomputable def coeffA (n k s : ℕ) : ℝ :=
  1 / ((k : ℝ) + 1) * ∏ t ∈ Finset.Icc 1 (n - 1), ((s : ℝ) + t) / ((k : ℝ) + t + 1)

/-- The coefficient `c(j,s',i,s)` of the dual constraint at `(i,s)`, for `j > i`:
`1/(s'+1) · ∏_{t=1}^{i−1} (s+t)/(s'+t+1)` if `s' ≥ s`, and `0` if `s' < s`
(the dual LP on p. 15 sums only over `s' ≥ s`). It does not depend on `j`. -/
noncomputable def coeffC (s' i s : ℕ) : ℝ :=
  if s ≤ s' then
    1 / ((s' : ℝ) + 1) * ∏ t ∈ Finset.Icc 1 (i - 1), ((s : ℝ) + t) / ((s' : ℝ) + t + 1)
  else 0

/-- The greedy dual solution (8) with the samples coefficients, `u(i,s)`, for rounds
`1 ≤ i ≤ n` and signals `s ∈ {0, …, k}`. -/
noncomputable def samplesGreedy (n k : ℕ) (i : ℕ) (s : Fin (k + 1)) : ℝ :=
  greedyDual n (S := Fin (k + 1)) (fun _ s => coeffA n k s) (fun _ s' i s => coeffC s' i s) i s

/-- The un-clipped backward recursion with the samples coefficients, `v(i,s)`:
`v(n,s) = a(n,s)`, `v(i,s) = a(i,s) − Σ_{j>i} Σ_{s'} v(j,s')·c(j,s',i,s)` for `i < n`. -/
noncomputable def samplesUnclipped (n k : ℕ) (i : ℕ) (s : Fin (k + 1)) : ℝ :=
  unclippedDual n (S := Fin (k + 1)) (fun _ s => coeffA n k s) (fun _ s' i s => coeffC s' i s) i s

end SecretaryAdvice.SamplesDual


