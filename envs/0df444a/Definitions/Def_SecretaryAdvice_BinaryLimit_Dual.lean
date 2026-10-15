-- Prove2me | Definitions.Def_SecretaryAdvice_BinaryLimit_Dual
-- name    : SecretaryAdvice_BinaryLimit_Dual
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-15T00:42:37.090336+00:00
-- url     : https://prove2.me/theorems/21b1e37b-16f0-4edd-a395-45a377afea04
-- title:
--   §6, p. 21 — rescaled greedy dual and thresholds
-- statement:
--   For the binary advice LP, let $w_i^Y,w_i^N$ be the greedy solution to the dual after rescaling the paper’s original dual variables by $n$. Starting at time $n$ and moving backward, set
--
--   $$
--   w_i^Y=\max\left\{0,p-\frac{1-p'}{i}\sum_{j=i+1}^n(w_j^Y+w_j^N)\right\},\qquad
--   w_i^N=\max\left\{0,1-p-\frac{p'}{i}\sum_{j=i+1}^n(w_j^Y+w_j^N)\right\}.
--   $$
--
--   The thresholds $t_Y,t_N$ are the first times $i\in\{1,\ldots,n\}$ with $w_i^Y>0$ and $w_i^N>0$, respectively. If a signal has no positive coordinate, its threshold is $n+1$. The limiting value is
--
--   $$L(p,p')=\left(\frac{1-p'}p\right)^{(1-p')/p'}\exp\left(\frac{p-1}{p'}\right).$$
--
--   These objects connect the exact finite LP to the threshold and asymptotic claims.
--
--   **Formalization Note** The paper calls its rescaled dual $u$; this file calls it $w$ to keep it distinct from the original dual. At $p=1$, $N$ is never accepted and $t_N=n+1$; the paper informally writes $t_N=n$ at $p=p'=1$, which has the same normalized limit. Real $0^0=1$ gives $L(p,1)=e^{p-1}$.
-- source:
--   Dütting et al., Secretaries with Advice, arXiv:2011.06726v1, p. 21, proof of Theorem 20, rescaled dual

import Mathlib
import Definitions.Def_SecretaryAdvice_BinaryLimit_LP

namespace SecretaryAdvice.BinaryLimit

/-- After `k` backward steps, the already visited coordinates of the rescaled dual.
At the next step the new time is `n-k`; later coordinates are left unchanged. -/
noncomputable def greedyStages (n : ℕ) (p pp : ℝ) : ℕ → ℕ → Bool → ℝ
  | 0 => fun _ _ => 0
  | k + 1 => fun i s =>
      if i = n - k then
        let future := ∑ j ∈ Finset.Ioc i n,
          (greedyStages n p pp k j true + greedyStages n p pp k j false)
        max 0 ((if s then p else 1 - p) -
          (if s then 1 - pp else pp) / (i : ℝ) * future)
      else greedyStages n p pp k i s

/-- The rescaled greedy dual of section 6: `w = n u`, with Y = `true`. -/
noncomputable def w (n : ℕ) (p pp : ℝ) (i : ℕ) (s : Bool) : ℝ :=
  greedyStages n p pp n i s

/-- First positive Y coordinate, or `n+1` if there is none. -/
noncomputable def tY (n : ℕ) (p pp : ℝ) : ℕ :=
  by
    classical
    exact if ∃ i : ℕ, 1 ≤ i ∧ i ≤ n ∧ 0 < w n p pp i true then
      sInf {i : ℕ | 1 ≤ i ∧ i ≤ n ∧ 0 < w n p pp i true}
    else n + 1

/-- First positive N coordinate. `n+1` means N is never accepted. -/
noncomputable def tN (n : ℕ) (p pp : ℝ) : ℕ :=
  by
    classical
    exact if ∃ i : ℕ, 1 ≤ i ∧ i ≤ n ∧ 0 < w n p pp i false then
      sInf {i : ℕ | 1 ≤ i ∧ i ≤ n ∧ 0 < w n p pp i false}
    else n + 1

/-- The limit value displayed at the end of the proof of Theorem 20. -/
noncomputable def limitValue (p pp : ℝ) : ℝ :=
  ((1 - pp) / p) ^ ((1 - pp) / pp) * Real.exp (p / pp - 1 / pp)

end SecretaryAdvice.BinaryLimit


