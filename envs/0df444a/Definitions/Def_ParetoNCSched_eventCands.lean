-- Prove2me | Definitions.Def_ParetoNCSched_eventCands
-- name    : ParetoNCSched_eventCands
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T03:12:06.692701+00:00
-- url     : https://prove2.me/theorems/d61ec563-4939-477e-91ad-16a4fbf48c61
-- title:
--   Event candidates of a step of $\mathrm{MRC}_R$
-- statement:
--   From the state at an event time $t_k$ with $N\ge2$, $\mathrm{MRC}_R$ runs $j$ at rate $a$ and each waiting job at rate $b$ until the next event, the first time $t>t_k$ at which
--
--   1. a job completes;
--   2. $D$ reaches $0$ (only if $D(t_k)<0$);
--   3. $e_j$ reaches the size of a completed job $i$ with $p_i\ne e_j(t_k)$;
--   4. $\ell$ reaches the size of a completed job $i$ with $p_i\ne \ell(t_k)$.
--
--   This set collects the positive durations $u$ after which each of these events happens under the constant rates: $(p_j-e_j)/a$; $(p_g-e_g)/b$ for a waiting job $g$; the first $u>0$ with $F+Nu-R\,\Phi(e+u\,r)\ge0$ when $D<0$; $(p_i-e_j)/a$ and $(p_i-\ell)/b$ for completed jobs $i$ of size $p_i>e_j$, resp. $p_i>\ell$.
--
--   **Formalization Note** Since $e_j$ and $\ell$ only increase, "$p_i\ne e_j(t_k)$" is written "$p_i>e_j(t_k)$": smaller sizes are never reached. Likewise for $\ell$.
-- source:
--   Benomar–Perchet, Pareto-optimal Non-Clairvoyant Scheduling with Predictions, manuscript (STOC 2027 submission, sha256 852cb174…), Appendix B, "The run, interval by interval", p.17; Algorithm 1, line 10, p.9

import Mathlib
import Definitions.Def_ParetoNCSched_commitRate
import Definitions.Def_ParetoNCSched_waitRate
import Definitions.Def_ParetoNCSched_mixRates
import Definitions.Def_ParetoNCSched_slack

namespace ParetoNCSched

/-- **Candidate lengths of the next step** (the four event types). Benomar–Perchet, *Pareto-optimal Non-Clairvoyant Scheduling with Predictions*, manuscript (STOC 2027 submission, sha256 852cb174…), Appendix B, "The run,
interval by interval", p.17: from the state at `t_k` (with `N ≥ 2`), run `j` at rate `a` and each
waiting job at rate `b` until `t_{k+1}`, "the first time t > t_k at which one of the following events
occurs: a job completes; D reaches 0 (only if D(t_k) < 0); eⱼ reaches the size of a completed job i
with pᵢ ≠ eⱼ(t_k); ℓ reaches the size of a completed job i with pᵢ ≠ ℓ(t_k)" (Algorithm 1, line 10,
p.9).

**Formalization Note.** The set collects every positive time `u` after `t_k` at which an event of
one of these types occurs under the constant rates: `j` completes at `(pⱼ − eⱼ)/a`; a waiting job
`g` completes at `(p_g − e_g)/b`; `D` reaches `0` at the first `u > 0` with
`F + N u − R Φ(e + u r) ≥ 0` (only if `D < 0`); `eⱼ` (resp. `ℓ`) reaches the size of a completed job
`i` at `(pᵢ − eⱼ)/a` (resp. `(pᵢ − ℓ)/b`). Since `eⱼ` and `ℓ` only increase, "pᵢ ≠ eⱼ(t_k)"
is written "pᵢ > eⱼ(t_k)" (smaller sizes are never reached), and similarly for `ℓ`. -/
noncomputable def eventCands {n : ℕ} (R : ℝ) (p : Fin n → ℝ) (s : MState n) (j : Fin n) : Set ℝ :=
  {u | 0 < u ∧
    (u = (p j - s.e j) / commitRate R p s j ∨
     (∃ g ∈ waiting p s j, u = (p g - s.e g) / waitRate R p s j) ∨
     (slack R s < 0 ∧
        u = sInf {v : ℝ | 0 < v ∧ 0 ≤ s.F + ((unfinished p s).card : ℝ) * v -
          R * Phi (s.e + v • mixRates p s j (commitRate R p s j))}) ∨
     (∃ i, i ∉ unfinished p s ∧ s.e j < p i ∧ u = (p i - s.e j) / commitRate R p s j) ∨
     (∃ i, i ∉ unfinished p s ∧ level p s j < p i ∧
        u = (p i - level p s j) / waitRate R p s j))}

end ParetoNCSched


