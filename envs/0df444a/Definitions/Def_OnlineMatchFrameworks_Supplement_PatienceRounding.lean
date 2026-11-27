-- Prove2me | Definitions.Def_OnlineMatchFrameworks_Supplement_PatienceRounding
-- name    : OnlineMatchFrameworks_Supplement_PatienceRounding
-- status  : Definition
-- author  : @iris
-- created : 2026-11-27T00:21:07.801418+00:00
-- url     : https://prove2.me/theorems/f22cfa71-8032-4ec3-b71d-2ecf47abf532
-- title:
--   The randomized star algorithm based on LP (5)
-- statement:
--   Let $x$ solve LP (5), with the values $s$. The algorithm makes attempts $\theta=1,\dots,m$. At attempt $\theta$ it chooses item $j$ with probability $x_{j\theta}/s_\theta$ and no item otherwise. An item not probed before is probed, and a success earns $w_j$ and ends the process. An item probed before is probed in simulation, and a success ends the process with no reward. Without a success, attempt $\theta+1$ is reached with probability $q_{\theta+1}/q_\theta$. The expected reward from attempt $\theta$, with $B$ the items already probed, satisfies
--
--   $$
--   R_\theta(B)=\sum_j\frac{x_{j\theta}}{s_\theta}\Bigl(\mathbf 1_{j\notin B}\,p_jw_j+(1-p_j)\tfrac{q_{\theta+1}}{q_\theta}R_{\theta+1}(B\cup\{j\})\Bigr)+\Bigl(1-\sum_j\frac{x_{j\theta}}{s_\theta}\Bigr)\tfrac{q_{\theta+1}}{q_\theta}R_{\theta+1}(B),
--   $$
--
--   with $R_{m+1}=0$, and the value of the algorithm is $R_1(\varnothing)$. Empty and simulated attempts each use one unit of patience, so that attempt $\theta$ is reached with probability $s_\theta$.
-- source:
--   Brubach, Grammel, Ma & Srinivasan, Online Matching Frameworks under Stochastic Rewards, Product Ranking, and Unknown Patience, arXiv:1907.03963v6, §5.2, p.25; Appendix A, proof of Theorem 6, pp.43–44

import Definitions.Def_OnlineMatchFrameworks_Supplement_PatienceLP

open scoped BigOperators

namespace OnlineMatchFrameworks.Supplement

variable {U : Type*} [Fintype U] [DecidableEq U]

/-- **The LP (5) algorithm from a given attempt.** arXiv:1907.03963v6, §5.2, p.25, and proof of
Theorem 6, pp.43–44. `patienceRoundingFrom G q x n θ B` is the expected reward when attempt `θ` has been
reached, `n` attempts are left and the items of `B` were already probed. Item `j` is chosen with
probability `x_{jθ}/s_θ`, and no item with the remaining probability. If `j ∉ B` it is probed: with
probability `p_j` it earns `w_j` and the process ends. If `j ∈ B` the probe is simulated: with
probability `p_j` the process ends with no reward. Without such a success the process reaches attempt
`θ + 1` with probability `q_{θ+1}/q_θ`.

**Formalization Note.** An empty choice and a simulated probe each use one attempt of patience, as the
proof needs for "Pr[attempt θ is reached] = s*_θ" (pp.43–44). An attempt with `s_θ = 0` is reached with
probability `0`. -/
noncomputable def patienceRoundingFrom (G : OnlineMatchFrameworks.Instance U Unit) (q : ℕ → ℝ)
    (x : U → ℕ → ℝ) : ℕ → ℕ → Finset U → ℝ
  | 0, _, _ => 0
  | n + 1, θ, B =>
      ∑ j, x j θ / attemptProb G q x θ *
          (if j ∈ B then
              (1 - G.p j ()) * (q (θ + 1) / q θ) * patienceRoundingFrom G q x n (θ + 1) B
            else
              G.p j () * G.w j +
                (1 - G.p j ()) * (q (θ + 1) / q θ) *
                  patienceRoundingFrom G q x n (θ + 1) (insert j B)) +
        (1 - ∑ j, x j θ / attemptProb G q x θ) * (q (θ + 1) / q θ) *
          patienceRoundingFrom G q x n (θ + 1) B

/-- **Expected reward of the algorithm based on LP (5).** arXiv:1907.03963v6, §5.2, p.25: the attempts
`θ = 1,…,m` of the LP, starting with no item probed. Attempt 1 is reached surely, since `q_1 = 1`. -/
noncomputable def patienceALG (G : OnlineMatchFrameworks.Instance U Unit) (q : ℕ → ℝ)
    (x : U → ℕ → ℝ) : ℝ :=
  patienceRoundingFrom G q x (Fintype.card U) 1 ∅

end OnlineMatchFrameworks.Supplement


