-- Prove2me | Definitions.Def_SingleMachineSched_Shared_RelaxationR
-- name    : SingleMachineSched_Shared_RelaxationR
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T03:52:09.399578+00:00
-- url     : https://prove2.me/theorems/0a0a1149-5a22-4f9a-a98d-db9b9e8f67d0
-- title:
--   The mean busy time relaxation (R) and its optimal value $Z_R$
-- statement:
--   For a nonempty set $S$ of jobs let $p(S) = \sum_{j \in S} p_j$ and $r_{\min}(S) = \min_{j \in S} r_j$. The **mean busy time relaxation** (R) of the problem of minimizing $\sum_j w_j C_j$ is the linear program
--
--   $$Z_R = \min \Big\{ \sum_{j \in N} w_j \Big(M_j + \tfrac12 p_j\Big) \;:\; \sum_{j \in S} p_j M_j \ge p(S)\Big(r_{\min}(S) + \tfrac12 p(S)\Big) \text{ for all nonempty } S \subseteq N \Big\}$$
--
--   in the real variables $M_j$, $j \in N$. The constraints are the shifted parallel inequalities (2.3).
--
--   Its optimal value $Z_R$ is a lower bound on the optimal value of the scheduling problem; Corollary 2.6 shows it equals the value $Z_D$ of the time-indexed relaxation.
--
--   It serves all three missions of the series: `01-lp-relaxations` (pp. 171–172, PDF pp. 7–8; Lemma 2.4, p. 172; Theorem 2.5 and Corollary 2.6, p. 173, PDF p. 9), `02-alpha-schedule` (p. 172, PDF p. 8; Theorem 2.5, p. 173, PDF p. 9; the benchmark $Z_R$ of Theorem 3.5, p. 183, PDF p. 19) and `03-alphaj-schedule` (pp. 171–172, PDF pp. 7–8; Theorem 2.5, p. 173, PDF p. 9; the benchmark $Z_R$ of Theorem 3.9, p. 185, PDF p. 21). It is reviewed once for all three.
--
--   **Formalization Note** The paper indexes the constraints by all $S \subseteq N$; for $S = \emptyset$ the constraint reads $0 \ge 0$, and $r_{\min}(\emptyset)$ is undefined, so only nonempty $S$ are listed. $Z_R$ is the infimum of the objective over the feasible set. The feasible set is nonempty (take all $M_j$ large), and for nonnegative weights the objective is bounded below on it (the singleton constraints give $M_j \ge r_j + p_j/2$), so the infimum is the LP value.
-- source:
--   Goemans, Queyranne, Schulz, Skutella & Wang, Single Machine Scheduling with Release Dates, SIAM J. Discrete Math. 15(2) (2002), p. 171 ($p(S)$, $r_{\min}(S)$), p. 172 (relaxation (R)); used on p. 173 (Theorem 2.5, Corollary 2.6), p. 183 (Theorem 3.5), p. 185 (Theorem 3.9)

import Mathlib

namespace SingleMachineSched.Shared

/-- `r_min(S) = min_{j ∈ S} r_j` for a nonempty set `S` of jobs. -/
def rmin {n : ℕ} (r : Fin n → ℕ) (S : Finset (Fin n)) (hS : S.Nonempty) : ℝ :=
  S.inf' hS (fun j => (r j : ℝ))

/-- `p(S) = Σ_{j ∈ S} p_j`. -/
def pSum {n : ℕ} (p : Fin n → ℕ) (S : Finset (Fin n)) : ℝ :=
  ∑ j ∈ S, (p j : ℝ)

/-- Feasibility for the mean busy time relaxation (R) (p. 172): for every nonempty set `S`,
`Σ_{j ∈ S} p_j M_j ≥ p(S) (r_min(S) + p(S)/2)`. -/
def FeasibleR {n : ℕ} (p r : Fin n → ℕ) (M : Fin n → ℝ) : Prop :=
  ∀ S : Finset (Fin n), ∀ hS : S.Nonempty,
    pSum p S * (rmin r S hS + pSum p S / 2) ≤ ∑ j ∈ S, (p j : ℝ) * M j

/-- The objective of (R): `Σ_j w_j (M_j + p_j/2)`. -/
noncomputable def objR {n : ℕ} (p : Fin n → ℕ) (w : Fin n → ℝ) (M : Fin n → ℝ) : ℝ :=
  ∑ j, w j * (M j + (p j : ℝ) / 2)

/-- `Z_R`, the optimal value of (R). The feasible set is nonempty, and for `w ≥ 0` the
objective is bounded below on it (the singleton constraints give `M_j ≥ r_j + p_j/2`), so this
infimum is the LP value. -/
noncomputable def zR {n : ℕ} (p r : Fin n → ℕ) (w : Fin n → ℝ) : ℝ :=
  sInf ((fun M => objR p w M) '' {M | FeasibleR p r M})

end SingleMachineSched.Shared


