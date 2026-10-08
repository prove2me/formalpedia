-- Prove2me | Definitions.Def_ReliableFacilityLoc_RRSP_RRSP
-- name    : ReliableFacilityLoc_RRSP_RRSP
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T02:17:00.281291+00:00
-- url     : https://prove2.me/theorems/7103f874-507e-4dd1-a684-1c3bb7d9eb3a
-- title:
--   The fixed-probability reformulation (RRSP$_i$) (7a)–(7e) and the numbers $\alpha_r$, $\beta_r$
-- statement:
--   Keep the data of the relaxed subproblem (RSP$_i$) of one customer $i$: $\lambda_i$, $d_{ij}$ for regular $j$, $d_{iJ} = \varphi_i$, failure probabilities $q_j$, multipliers $\mu_{ij}$ and levels $r = 0,\dots,R$.
--
--   1. Let $j_0, j_1, \dots, j_{J-1}$ be an ordering of the regular facilities with $q_{j_0} \le q_{j_1} \le \dots \le q_{j_{J-1}}$, given as a bijection $\sigma$ of $\{0,\dots,J-1\}$ with $j_\ell = \sigma(\ell)$.
--   2. Define
--
--   $$
--   \alpha_r = (1 - q_{j_r}) \prod_{\ell=0}^{r-1} q_{j_\ell}, \qquad \beta_r = \prod_{\ell=0}^{r-1} q_{j_\ell}.
--   $$
--
--   $\beta_r$ is the probability that the $r$ most reliable facilities all fail, and $\alpha_r$ the probability that, in addition, the next most reliable one survives.
--   3. (RRSP$_i$) minimizes, over the level assignments $Y$ (constraints (7b)–(7e), the same as (4b)–(4d), (4g)),
--
--   $$
--   \sum_{j=0}^{J-1}\sum_{r=0}^{R-1} \big(\lambda_i d_{ij}\alpha_r + \mu_{ij}\big) Y_{jr} + \sum_{r=0}^{R} \lambda_i d_{iJ} \beta_r Y_{Jr}.
--   $$
--
--   The reformulation replaces the variable probability $P_{jr}$ of (RSP$_i$) by the fixed number $\alpha_r$ for a regular facility and $\beta_r$ for the emergency facility. The result is an assignment problem in $Y$, solvable in strongly polynomial time.
--
--   **Formalization Note** $\alpha_r$ needs $j_r$, so it is defined only for $r < J$; for $r \ge J$ the Lean value is $0$. A regular facility can never sit at a level $r \ge J$ (the levels $0,\dots,r$ would hold $r+1 > J$ distinct regular facilities), so this value is never multiplied by a nonzero $Y_{jr}$. Likewise $\beta_r$ for $r > J$ is the product of all $J$ failure probabilities, and the emergency facility never sits above level $J$. No assumption $R \le J$ is made. The ordering is printed with last term $q_{J-1}$, a typo for $q_{j_{J-1}}$. Constraint (7b) is corrected like (4b) to sum over all facilities $j = 0,\dots,J$.
-- source:
--   Cui, Ouyang, Shen, Reliable Facility Location Design under the Risk of Disruptions, UCTC-FR-2010-02 (Feb. 2010), p. 14 (PDF 16), §3.3.2, definitions of α_r, β_r and (RRSP_i) (7a)–(7e)

import Mathlib
import Definitions.Def_ReliableFacilityLoc_RRSP_RSP

open Finset

namespace ReliableFacilityLoc.RRSP

/-- An ordering `j_0, j_1, …, j_{J−1}` of the regular facilities by nondecreasing failure
probability, `q_{j_0} ≤ q_{j_1} ≤ ⋯ ≤ q_{j_{J−1}}` (UCTC-FR-2010-02, §3.3.2, p. 14, PDF 16):
a bijection `σ` of `Fin J` with `j_ℓ = σ ℓ`.

Formalization Note: the last term is printed `q_{J−1}`; it is `q_{j_{J−1}}`. -/
def IsQOrdering {J : ℕ} (q : Fin J → ℝ) (σ : Fin J ≃ Fin J) : Prop :=
  Monotone (q ∘ σ)

/-- `β_r = Π_{ℓ=0}^{r−1} q_{j_ℓ}` (UCTC-FR-2010-02, §3.3.2, p. 14, PDF 16), the probability that
the `r` regular facilities with the smallest failure probabilities all fail.

Formalization Note: the product runs over the `ℓ : Fin J` with `ℓ < r`, so for `r ≥ J` it is the
product of all `J` failure probabilities. The paper uses `β_r` only at the level of the emergency
facility, which by (7b)–(7c) is at most `J` (the levels below it hold distinct regular
facilities), so the value for `r > J` is never multiplied by a nonzero `Y_Jr`. -/
def beta {J : ℕ} (q : Fin J → ℝ) (σ : Fin J ≃ Fin J) (r : ℕ) : ℝ :=
  ∏ ℓ ∈ univ.filter (fun ℓ : Fin J => (ℓ : ℕ) < r), q (σ ℓ)

/-- `α_r = (1 − q_{j_r}) Π_{ℓ=0}^{r−1} q_{j_ℓ}` (UCTC-FR-2010-02, §3.3.2, p. 14, PDF 16).

Formalization Note: `α_r` is defined by the paper only for `r ≤ J − 1` (it needs `j_r`). Here it is
`0` for `r ≥ J`. By (7b)–(7c) and pigeonhole a regular facility is never assigned at a level
`r ≥ J` (the levels `0, …, r` would hold `r + 1 > J` distinct regular facilities), so this junk
value is never multiplied by a nonzero `Y_jr`. No hypothesis `R ≤ J` is added. -/
def alpha {J : ℕ} (q : Fin J → ℝ) (σ : Fin J ≃ Fin J) (r : ℕ) : ℝ :=
  if h : r < J then (1 - q (σ ⟨r, h⟩)) * beta q σ r else 0

/-- The objective (7a) of the fixed-probability reformulation (RRSP_i) of the relaxed subproblem
(UCTC-FR-2010-02, §3.3.2, p. 14, PDF 16):
`Σ_{j=0}^{J-1} Σ_{r=0}^{R-1} (λ_i d_ij α_r + µ_ij) Y_jr + Σ_{r=0}^{R} λ_i d_iJ β_r Y_Jr`,
with `d_iJ = φ_i`. The constraints of (RRSP_i) are (7b)–(7e), i.e. `IsLevelAssignment Y`
(with (7b) corrected as there).

Formalization Note: `P_jr` of (RSP_i) is replaced by the fixed number `α_r` for a regular `j`
and by `β_r` for the emergency facility, as on p. 14. -/
def rrspObjective {J R : ℕ} (lam : ℝ) (d : Fin J → ℝ) (phi : ℝ) (q : Fin J → ℝ)
    (mu : Fin J → ℝ) (σ : Fin J ≃ Fin J) (Y : Fin (J + 1) → Fin (R + 1) → ℝ) : ℝ :=
  ∑ j : Fin J, ∑ r : Fin R, (lam * d j * alpha q σ r + mu j) * Y j.castSucc r.castSucc
    + ∑ r : Fin (R + 1), lam * phi * beta q σ r * Y (Fin.last J) r

end ReliableFacilityLoc.RRSP


