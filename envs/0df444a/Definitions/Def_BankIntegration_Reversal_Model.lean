-- Prove2me | Definitions.Def_BankIntegration_Reversal_Model
-- name    : BankIntegration_Reversal_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-21T05:02:17.936984+00:00
-- url     : https://prove2.me/theorems/5b318387-ab27-4e4c-82ed-ceb8d440f472
-- title:
--   §2, pp. 6–9; App. A, p. 22 — deposit-financed Cournot banking with borrower risk-shifting; segmented and integrated markets; the effects of (11)
-- statement:
--   This file fixes the banking model of Dam and Sengupta, §2 and Appendix A.
--
--   A banking market has $a>0$ depositors, $b>0$ borrowers (entrepreneurs) and $m$ banks. A borrower's project succeeds with probability $1-\theta/\lambda$ and then returns $\theta$, where the risk $\theta\in[0,\lambda]$ is chosen by the borrower. Inverse deposit supply and inverse loan demand are
--   $$R(D/a)=\frac{D}{a},\qquad r(L/b)=\lambda-\frac{L}{b}.$$
--   Banks are financed by deposits only, so aggregate deposits equal aggregate loans, $D=L=\sum_i L_i$.
--
--   1. **Bank profit.** With constant marginal lending cost $c$, bank $i$ lending $L_i$ earns, as in display (2), (7) and Appendix A,
--   $$\pi_i=\frac{L}{2\lambda b}\Big(\lambda-\frac{L}{b}-\frac{L}{a}-c\Big)L_i .$$
--   The segmented and integrated markets of §2 have $c=0$.
--   2. **Cournot equilibrium.** A profile $(L_1,\dots,L_m)$ is a Cournot equilibrium when every $L_i\ge0$ and no bank can raise its profit by switching to another volume $x\ge0$ while the other banks keep theirs. It is the published pure-strategy Nash equilibrium with feasible sets, specialised to $m$ banks with feasible set $[0,\infty)$ each.
--   3. **Borrower-optimal risk.** $\theta$ is borrower-optimal at the loan rate $r$ if $\theta\in[0,\lambda]$ maximizes $(1-\theta'/\lambda)(\theta'-r)$ over $\theta'\in[0,\lambda]$ (the problem in equation (1)).
--   4. **Customer composition.** $\xi=b/a$; for two markets with $(a_1,b_1)$ and $(a_2,b_2)$ the integrated market has $a_1+a_2$ depositors, $b_1+b_2$ borrowers and $\xi^*=(b_1+b_2)/(a_1+a_2)$.
--   5. **The two effects of (11).** For $n$ banks per segmented market,
--   $$\text{bank-competitor effect}=-\lambda\cdot\frac{1}{1+\xi^*}\Big(\frac{2n+1}{2n+2}-\frac{n+1}{n+2}\Big),\qquad \text{bank-customer effect w.r.t. market } j=\lambda\cdot\frac{n+1}{n+2}\Big(\frac{1}{1+\xi_j}-\frac{1}{1+\xi^*}\Big).$$
--   6. **Standing assumptions** (§2, p. 6): $\lambda>1$, $a_1,a_2,b_1,b_2>0$ and $n\ge1$.
--
--   These objects are shared by every statement of the mission: the segmented market $j$ is the Cournot game with $(a_j,b_j)$, $n$ banks and $c=0$; the integrated market is the Cournot game with $(a_1+a_2,b_1+b_2)$, $2n$ banks and $c=0$.
--
--   **Formalization Note** Banks are indexed by `Fin m`; loan volumes, rates and parameters are real numbers, and $n$ is a natural number cast to $\mathbb R$. The feasible set $L_i\ge0$ is stated explicitly (the page treats volumes as nonnegative implicitly). The loan and deposit rates are functions of the aggregate volume, so they are not separate variables, and the risk $\theta$ is defined by the maximization problem rather than by the closed form $(\lambda+r)/2$, which is a theorem of the mission. $\lambda>1$ is printed on p. 6 and kept, although no result uses more than $\lambda>0$.
-- source:
--   Dam & Sengupta, Bank competition and risk-taking under market integration, Federal Reserve Bank of Kansas City RWP 20-21 (updated Oct. 2024; doi:10.18651/RWP2020-21), pp. 6–10 (PDF 7–11), §2, (1), (2), (6), (7), (11); p. 22 (PDF 23), Appendix A

import Mathlib
import Definitions.Def_CarbonDoubleCount_Planner_PureGame

namespace BankIntegration.Reversal

/-- Expected profit of a bank lending `Li` when aggregate loans (= aggregate deposits) are `L`,
in a market with `a` depositors, `b` borrowers, project-return bound `lam` (λ) and marginal
lending cost `c`: display (2)/(7), and with cost `c` Appendix A, p. 22,
`(L / (2 λ b)) (λ − L/b − L/a − c) L_i`. -/
noncomputable def bankProfit (lam c a b L Li : ℝ) : ℝ :=
  L / (2 * lam * b) * (lam - L / b - L / a - c) * Li

/-- Inverse loan demand `r(L/b) = λ − L/b` (§2.1, p. 7; (6); (A.2)). -/
noncomputable def loanRate (lam b L : ℝ) : ℝ := lam - L / b

/-- Inverse deposit supply `R(D/a) = D/a` (§2.1, p. 7; (6); (A.1)). In equilibrium deposits equal
loans, so it is evaluated at the aggregate loan volume. -/
noncomputable def depositRate (a D : ℝ) : ℝ := D / a

/-- Cournot equilibrium of a banking market with `a` depositors, `b` borrowers, `m` banks and
marginal cost `c`: every bank `i : Fin m` chooses a loan volume `L i ∈ [0, ∞)` that maximizes its
expected profit `bankProfit lam c a b (∑ k, L k) (L i)` against the other banks' volumes. It is the
published feasible pure-strategy Nash equilibrium `CarbonDoubleCount.Planner.IsPureNash`. -/
def IsCournotEq (lam c a b : ℝ) (m : ℕ) (L : Fin m → ℝ) : Prop :=
  CarbonDoubleCount.Planner.IsPureNash (ι := Fin m) (strategy := fun _ => ℝ)
    (fun _ => Set.Ici (0 : ℝ)) (fun i M => bankProfit lam c a b (∑ k, M k) (M i)) L

/-- The borrower's problem behind equation (1): `θ ∈ [0, λ]` maximizes the expected margin
`(1 − θ/λ)(θ − r)` over all risks `θ' ∈ [0, λ]` at the loan rate `r`. -/
def IsOptimalRisk (lam r θ : ℝ) : Prop :=
  θ ∈ Set.Icc 0 lam ∧
    ∀ θ' ∈ Set.Icc 0 lam, (1 - θ' / lam) * (θ' - r) ≤ (1 - θ / lam) * (θ - r)

/-- Customer composition `ξ = b/a`, the ratio of borrowers to depositors (p. 7). -/
noncomputable def xi (a b : ℝ) : ℝ := b / a

/-- Customer composition of the integrated market, `ξ∗ = (b₁ + b₂)/(a₁ + a₂)` (Lemma 2). -/
noncomputable def xiStar (a1 a2 b1 b2 : ℝ) : ℝ := (b1 + b2) / (a1 + a2)

/-- The bank-competitor effect, first term of (11):
`−λ · 1/(1 + ξ∗) · ((2n + 1)/(2n + 2) − (n + 1)/(n + 2))`. -/
noncomputable def bankCompetitorEffect (lam : ℝ) (n : ℕ) (xs : ℝ) : ℝ :=
  -lam * (1 / (1 + xs)) *
    ((2 * (n : ℝ) + 1) / (2 * (n : ℝ) + 2) - ((n : ℝ) + 1) / ((n : ℝ) + 2))

/-- The bank-customer effect with respect to a market of composition `xj`, second term of (11):
`λ · (n + 1)/(n + 2) · (1/(1 + ξ_j) − 1/(1 + ξ∗))`. -/
noncomputable def bankCustomerEffect (lam : ℝ) (n : ℕ) (xj xs : ℝ) : ℝ :=
  lam * (((n : ℝ) + 1) / ((n : ℝ) + 2)) * (1 / (1 + xj) - 1 / (1 + xs))

/-- Standing assumptions of §2, p. 6: `λ > 1`, `a_j > 0` depositors, `b_j > 0` entrepreneurs,
and the same number `n ≥ 1` of banks in each market. -/
def Standing (lam a1 a2 b1 b2 : ℝ) (n : ℕ) : Prop :=
  1 < lam ∧ 0 < a1 ∧ 0 < a2 ∧ 0 < b1 ∧ 0 < b2 ∧ 1 ≤ n

end BankIntegration.Reversal


