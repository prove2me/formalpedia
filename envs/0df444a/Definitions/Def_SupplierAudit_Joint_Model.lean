-- Prove2me | Definitions.Def_SupplierAudit_Joint_Model
-- name    : SupplierAudit_Joint_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T03:30:40.630732+00:00
-- url     : https://prove2.me/theorems/2fc2fb56-4c33-4dbe-8004-77d297180a22
-- title:
--   Sec. 3, Lemma 1, OA.2, Sec. 4.3 — supplier-auditing model: stage-2 profits, expected profits, unilateral equilibrium, joint-auditing coalition, cost shares, thresholds
-- statement:
--   This file sets up the two-stage supply-chain model of Chen, Qi and Dawande and the joint-auditing coalition of their Section 4.3.
--
--   **Parameters.** Two buyers $B_1, B_2$ source from three suppliers: $B_i$ from its independent supplier $S_i$ and both from the common supplier $S_c$. The data are the willingness-to-pay level $\alpha$, the substitution parameter $\beta\in[0,1]$, wholesale prices $w\le\hat w$, the MWTP damage $d_M>0$, the suppliers' responsibility effort $e\in(0,1)$, the public-discovery probability $r\in(0,1]$ and the variable-cost coefficient $a>0$, subject to the positivity conditions of p. 8:
--   $$(2-\beta)\alpha-2d_M>2(1-\beta)w+2\hat w,\qquad (2-\beta)(\alpha-d_M)>(4-\beta)\hat w-\beta w,\qquad \alpha-d_M>2\hat w.$$
--
--   **Stage 2.** If buyer $B_i$ has $n_i\in\{0,1,2\}$ suppliers exposed as non-compliant, its demand intercept is $A_i=\alpha-d_M\mathbf 1\{n_i\ge1\}$ and its unit input cost is $c_i=(2-n_i)w+n_i\hat w$. The buyers play a differentiated Cournot game, and $B_1$'s equilibrium quantity and profit are
--   $$q_1^*=\frac{2(A_1-c_1)-\beta(A_2-c_2)}{4-\beta^2},\qquad \pi^b_1(n_1,n_2)=(q_1^*)^2,$$
--   with $\pi^b_2(n_1,n_2)=\pi^b_1(n_2,n_1)$. The aggregate ex post profit is $\pi^b(i\,d_M,j\,d_M)=\pi^b_1(i,j)+\pi^b_2(i,j)$, where $i,j$ count exposed suppliers. The **scenario** of Sec. 4.3 is the chain
--   $$\pi^b(0,0)\ge\pi^b(d_M,0)\ge\pi^b(d_M,d_M)\ge\pi^b(2d_M,d_M)\ge\pi^b(2d_M,2d_M).$$
--
--   **Damage probabilities and expected profits.** An independent supplier audited with effort $x$ causes damage with probability $\lambda_I(x)=r(1-e)(1-x)$; the common supplier audited by the buyers with efforts $x_1,x_2$ does so with probability $\lambda_C(x_1,x_2)=r(1-e)(1-x_1)(1-x_2)$. The three suppliers offend independently. Buyer $B_1$'s gross expected profit is the expectation of $\pi^b_1(n_1,n_2)$ over the eight outcomes, where $n_1$ counts offending suppliers among $S_1,S_c$ and $n_2$ among $S_2,S_c$. Auditing a supplier with effort $x$ costs $K\mathbf 1\{x>0\}+\tfrac a2x^2$.
--
--   **Unilateral auditing.** $\Pi^b_1(e_{11},e_{1c};e_{22},e_{2c})$ is $B_1$'s gross expected profit minus the costs of its own audits, and $\Pi^b_2$ is symmetric. A strategy is a pair of efforts in $[0,1]^2$ on (own independent supplier, common supplier), at most one of them positive. A profile is an **equilibrium** if each buyer's strategy is a best response and, following the paper's tie-breaking rule, a buyer who audits earns strictly more than by not auditing. The effort $\hat e_I$ is eq. (2) of p. 11.
--
--   **Joint auditing.** A joint plan $x=(e_{c1},e_{cc},e_{c2})$ gives the coalition's efforts on $S_1,S_c,S_2$; it is **feasible** if every effort lies in $[0,1]$ and at most two are positive. Write $R^b_i(x)$ for $B_i$'s gross expected profit when the common supplier is audited once, $\lambda_C=r(1-e)(1-e_{cc})$. The coalition's aggregate profit is
--   $$\Pi^b(x)=R^b_1(x)+R^b_2(x)-\sum_{j\in\{1,c,2\}}\Big[K\mathbf 1\{e_{cj}>0\}+\tfrac a2e_{cj}^2\Big],$$
--   so each audited supplier's cost is charged once. Further, $\Delta\Pi=R^b_1(x)-R^b_2(x)$, and the cost shares are $\Gamma_{1,2}=\tfrac12[\text{total auditing cost}\pm\Delta\Pi]$. The thresholds are
--   $$\hat K=\max_{y\in[0,1]}\Pi^b(0,y,0)\big|_{K=0}-\Pi^b(0,0,0),\qquad \tilde K=\max_{(y,z)\in[0,1]^2}\Pi^b(y,z,0)\big|_{K=0}-\max_{y\in[0,1]}\Pi^b(0,y,0)\big|_{K=0},$$
--   $$K^L_c=\min\Big\{\tfrac{\hat K+\tilde K}2,\tilde K\Big\},\qquad K^H_c=\max\Big\{\tfrac{\hat K+\tilde K}2,\hat K\Big\}.$$
--
--   These objects are shared by every statement of the mission on Proposition 3.
--
--   **Formalization Note** A joint plan is a triple `(e_c1, e_cc, e_c2) : ℝ × ℝ × ℝ`. The maxima defining $\hat K$ and $\tilde K$ are written as `sSup` of the image of a compact box. At $K=0$ the profit is a polynomial in the efforts, so these images are compact and nonempty and the supremum is attained. Buyer $B_2$'s gross profit is buyer $B_1$'s formula with the roles of $S_1$ and $S_2$ exchanged. The cost shares use the total cost over all three suppliers; for a plan that does not audit $S_2$ this is the sum over $j\in\{1,c\}$ printed in eq. (3).
-- source:
--   Chen, Qi, Dawande, Supplier Centrality and Auditing Priority in Socially-Responsible Supply Chains, accepted manuscript (SSRN 2889889), Sec. 3, pp. 5–8; Lemma 1, p. 9; eq. (2), p. 11; Sec. 4.3, p. 13; eq. (3), p. 14; OA.2, p. ec1 (PDF 29); proofs of Lemmas OA9–OA11 and Proposition 3, pp. ec11–ec13 (PDF 39–41)

import Mathlib
import Definitions.Def_SupplierAudit_Competition_Model

namespace SupplierAudit.Joint

open Set

variable (P : SupplierAudit.Competition.Params)

/-- Demand intercept minus unit input cost, `A_i − c_i`, of a buyer with `n ∈ {0,1,2}` offending
suppliers: the intercept is `α − d_M·[n ≥ 1]` (the MWTP damage is incurred once) and the unit input
cost is `(2 − n)w + nŵ`. -/
noncomputable def margin (n : ℕ) : ℝ :=
  P.α - (if 1 ≤ n then P.dM else 0) - ((2 - (n : ℝ)) * P.w + (n : ℝ) * P.wh)

/-- Buyer `B₁`'s stage-2 (Cournot) equilibrium quantity when `B₁` has `n₁` and `B₂` has `n₂`
offending suppliers: `q*₁ = (2(A₁ − c₁) − β(A₂ − c₂))/(4 − β²)` (Lemma 1, p. 9). -/
noncomputable def stage2q₁ (n₁ n₂ : ℕ) : ℝ :=
  (2 * margin P n₁ - P.β * margin P n₂) / (4 - P.β ^ 2)

/-- Buyer `B₁`'s stage-2 equilibrium profit `π^b_1 = (q*₁)²` (Lemma 1, p. 9). -/
noncomputable def stage2Profit₁ (n₁ n₂ : ℕ) : ℝ := (stage2q₁ P n₁ n₂) ^ 2

/-- Buyer `B₂`'s stage-2 equilibrium profit; the game is symmetric, so it is `B₁`'s profit with the
roles of the buyers exchanged. -/
noncomputable def stage2Profit₂ (n₁ n₂ : ℕ) : ℝ := stage2Profit₁ P n₂ n₁

/-- `π^b(i d_M, j d_M)` (p. 13): the aggregate ex post profit of the two buyers when `B₁` has `i`
and `B₂` has `j` suppliers identified as socially irresponsible. The arguments count offending
suppliers; the MWTP damage itself is `d_M` once. -/
noncomputable def piAgg (i j : ℕ) : ℝ := stage2Profit₁ P i j + stage2Profit₂ P i j

/-- The scenario of Sec. 4.3 (p. 13):
`π^b(0,0) ≥ π^b(d_M,0) ≥ π^b(d_M,d_M) ≥ π^b(2d_M,d_M) ≥ π^b(2d_M,2d_M)`. -/
def Scenario : Prop :=
  piAgg P 1 0 ≤ piAgg P 0 0 ∧ piAgg P 1 1 ≤ piAgg P 1 0 ∧ piAgg P 2 1 ≤ piAgg P 1 1 ∧
    piAgg P 2 2 ≤ piAgg P 2 1

/-- Buyer `B₁`'s expected stage-2 profit, excluding auditing costs, when `S₁`, `S_c`, `S₂` offend
independently with probabilities `l₁`, `lc`, `l₂`: the expectation over the 8 outcomes
`(b₁, b_c, b₂)` of `π^b_1(n₁, n₂)` with `n₁ = b₁ + b_c`, `n₂ = b₂ + b_c`. -/
noncomputable def grossProfit₁ (l₁ lc l₂ : ℝ) : ℝ :=
  ∑ b : Bool × Bool × Bool,
    (if b.1 then l₁ else 1 - l₁) * (if b.2.1 then lc else 1 - lc) * (if b.2.2 then l₂ else 1 - l₂) *
      stage2Profit₁ P (b.1.toNat + b.2.1.toNat) (b.2.2.toNat + b.2.1.toNat)

/-- Buyer `B₂`'s expected stage-2 profit, excluding auditing costs (symmetric to `B₁`): `l₁`, `lc`,
`l₂` are still the damage probabilities of `S₁`, `S_c`, `S₂`. -/
noncomputable def grossProfit₂ (l₁ lc l₂ : ℝ) : ℝ := grossProfit₁ P l₂ lc l₁

/-! ### Unilateral auditing (Sec. 3, Sec. 4.2): the benchmark for stability -/

/-- `Π^b_1(e₁₁, e₁c; e₂₂, e₂c)`: buyer `B₁`'s ex ante expected profit under unilateral auditing
(OA.2, p. ec1), the 8-outcome expectation minus `B₁`'s own auditing costs. -/
noncomputable def expProfit₁ (K e11 e1c e22 e2c : ℝ) : ℝ :=
  grossProfit₁ P (SupplierAudit.Competition.lamI P e11) (SupplierAudit.Competition.lamC P e1c e2c) (SupplierAudit.Competition.lamI P e22) - SupplierAudit.Competition.auditCost P K e11 - SupplierAudit.Competition.auditCost P K e1c

/-- `Π^b_2(e₂₂, e₂c; e₁₁, e₁c)`: buyer `B₂`'s expected profit (symmetric), in the paper's argument
order (own efforts first). -/
noncomputable def expProfit₂ (K e22 e2c e11 e1c : ℝ) : ℝ :=
  grossProfit₂ P (SupplierAudit.Competition.lamI P e11) (SupplierAudit.Competition.lamC P e1c e2c) (SupplierAudit.Competition.lamI P e22) - SupplierAudit.Competition.auditCost P K e22 - SupplierAudit.Competition.auditCost P K e2c

/-- A buyer's unilateral auditing strategy `(own independent supplier effort, common supplier
effort) ∈ [0,1]²`; a buyer audits at most one of his two suppliers (p. 7), so one effort is `0`. -/
abbrev Strategy : Type := {s : ℝ × ℝ // s.1 ∈ Icc (0 : ℝ) 1 ∧ s.2 ∈ Icc (0 : ℝ) 1 ∧ s.1 * s.2 = 0}

/-- The no-audit strategy `(0, 0)`. -/
def noAudit : Strategy := ⟨(0, 0), by norm_num⟩

/-- Buyer `B₁`'s unilateral expected profit at the profile `(s₁, s₂)`. -/
noncomputable def unilProfit₁ (K : ℝ) (s₁ s₂ : Strategy) : ℝ :=
  expProfit₁ P K s₁.1.1 s₁.1.2 s₂.1.1 s₂.1.2

/-- Buyer `B₂`'s unilateral expected profit at the profile `(s₁, s₂)`. -/
noncomputable def unilProfit₂ (K : ℝ) (s₁ s₂ : Strategy) : ℝ :=
  expProfit₂ P K s₂.1.1 s₂.1.2 s₁.1.1 s₁.1.2

/-- Unilateral-auditing equilibrium with the paper's tie-breaking rule (p. 10): each buyer's strategy
is a best response to the other's, and a buyer who audits strictly prefers it to not auditing
("when a buyer is indifferent between auditing a supplier and no-audit, … the buyer chooses
no-audit"). -/
def IsEquilibrium (K : ℝ) (s₁ s₂ : Strategy) : Prop :=
  (∀ t : Strategy, unilProfit₁ P K t s₂ ≤ unilProfit₁ P K s₁ s₂) ∧
  (∀ t : Strategy, unilProfit₂ P K s₁ t ≤ unilProfit₂ P K s₁ s₂) ∧
  (s₁.1 ≠ (0, 0) → unilProfit₁ P K noAudit s₂ < unilProfit₁ P K s₁ s₂) ∧
  (s₂.1 ≠ (0, 0) → unilProfit₂ P K s₁ noAudit < unilProfit₂ P K s₁ s₂)

/-! ### Joint auditing (Sec. 4.3, pp. 13–14; e-companion pp. ec11–ec14)

A joint-auditing plan is `x = (e_c1, e_cc, e_c2) : ℝ × ℝ × ℝ`, the coalition's efforts on `S₁`,
`S_c`, `S₂`. -/

/-- `R^b_1(x)`: buyer `B₁`'s expected profit, excluding auditing costs, under the joint plan `x`;
the common supplier is audited once, so `λ_C = r(1−e)(1−e_cc)`. -/
noncomputable def jointG₁ (x : ℝ × ℝ × ℝ) : ℝ :=
  grossProfit₁ P (SupplierAudit.Competition.lamI P x.1) (P.r * (1 - P.e) * (1 - x.2.1)) (SupplierAudit.Competition.lamI P x.2.2)

/-- `R^b_2(x)`: buyer `B₂`'s expected profit, excluding auditing costs, under the joint plan `x`. -/
noncomputable def jointG₂ (x : ℝ × ℝ × ℝ) : ℝ :=
  grossProfit₂ P (SupplierAudit.Competition.lamI P x.1) (P.r * (1 - P.e) * (1 - x.2.1)) (SupplierAudit.Competition.lamI P x.2.2)

/-- Total auditing cost of the joint plan `x`, each audited supplier charged once to the coalition. -/
noncomputable def totalCost (K : ℝ) (x : ℝ × ℝ × ℝ) : ℝ :=
  SupplierAudit.Competition.auditCost P K x.1 + SupplierAudit.Competition.auditCost P K x.2.1 + SupplierAudit.Competition.auditCost P K x.2.2

/-- `Π^b(e_c1, e_cc, e_c2)`: the coalition's aggregate expected profit (pp. ec11–ec12). -/
noncomputable def aggProfit (K : ℝ) (x : ℝ × ℝ × ℝ) : ℝ :=
  jointG₁ P x + jointG₂ P x - totalCost P K x

/-- Feasible joint plans: efforts in `[0,1]`, and the coalition audits at most two of the three
suppliers (p. 13). -/
def Feasible : Set (ℝ × ℝ × ℝ) :=
  {x | x.1 ∈ Icc (0 : ℝ) 1 ∧ x.2.1 ∈ Icc (0 : ℝ) 1 ∧ x.2.2 ∈ Icc (0 : ℝ) 1 ∧
    (x.1 = 0 ∨ x.2.1 = 0 ∨ x.2.2 = 0)}

/-- `∆Π = R^b_1(x) − R^b_2(x)`: difference of the buyers' expected profits excluding auditing costs
(p. 13, p. ec13). -/
noncomputable def deltaPi (x : ℝ × ℝ × ℝ) : ℝ := jointG₁ P x - jointG₂ P x

/-- Buyer `B₁`'s cost share `Γ₁ = ½[total auditing cost + ∆Π]` (eq. (3), p. 14). -/
noncomputable def Gamma₁ (K : ℝ) (x : ℝ × ℝ × ℝ) : ℝ := (1 / 2) * (totalCost P K x + deltaPi P x)

/-- Buyer `B₂`'s cost share `Γ₂ = ½[total auditing cost − ∆Π]` (eq. (3), p. 14). -/
noncomputable def Gamma₂ (K : ℝ) (x : ℝ × ℝ × ℝ) : ℝ := (1 / 2) * (totalCost P K x - deltaPi P x)

/-- `Π^b(0, e*_cc, 0)|_{K=0}`: the coalition's optimal profit from auditing only `S_c`, at `K = 0`
(p. ec11). A maximum of a continuous function over `[0,1]`. -/
noncomputable def optCommonOnly : ℝ :=
  sSup ((fun y => aggProfit P 0 (0, y, 0)) '' Icc (0 : ℝ) 1)

/-- `Π^b(ê_c1, ê_cc, 0)|_{K=0}`: the coalition's optimal profit from auditing `S₁` and `S_c`, at
`K = 0` (p. ec12). A maximum of a continuous function over `[0,1]²`. -/
noncomputable def optOneCommon : ℝ :=
  sSup ((fun p : ℝ × ℝ => aggProfit P 0 (p.1, p.2, 0)) '' (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1))

/-- `K̂ ≜ Π^b(0, e*_cc, 0)|_{K=0} − Π^b(0, 0, 0)` (proof of Lemma OA9, p. ec11). -/
noncomputable def Khat : ℝ := optCommonOnly P - aggProfit P 0 (0, 0, 0)

/-- `K̃ ≜ Π^b(ê_c1, ê_cc, 0)|_{K=0} − Π^b(0, e*_cc, 0)|_{K=0}` (proof of Lemma OA11, p. ec12). -/
noncomputable def Ktilde : ℝ := optOneCommon P - optCommonOnly P

/-- `K^L_c = min{(K̂ + K̃)/2, K̃}` (proof of Proposition 3, p. ec13). -/
noncomputable def KcL : ℝ := min ((Khat P + Ktilde P) / 2) (Ktilde P)

/-- `K^H_c = max{(K̂ + K̃)/2, K̂}` (proof of Proposition 3, p. ec13). -/
noncomputable def KcH : ℝ := max ((Khat P + Ktilde P) / 2) (Khat P)

end SupplierAudit.Joint


