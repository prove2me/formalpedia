-- Prove2me | Definitions.Def_SupplierAudit_Competition_Model
-- name    : SupplierAudit_Competition_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T02:29:27.084425+00:00
-- url     : https://prove2.me/theorems/d64d6858-68e1-4729-8e36-490231e3f059
-- title:
--   Sec. 3, Lemma 1, OA.2, eqs. (1)–(2), (OA-9)–(OA-13) — the auditing game under downstream competition
-- statement:
--   Two buyers $B_1, B_2$ source from three suppliers: $S_1$ (independent supplier of $B_1$), $S_2$ (independent supplier of $B_2$) and the common supplier $S_c$. The parameters are the MWTP $\alpha$, the substitution parameter $\beta \in [0,1]$, wholesale prices $w \le \hat w$, the MWTP damage $d_M > 0$, the suppliers' social-responsibility effort $e \in (0,1)$, the public-discovery probability $r \in (0,1]$, and the variable-audit-cost coefficient $a > 0$. They satisfy the three conditions of p. 8,
--   $$(2-\beta)\alpha - 2d_M > 2(1-\beta)w + 2\hat w,\qquad (2-\beta)(\alpha-d_M) > (4-\beta)\hat w - \beta w,\qquad \alpha - d_M > 2\hat w .$$
--   The fixed audit cost $K$ is a separate real argument.
--
--   **Stage 2.** A buyer with $n \in \{0,1,2\}$ suppliers discovered as non-compliant has demand intercept $A(n) = \alpha$ if $n = 0$ and $A(n) = \alpha - d_M$ if $n \ge 1$, and unit input cost $c(n) = (2-n)w + n\hat w$. When $B_1$ has $n_1$ and $B_2$ has $n_2$ such suppliers, $B_1$'s stage-2 quantity and profit are
--   $$q^*_1(n_1,n_2) = \frac{2\,(A(n_1)-c(n_1)) - \beta\,(A(n_2)-c(n_2))}{4-\beta^2},\qquad \pi^b_1(n_1,n_2) = q^*_1(n_1,n_2)^2,$$
--   and $B_2$'s are $q^*_1(n_2,n_1)$ and $\pi^b_1(n_2,n_1)$.
--
--   **Stage 1.** Buyer $B_i$ puts effort $e_{ii} \in [0,1]$ on auditing $S_i$ and $e_{ic} \in [0,1]$ on $S_c$, and audits at most one supplier: $e_{ii}\,e_{ic} = 0$. With $\lambda_I(x) = r(1-e)(1-x)$ and $\lambda_C(x_1,x_2) = r(1-e)(1-x_1)(1-x_2)$, the suppliers $S_1, S_c, S_2$ cause damage independently with probabilities $\lambda_I(e_{11})$, $\lambda_C(e_{1c},e_{2c})$, $\lambda_I(e_{22})$; in an outcome $(b_1,b_c,b_2) \in \{0,1\}^3$, $n_1 = b_1 + b_c$ and $n_2 = b_2 + b_c$. Auditing a supplier with effort $x$ costs $K\mathbb 1_{x>0} + \tfrac a2 x^2$. Buyer $B_1$'s expected profit $\Pi^b_1(e_{11},e_{1c};e_{22},e_{2c})$ is the expectation of $\pi^b_1(n_1,n_2)$ over the 8 outcomes minus his two audit costs; $\Pi^b_2(e_{22},e_{2c};e_{11},e_{1c})$ is the same expression with the buyers' roles exchanged.
--
--   **Equilibrium.** A profile $(s_1,s_2)$ with $s_i = (e_{ii},e_{ic})$ is an equilibrium if each $s_i$ is a strategy, maximizes $B_i$'s expected profit over all strategies given $s_{i'}$, and, when $s_i \ne (0,0)$, gives $B_i$ strictly more than no-audit $(0,0)$ (the tie-breaking rule of p. 10: a buyer indifferent between auditing and not auditing does not audit). $\mathrm{EqSet}(K)$ is the set of equilibrium profiles.
--
--   **Efforts and thresholds.** With $X = r(1-e)$ and the brace
--   $$\Phi = \alpha(2-\beta)\{[1-X]d_M + \hat w - w\} - d_M w[1-2X]\{2-\beta[2-X]\} - d_M\hat w\{2-\beta X[3-2X]\} - d_M^2[1-X][1-\beta X] - (\hat w - w)\{w[3-2\beta-2(1-\beta)X] + \hat w[1+2(1-\beta)X]\},$$
--   eqs. (1) and (2) of p. 11 are
--   $$e^*_I = \frac{4X\,\Phi}{a(4-\beta^2)^2 + 4\beta X^2\{[1-X]d_M^2 + 2[1-X](\hat w-w)d_M + (\hat w-w)^2\}},\qquad \hat e_I = \frac{4X}{a(4-\beta^2)^2}\,\Phi .$$
--   $e^*_{11}(e_{22})$ is the right-hand side of (OA-9) (p. ec8), and the thresholds are
--   $$K^M_u = \Pi^b_1(e^*_I,0;e^*_I,0)\big|_{K=0} - \Pi^b_1(0,0;e^*_I,0),\quad K^L_u = \Pi^b_1(e^*_{11}(\hat e_I),0;\hat e_I,0)\big|_{K=0} - \Pi^b_1(0,0;\hat e_I,0),\quad K^H_u = \Pi^b_2(\hat e_I,0;0,0)\big|_{K=0} - \Pi^b_2(0,0;0,0),$$
--   as in (OA-10), (OA-12), (OA-13).
--
--   These objects carry the statements of the competition mission (Lemma 1 links the stage-2 closed form to the Cournot game, and Proposition 2 describes $\mathrm{EqSet}(K)$); the joint-auditing mission (Proposition 3) builds its coalition model on the same parameters, damage probabilities, audit cost and $\hat e_I$.
--
--   **Formalization Note** The stage-2 profit is defined by the closed form above for all $(n_1,n_2)$, so it is symmetric by construction; Lemma 1 (a milestone) states that it is the game's unique equilibrium. $\Pi^b_1$ is the 8-term expectation; the grouped display of OA.2 is a milestone. Efforts are kept in $[0,1]$ by the strategy set, so $\lambda_I, \lambda_C \in [0,1]$. $e^*_I$, $\hat e_I$, $e^*_{11}(\cdot)$ and the three thresholds are explicit formulas, never defined as maximizers. This module is shared by both missions of the series: the joint-auditing mission (namespace `SupplierAudit.Joint`) imports its parameters `Params`, the damage probabilities $\lambda_I, \lambda_C$, the audit cost and $\hat e_I$ instead of restating them.
-- source:
--   Chen, Qi, Dawande, Supplier Centrality and Auditing Priority in Socially-Responsible Supply Chains, accepted manuscript (SSRN 2889889), Sec. 3, pp. 6–8; Lemma 1, p. 9; Sec. 4, p. 10 (tie-breaking rule); eqs. (1)–(2), p. 11; OA.2, p. ec1 (PDF 29); (OA-9), (OA-10), p. ec8 (PDF 36); (OA-12), (OA-13), p. ec9 (PDF 37)

import Mathlib
import Definitions.Def_SupplierAudit_Competition_CournotDuopoly

namespace SupplierAudit.Competition

open Set

/-- Model parameters of Chen, Qi, Dawande (Sec. 3, pp. 6–8), with the standing assumptions of the
model as fields: `β ∈ [0,1]`, `w ≤ ŵ`, `d_M > 0`, `e ∈ (0,1)`, `r ∈ (0,1]`, `a > 0`, and the three
conditions of p. 8 that make the buyers order positive amounts.
`α` is the MWTP, `β` the substitution parameter, `w`/`wh` the wholesale prices `w`/`ŵ`, `dM` the
MWTP damage `d_M`, `e` the suppliers' social-responsibility effort, `r` the probability of public
discovery and `a` the coefficient of the variable auditing cost `(a/2)e²`. The fixed auditing cost
`K` is not a field: it is a separate argument everywhere. -/
structure Params where
  α : ℝ
  β : ℝ
  w : ℝ
  wh : ℝ
  dM : ℝ
  e : ℝ
  r : ℝ
  a : ℝ
  hβ0 : 0 ≤ β
  hβ1 : β ≤ 1
  hw : w ≤ wh
  hdM : 0 < dM
  he0 : 0 < e
  he1 : e < 1
  hr0 : 0 < r
  hr1 : r ≤ 1
  ha : 0 < a
  hpos1 : 2 * (1 - β) * w + 2 * wh < (2 - β) * α - 2 * dM
  hpos2 : (4 - β) * wh - β * w < (2 - β) * (α - dM)
  hpos3 : 2 * wh < α - dM

variable (P : Params)

/-! ### Stage 2 (Sec. 3, p. 8; Lemma 1, p. 9) -/

/-- Demand intercept of a buyer with `n` offending suppliers: `α` if `n = 0`, and `α − d_M` if
`n ≥ 1` (the MWTP damage `d_M` is incurred once, however many suppliers offend). -/
noncomputable def intercept (n : ℕ) : ℝ := if n = 0 then P.α else P.α - P.dM

/-- Unit input cost of a buyer with `n ∈ {0,1,2}` offending suppliers: each of his two suppliers is
paid `w` per unit if not discovered as non-compliant and `ŵ` otherwise, so the cost is
`(2 − n)w + nŵ`. -/
noncomputable def unitCost (n : ℕ) : ℝ := (2 - (n : ℝ)) * P.w + (n : ℝ) * P.wh

/-- Buyer `B₁`'s stage-2 equilibrium quantity when `B₁` has `n₁` and `B₂` has `n₂` offending
suppliers, in closed form: `q*₁ = (2(A₁ − c₁) − β(A₂ − c₂))/(4 − β²)` with `Aᵢ = intercept nᵢ`,
`cᵢ = unitCost nᵢ`. Buyer `B₂`'s quantity is `stage2q P n₂ n₁`. -/
noncomputable def stage2q (n₁ n₂ : ℕ) : ℝ :=
  (2 * (intercept P n₁ - unitCost P n₁) - P.β * (intercept P n₂ - unitCost P n₂)) / (4 - P.β ^ 2)

/-- Buyer `B₁`'s stage-2 (ex post) equilibrium profit `π^b_1 = (q*₁)²`; buyer `B₂`'s is
`stage2Profit P n₂ n₁`. -/
noncomputable def stage2Profit (n₁ n₂ : ℕ) : ℝ := (stage2q P n₁ n₂) ^ 2

/-! ### Stage 1 (Sec. 3, pp. 6–7; OA.2, p. ec1) -/

/-- `λ_I(x) = r(1−e)(1−x)`: probability that an independent supplier audited with effort `x`
causes MWTP damage to its buyer. -/
noncomputable def lamI (x : ℝ) : ℝ := P.r * (1 - P.e) * (1 - x)

/-- `λ_C(x₁, x₂) = r(1−e)(1−x₁)(1−x₂)`: probability that the common supplier, audited with efforts
`x₁` by `B₁` and `x₂` by `B₂`, causes MWTP damage to both buyers. -/
noncomputable def lamC (x₁ x₂ : ℝ) : ℝ := P.r * (1 - P.e) * (1 - x₁) * (1 - x₂)

/-- Cost of auditing one supplier with effort `x`: `K·1{x>0} + (a/2)x²` (p. 7). Effort `0` means
that the supplier is not audited, which costs nothing. -/
noncomputable def auditCost (K x : ℝ) : ℝ := (if 0 < x then K else 0) + P.a / 2 * x ^ 2

/-- `Π^b_1(e₁₁, e₁c; e₂₂, e₂c)`: buyer `B₁`'s ex ante expected profit. The suppliers `S₁`, `S_c`,
`S₂` cause damage independently with probabilities `λ_I(e₁₁)`, `λ_C(e₁c, e₂c)`, `λ_I(e₂₂)`; in the
outcome `(b₁, b_c, b₂)` buyer `B₁` has `n₁ = b₁ + b_c` and `B₂` has `n₂ = b₂ + b_c` offending
suppliers, and earns `stage2Profit P n₁ n₂`. The profit is the expectation over the 8 outcomes
minus `B₁`'s auditing costs on `S₁` and on `S_c`. -/
noncomputable def expProfit₁ (K e11 e1c e22 e2c : ℝ) : ℝ :=
  (∑ b : Bool × Bool × Bool,
    (if b.1 then lamI P e11 else 1 - lamI P e11) *
    (if b.2.1 then lamC P e1c e2c else 1 - lamC P e1c e2c) *
    (if b.2.2 then lamI P e22 else 1 - lamI P e22) *
    stage2Profit P (b.1.toNat + b.2.1.toNat) (b.2.2.toNat + b.2.1.toNat))
  - auditCost P K e11 - auditCost P K e1c

/-- `Π^b_2(e₂₂, e₂c; e₁₁, e₁c)`: buyer `B₂`'s expected profit, in the paper's argument order (own
efforts first). The model is symmetric, so it is `Π^b_1` with the roles of the buyers exchanged. -/
noncomputable def expProfit₂ (K e22 e2c e11 e1c : ℝ) : ℝ := expProfit₁ P K e22 e2c e11 e1c

/-- A buyer's strategy `(x, y)`: effort `x ∈ [0,1]` on his independent supplier and `y ∈ [0,1]` on
the common supplier; a buyer audits at most one of his two suppliers (p. 7), so `x·y = 0`.
`(0, 0)` is no-audit. -/
def StrategySet : Set (ℝ × ℝ) :=
  {s | s.1 ∈ Icc (0 : ℝ) 1 ∧ s.2 ∈ Icc (0 : ℝ) 1 ∧ s.1 * s.2 = 0}

/-- Equilibrium of the stage-1 auditing game with the tie-breaking rule of p. 10. The profile is
`s₁ = (e₁₁, e₁c)`, `s₂ = (e₂₂, e₂c)`. Both are strategies; each maximizes its buyer's expected
profit over all strategies given the other's; and a buyer who audits strictly prefers it to not
auditing ("when a buyer is indifferent between auditing a supplier and no-audit, we assume that the
buyer chooses no-audit"). -/
def IsEquilibrium (K : ℝ) (s₁ s₂ : ℝ × ℝ) : Prop :=
  s₁ ∈ StrategySet ∧ s₂ ∈ StrategySet ∧
  (∀ t ∈ StrategySet, expProfit₁ P K t.1 t.2 s₂.1 s₂.2 ≤ expProfit₁ P K s₁.1 s₁.2 s₂.1 s₂.2) ∧
  (∀ t ∈ StrategySet, expProfit₂ P K t.1 t.2 s₁.1 s₁.2 ≤ expProfit₂ P K s₂.1 s₂.2 s₁.1 s₁.2) ∧
  (s₁ ≠ (0, 0) → expProfit₁ P K 0 0 s₂.1 s₂.2 < expProfit₁ P K s₁.1 s₁.2 s₂.1 s₂.2) ∧
  (s₂ ≠ (0, 0) → expProfit₂ P K 0 0 s₁.1 s₁.2 < expProfit₂ P K s₂.1 s₂.2 s₁.1 s₁.2)

/-- The set of equilibrium profiles `(s₁, s₂)` at fixed auditing cost `K`. -/
def EqSet (K : ℝ) : Set ((ℝ × ℝ) × (ℝ × ℝ)) := {p | IsEquilibrium P K p.1 p.2}

/-! ### Efforts and thresholds (eqs. (1)–(2), p. 11; (OA-9)–(OA-13), pp. ec8–ec9) -/

/-- `e*_I`, eq. (1), p. 11, verbatim (with `X = r(1−e)`). -/
noncomputable def eStarI : ℝ :=
  let X := P.r * (1 - P.e)
  4 * X *
    (P.α * (2 - P.β) * ((1 - X) * P.dM + P.wh - P.w)
      - P.dM * P.w * (1 - 2 * X) * (2 - P.β * (2 - X))
      - P.dM * P.wh * (2 - P.β * X * (3 - 2 * X))
      - P.dM ^ 2 * (1 - X) * (1 - P.β * X)
      - (P.wh - P.w) * (P.w * (3 - 2 * P.β - 2 * (1 - P.β) * X) + P.wh * (1 + 2 * (1 - P.β) * X)))
  / (P.a * (4 - P.β ^ 2) ^ 2 + 4 * P.β * X ^ 2 *
      ((1 - X) * P.dM ^ 2 + 2 * (1 - X) * (P.wh - P.w) * P.dM + (P.wh - P.w) ^ 2))

/-- `ê_I`, eq. (2), p. 11, verbatim (with `X = r(1−e)`). -/
noncomputable def eHatI : ℝ :=
  let X := P.r * (1 - P.e)
  4 * X / (P.a * (4 - P.β ^ 2) ^ 2) *
    (P.α * (2 - P.β) * ((1 - X) * P.dM + P.wh - P.w)
      - P.dM * P.w * (1 - 2 * X) * (2 - P.β * (2 - X))
      - P.dM * P.wh * (2 - P.β * X * (3 - 2 * X))
      - P.dM ^ 2 * (1 - X) * (1 - P.β * X)
      - (P.wh - P.w) * (P.w * (3 - 2 * P.β - 2 * (1 - P.β) * X) + P.wh * (1 + 2 * (1 - P.β) * X)))

/-- `e*_11(e₂₂)`, the right-hand side of (OA-9), p. ec8: buyer `B₁`'s best-response effort on `S₁`
when `B₂` audits `S₂` with effort `e₂₂` (`X = r(1−e)`; the seven squares are Lemma 1's profits). -/
noncomputable def bestResp (e22 : ℝ) : ℝ :=
  let X := P.r * (1 - P.e)
  let t00 := ((P.α - 2 * P.w) / (2 + P.β)) ^ 2
  let t01 := (P.α / (2 + P.β) + (P.β * P.dM - (4 - P.β) * P.w + P.β * P.wh) / (4 - P.β ^ 2)) ^ 2
  let t10 := (P.α / (2 + P.β) - (2 * P.dM + 2 * (1 - P.β) * P.w + 2 * P.wh) / (4 - P.β ^ 2)) ^ 2
  let t11 := ((P.α - P.dM - P.w - P.wh) / (2 + P.β)) ^ 2
  let t12 := ((P.α - P.dM) / (2 + P.β) - (2 * P.w + 2 * (1 - P.β) * P.wh) / (4 - P.β ^ 2)) ^ 2
  let t21 := ((P.α - P.dM) / (2 + P.β) - ((4 - P.β) * P.wh - P.β * P.w) / (4 - P.β ^ 2)) ^ 2
  let t22 := ((P.α - P.dM - 2 * P.wh) / (2 + P.β)) ^ 2
  X * (1 - X) * (1 - X * (1 - e22)) / P.a * (t00 - t10)
    + X * (1 - X) * (X * (1 - e22)) / P.a * (t01 - t11)
    + X ^ 2 * (1 - X * (1 - e22)) / P.a * (t11 - t21)
    + X ^ 2 * (X * (1 - e22)) / P.a * (t12 - t22)

/-- `K^M_u`, (OA-10), p. ec8: `Π^b_1(e*_I, 0; e*_I, 0)|_{K=0} − Π^b_1(0, 0; e*_I, 0)`. -/
noncomputable def KMu : ℝ :=
  expProfit₁ P 0 (eStarI P) 0 (eStarI P) 0 - expProfit₁ P 0 0 0 (eStarI P) 0

/-- `K^L_u`, (OA-12), p. ec9: `Π^b_1(e*_11(ê_I), 0; ê_I, 0)|_{K=0} − Π^b_1(0, 0; ê_I, 0)`. -/
noncomputable def KLu : ℝ :=
  expProfit₁ P 0 (bestResp P (eHatI P)) 0 (eHatI P) 0 - expProfit₁ P 0 0 0 (eHatI P) 0

/-- `K^H_u`, (OA-13), p. ec9: `Π^b_2(ê_I, 0; 0, 0)|_{K=0} − Π^b_2(0, 0; 0, 0)`. -/
noncomputable def KHu : ℝ :=
  expProfit₂ P 0 (eHatI P) 0 0 0 - expProfit₂ P 0 0 0 0 0

end SupplierAudit.Competition


