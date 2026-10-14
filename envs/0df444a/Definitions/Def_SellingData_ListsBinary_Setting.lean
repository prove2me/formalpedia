-- Prove2me | Definitions.Def_SellingData_ListsBinary_Setting
-- name    : SellingData_ListsBinary_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-14T01:20:18.285793+00:00
-- url     : https://prove2.me/theorems/a0e50323-d5ed-4b34-8242-514e1ecca41c
-- title:
--   §2–§3.1, pp. 5–11 — binary value, signal (1)–(2), selling cost k, two cost types, menus, payoffs (5), problem (6) with IR/IC, benchmark (4), objective (7)
-- statement:
--   This file sets up the base model of Guo's *Selling Data to Marketers* for **marketing lists**.
--
--   **Information environment.** A marketer's value $u$ of taking an action (say, targeting a consumer) is $\bar u$ with prior probability $\phi\in(0,1)$ and $\underline u$ with probability $1-\phi$, where $\underline u<\bar u$. The data seller sells a binary signal $w\in\{w_h,w_l\}$ with $\Pr(w_h\mid\bar u)=\Pr(w_l\mid\underline u)=\alpha$, where the informativeness $\alpha$ ranges over an interval $[\underline\alpha,\bar\alpha]\subset(1/2,1)$. The signal probabilities and posteriors are, exactly as in (1)–(2),
--   $$\sigma_h(\alpha)=\phi\alpha+(1-\phi)(1-\alpha),\qquad \sigma_l(\alpha)=\phi(1-\alpha)+(1-\phi)\alpha,$$
--   $$\phi_h(\alpha)=\frac{\phi\alpha}{\phi\alpha+(1-\phi)(1-\alpha)},\qquad \phi_l(\alpha)=\frac{\phi(1-\alpha)}{\phi(1-\alpha)+(1-\phi)\alpha},$$
--   and the posterior means are $v_h(\alpha)=\phi_h(\alpha)\bar u+[1-\phi_h(\alpha)]\underline u$ and $v_l(\alpha)=\phi_l(\alpha)\bar u+[1-\phi_l(\alpha)]\underline u$. Serving a marketer with informativeness $\alpha$ costs the seller $k(\alpha)$, where $k(\underline\alpha)=0$ and $k$ is increasing on $[\underline\alpha,\bar\alpha]$. A targeting cost $c$ is **admissible** if $v_l(\underline\alpha)<c<v_h(\underline\alpha)$ (the standing assumption of p. 7).
--
--   **Benchmark.** For a weight $\theta_i$ and cost $c$, the benchmark objective (4) is
--   $$\Pi_i(\alpha)=\theta_i\big[\sigma_h(\alpha)[v_h(\alpha)-c]-k(\alpha)\big],$$
--   and $a$ is **efficient** if it maximizes $\Pi_i$ over $[\underline\alpha,\bar\alpha]$.
--
--   **Screening.** There are two cost types $H$ and $L$ with costs $c_H>c_L>0$, both admissible, and the type is $H$ with probability $\theta\in(0,1)$; write $\theta_H=\theta$, $\theta_L=1-\theta$. A menu consists of plans $(T_H,\alpha_H)$ and $(T_L,\alpha_L)$. The payoff (5) of type $i$ choosing plan $j$ is $U_{ij}=-T_j+\sigma_h(\alpha_j)[v_h(\alpha_j)-c_i]$. A menu is **feasible** if $T_H,T_L\ge0$, $\alpha_H,\alpha_L\in[\underline\alpha,\bar\alpha]$, $U_{ii}\ge0$ for $i=H,L$ (IR) and $U_{ii}\ge U_{ii'}$ for $i\ne i'$ (IC); it is **optimal** if it is feasible and maximizes
--   $$\Pi=\sum_{i=H,L}\theta_i\,[T_i-k(\alpha_i)]$$
--   among feasible menus, as in (6). Finally, the objective of the reduced problem (7) is
--   $$\theta\big[\sigma_h(\alpha_H)[v_h(\alpha_H)-c_H]-k(\alpha_H)\big]+(1-\theta)\big[\sigma_h(\alpha_L)[v_h(\alpha_L)-c_L]-\sigma_h(\alpha_H)(c_H-c_L)-k(\alpha_L)\big],$$
--   and a pair $(\alpha_H,\alpha_L)$ is a maximizer of (7) if it maximizes this expression over $[\underline\alpha,\bar\alpha]^2$.
--
--   These objects are shared by every statement of the mission: Propositions 1 and 2, the reduction (7) and the derivative computations of the Appendix.
--
--   **Formalization Note** $\phi_h,\phi_l$ are defined with the divisions printed in (2); the identity $\sigma_h(\alpha)v_h(\alpha)=\phi\alpha\bar u+(1-\phi)(1-\alpha)\underline u$ is left to the theorems. Efficiency and optimality are defined as membership in the set of maximizers, never as "the" maximizer, since $k$ need not be convex. The standing assumptions $\underline u<\bar u$ (implicit in $c\in(\underline u,\bar u)$) and admissibility of both $c_H$ and $c_L$ are fields of the structures; $c\in(\underline u,\bar u)$ itself follows from admissibility and is not added. "Increasing" for $k$ is read weakly (`MonotoneOn`). The sum in (6) is written out over the two types.
-- source:
--   Guo, Selling Data to Marketers, author's manuscript (Management Science, doi:10.1287/mnsc.2023.01350), pp. 5–11, §2, §3.1, (1)–(7)

import Mathlib

namespace SellingData.ListsBinary

/-! Guo, *Selling Data to Marketers* (author's manuscript), §2 and §3.1, pp. 5–11:
the binary-value model, the binary signal (1)–(2), the selling cost `k`, the two cost types,
the benchmark (4), and the screening problem (5)–(6) for marketing lists, together with the
right-hand side of the reduced problem (7). -/

/-- (1): `σ_h(α) = Pr(w_h) = φα + (1 - φ)(1 - α)`. -/
def sigmaH (phi α : ℝ) : ℝ := phi * α + (1 - phi) * (1 - α)

/-- (1): `σ_l(α) = Pr(w_l) = φ(1 - α) + (1 - φ)α`. -/
def sigmaL (phi α : ℝ) : ℝ := phi * (1 - α) + (1 - phi) * α

/-- (2): `φ_h(α) = Pr(ū | w_h) = φα / (φα + (1 - φ)(1 - α))`. -/
noncomputable def phiH (phi α : ℝ) : ℝ := phi * α / (phi * α + (1 - phi) * (1 - α))

/-- (2): `φ_l(α) = Pr(ū | w_l) = φ(1 - α) / (φ(1 - α) + (1 - φ)α)`. -/
noncomputable def phiL (phi α : ℝ) : ℝ := phi * (1 - α) / (phi * (1 - α) + (1 - phi) * α)

/-- Posterior mean after `w_h`: `v_h(α) = φ_h(α) ū + [1 - φ_h(α)] u̲`. -/
noncomputable def vH (uLo uHi phi α : ℝ) : ℝ := phiH phi α * uHi + (1 - phiH phi α) * uLo

/-- Posterior mean after `w_l`: `v_l(α) = φ_l(α) ū + [1 - φ_l(α)] u̲`. -/
noncomputable def vL (uLo uHi phi α : ℝ) : ℝ := phiL phi α * uHi + (1 - phiL phi α) * uLo

/-- The information environment of §2 (pp. 5–7): values `u̲ < ū`, prior `φ ∈ (0,1)`,
informativeness interval `[α̲, ᾱ] ⊂ (1/2, 1)`, and selling cost `k` with `k(α̲) = 0`,
increasing on `[α̲, ᾱ]`. -/
structure Model where
  /-- the low value `u̲` -/
  uLo : ℝ
  /-- the high value `ū` -/
  uHi : ℝ
  /-- the prior probability `φ` of `ū` -/
  phi : ℝ
  /-- the least informativeness `α̲` -/
  aLo : ℝ
  /-- the greatest informativeness `ᾱ` -/
  aHi : ℝ
  /-- the (marginal) selling cost `k(α)` -/
  k : ℝ → ℝ
  uLo_lt_uHi : uLo < uHi
  phi_pos : 0 < phi
  phi_lt_one : phi < 1
  half_lt_aLo : 1 / 2 < aLo
  aLo_lt_aHi : aLo < aHi
  aHi_lt_one : aHi < 1
  k_aLo : k aLo = 0
  k_mono : MonotoneOn k (Set.Icc aLo aHi)

namespace Model

variable (M : Model)

/-- The standing assumption of p. 7 for a targeting cost `c`: `v_l(α̲) < c < v_h(α̲)`. -/
def CostAdmissible (c : ℝ) : Prop :=
  vL M.uLo M.uHi M.phi M.aLo < c ∧ c < vH M.uLo M.uHi M.phi M.aLo

/-- The gross expected payoff `σ_h(α)[v_h(α) - c]` of a marketer with cost `c` who receives a
signal of informativeness `α` ((3) without the payment). -/
noncomputable def payoff (α c : ℝ) : ℝ :=
  sigmaH M.phi α * (vH M.uLo M.uHi M.phi α - c)

/-- The benchmark objective (4): `Π_i = θ_i[σ_h(α)[v_h(α) - c_i] - k(α)]`. -/
noncomputable def benchProfit (θi c α : ℝ) : ℝ :=
  θi * (sigmaH M.phi α * (vH M.uLo M.uHi M.phi α - c) - M.k α)

/-- `a` is an efficient informativeness for weight `θ_i` and cost `c`: a maximizer of (4) over
`[α̲, ᾱ]`. -/
def IsEfficient (θi c a : ℝ) : Prop :=
  a ∈ Set.Icc M.aLo M.aHi ∧
    ∀ a' ∈ Set.Icc M.aLo M.aHi, M.benchProfit θi c a' ≤ M.benchProfit θi c a

end Model

/-- The two cost types of p. 9. -/
inductive CostType
  | H
  | L
  deriving DecidableEq

/-- The screening environment of p. 9: two cost levels `c_H > c_L > 0`, both satisfying the
standing assumption of p. 7, and the probability `θ ∈ (0,1)` of type `H`. -/
structure Screening extends Model where
  /-- the probability `θ = θ_H` of the high-cost type -/
  θ : ℝ
  /-- the low targeting cost `c_L` -/
  cL : ℝ
  /-- the high targeting cost `c_H` -/
  cH : ℝ
  θ_pos : 0 < θ
  θ_lt_one : θ < 1
  cL_pos : 0 < cL
  cL_lt_cH : cL < cH
  cL_admissible : vL uLo uHi phi aLo < cL ∧ cL < vH uLo uHi phi aLo
  cH_admissible : vL uLo uHi phi aLo < cH ∧ cH < vH uLo uHi phi aLo

/-- A menu of two service plans `(T_H, α_H)` and `(T_L, α_L)`. -/
structure Menu where
  TH : ℝ
  αH : ℝ
  TL : ℝ
  αL : ℝ

namespace Menu

/-- The payment `T_j` of plan `j`. -/
def T (m : Menu) : CostType → ℝ
  | .H => m.TH
  | .L => m.TL

/-- The informativeness `α_j` of plan `j`. -/
def α (m : Menu) : CostType → ℝ
  | .H => m.αH
  | .L => m.αL

end Menu

namespace Screening

variable (S : Screening)

/-- The cost `c_i` of type `i`. -/
def cost : CostType → ℝ
  | .H => S.cH
  | .L => S.cL

/-- The probability `θ_i` of type `i`: `θ_H = θ`, `θ_L = 1 - θ`. -/
def weight : CostType → ℝ
  | .H => S.θ
  | .L => 1 - S.θ

/-- (5): `U_ij = -T_j + σ_h(α_j)[v_h(α_j) - c_i]`. -/
noncomputable def U (m : Menu) (i j : CostType) : ℝ :=
  -(m.T j) + S.payoff (m.α j) (S.cost i)

/-- The constraints of (6): `T_j ≥ 0`, `α_j ∈ [α̲, ᾱ]`, `(IR_i)` and `(IC_{i,i'})`. -/
def Feasible (m : Menu) : Prop :=
  0 ≤ m.TH ∧ 0 ≤ m.TL ∧ m.αH ∈ Set.Icc S.aLo S.aHi ∧ m.αL ∈ Set.Icc S.aLo S.aHi ∧
    (∀ i, 0 ≤ S.U m i i) ∧ (∀ i i', i ≠ i' → S.U m i i' ≤ S.U m i i)

/-- The objective (6): `Π = Σ_{i=H,L} θ_i [T_i - k(α_i)]`, the sum written out over the two
types. -/
def profit (m : Menu) : ℝ :=
  S.weight .H * (m.T .H - S.k (m.α .H)) + S.weight .L * (m.T .L - S.k (m.α .L))

/-- `m` is an optimal menu: it solves (6). -/
def IsOptimalMenu (m : Menu) : Prop :=
  S.Feasible m ∧ ∀ m', S.Feasible m' → S.profit m' ≤ S.profit m

/-- `a` is an efficient informativeness for type `i` under the benchmark (4). -/
def IsEfficientType (i : CostType) (a : ℝ) : Prop :=
  S.IsEfficient (S.weight i) (S.cost i) a

/-- The objective of (7), transcribed term by term:
`θ[σ_h(α_H)[v_h(α_H) - c_H] - k(α_H)]
  + (1 - θ)[σ_h(α_L)[v_h(α_L) - c_L] - σ_h(α_H)(c_H - c_L) - k(α_L)]`. -/
noncomputable def reducedProfit (αH αL : ℝ) : ℝ :=
  S.θ * (sigmaH S.phi αH * (vH S.uLo S.uHi S.phi αH - S.cH) - S.k αH) +
    (1 - S.θ) * (sigmaH S.phi αL * (vH S.uLo S.uHi S.phi αL - S.cL) -
      sigmaH S.phi αH * (S.cH - S.cL) - S.k αL)

/-- `(α_H, α_L)` maximizes (7) over `[α̲, ᾱ] × [α̲, ᾱ]`. -/
def IsReducedMaximizer (αH αL : ℝ) : Prop :=
  αH ∈ Set.Icc S.aLo S.aHi ∧ αL ∈ Set.Icc S.aLo S.aHi ∧
    ∀ x ∈ Set.Icc S.aLo S.aHi, ∀ y ∈ Set.Icc S.aLo S.aHi,
      S.reducedProfit x y ≤ S.reducedProfit αH αL

end Screening

end SellingData.ListsBinary


