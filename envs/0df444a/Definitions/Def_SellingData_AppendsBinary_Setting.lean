-- Prove2me | Definitions.Def_SellingData_AppendsBinary_Setting
-- name    : SellingData_AppendsBinary_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-14T03:09:01.666991+00:00
-- url     : https://prove2.me/theorems/a401c98a-0845-43aa-85f7-a702e799d027
-- title:
--   §2–§3.2, pp. 5–13 — binary value, signal (1)–(2), selling cost k, two cost types, payoffs (5), outside option max{û − c_i, 0}, data-append problem (6), benchmark (4), objective (8)
-- statement:
--   This module fixes the objects of Guo's model of a monopoly data seller who sells **data appends** to marketers with privately known targeting costs.
--
--   **Value and prior.** A marketer can take a binary action at cost $c>0$; the action yields a value $u\in\{\underline u,\bar u\}$ with $\underline u<\bar u$, where $u=\bar u$ with prior probability $\varphi\in(0,1)$. The prior mean is
--   $$\hat u=\varphi\bar u+(1-\varphi)\underline u .$$
--
--   **Signal and posteriors.** The seller's data produce a signal $w\in\{w_h,w_l\}$ with $\Pr(w_h\mid\bar u)=\Pr(w_l\mid\underline u)=\alpha$, where the informativeness $\alpha$ ranges over $[\underline\alpha,\bar\alpha]\subset(1/2,1)$. The signal probabilities and posteriors are, as in (1) and (2),
--   $$\sigma_h(\alpha)=\varphi\alpha+(1-\varphi)(1-\alpha),\qquad \sigma_l(\alpha)=\varphi(1-\alpha)+(1-\varphi)\alpha,$$
--   $$\varphi_h(\alpha)=\frac{\varphi\alpha}{\varphi\alpha+(1-\varphi)(1-\alpha)},\qquad \varphi_l(\alpha)=\frac{\varphi(1-\alpha)}{\varphi(1-\alpha)+(1-\varphi)\alpha},$$
--   and the posterior means are $v_h(\alpha)=\varphi_h(\alpha)\bar u+[1-\varphi_h(\alpha)]\underline u$ and $v_l(\alpha)=\varphi_l(\alpha)\bar u+[1-\varphi_l(\alpha)]\underline u$.
--
--   **Types and costs.** There are two cost types $c_H>c_L>0$, with $\theta_H=\theta\in(0,1)$ and $\theta_L=1-\theta$. The standing assumption $v_l(\underline\alpha)<c_i<v_h(\underline\alpha)$ holds for both costs. The seller's selling cost $k$ satisfies $k(\underline\alpha)=0$ and is increasing on $[\underline\alpha,\bar\alpha]$.
--
--   **Menus and payoffs.** A menu consists of two plans $(T_H,\alpha_H)$ and $(T_L,\alpha_L)$. Type $i$'s payoff from plan $j$ is (5),
--   $$U_{ij}=-T_j+\sigma_h(\alpha_j)[v_h(\alpha_j)-c_i],$$
--   and its outside option with data appends is $U_{i0}=\max\{\hat u-c_i,0\}$. A menu is **feasible** if $T_j\ge 0$ and $\alpha_j\in[\underline\alpha,\bar\alpha]$ for both plans, $U_{ii}\ge U_{i0}$ for both types ($IR_i$), and $U_{ii}\ge U_{ii'}$ for $i\ne i'$ ($IC_{i,i'}$). Its profit is $\Pi=\sum_{i=H,L}\theta_i[T_i-k(\alpha_i)]$, as in (6), and it is **optimal** if it is feasible and no feasible menu earns more.
--
--   **Benchmark.** With observable cost $c_i$ the seller's profit is (4), $\Pi_i=\theta_i[\sigma_h(\alpha)[v_h(\alpha)-c_i]-k(\alpha)]$; an **efficient** informativeness $\alpha_i^e$ is any maximizer of $\Pi_i$ over $[\underline\alpha,\bar\alpha]$.
--
--   **Reduced problem.** The objective of (8) is
--   $$\theta\big[\sigma_h(\alpha_H)[v_h(\alpha_H)-c_H]-\sigma_h(\alpha_L)(c_L-c_H)-k(\alpha_H)\big]+(1-\theta)\big[\sigma_h(\alpha_L)[v_h(\alpha_L)-c_L]-k(\alpha_L)\big]-\hat u+c_L ,$$
--   with maximizers taken over $[\underline\alpha,\bar\alpha]^2$. The binding menu at $(\alpha_H,\alpha_L)$ sets $T_L=\sigma_h(\alpha_L)[v_h(\alpha_L)-c_L]-U_{L0}$ (binding $IR_L$) and $T_H=T_L+\sigma_h(\alpha_H)[v_h(\alpha_H)-c_H]-\sigma_h(\alpha_L)[v_h(\alpha_L)-c_H]$ (binding $IC_{H,L}$).
--
--   These objects are shared by every statement of the mission.
--
--   **Formalization Note** The two types are an inductive type with constructors `H` and `L`. The posteriors are defined with the divisions of (2), not through simplified products. "The" efficient and optimal informativeness are not assumed unique: efficiency and optimality are predicates on maximizers. The optimal menu is defined directly from the data-append problem (6), never through (8). The condition $c\in(\underline u,\bar u)$ of p. 5 is implied by the standing assumption and is not stated separately. "Increasing" for $k$ is read as weakly increasing on $[\underline\alpha,\bar\alpha]$.
-- source:
--   Guo, Selling Data to Marketers, author's manuscript (Management Science, doi:10.1287/mnsc.2023.01350), pp. 5–13, §2, §3.1, §3.2, (1)–(6), (8), outside option U_i0 = max{û − c_i, 0} p. 13

import Mathlib
import Definitions.Def_SellingData_ListsBinary_Setting

noncomputable section

namespace SellingData.AppendsBinary

/-- The posterior mean after the high signal, `v_h(α) = φ_h(α)ū + [1 − φ_h(α)]u̲`. -/
def vHigh (uLo uHi φ α : ℝ) : ℝ := SellingData.ListsBinary.phiH φ α * uHi + (1 - SellingData.ListsBinary.phiH φ α) * uLo

/-- The posterior mean after the low signal, `v_l(α) = φ_l(α)ū + [1 − φ_l(α)]u̲`. -/
def vLow (uLo uHi φ α : ℝ) : ℝ := SellingData.ListsBinary.phiL φ α * uHi + (1 - SellingData.ListsBinary.phiL φ α) * uLo

instance : Fintype SellingData.ListsBinary.CostType :=
  ⟨{SellingData.ListsBinary.CostType.H, SellingData.ListsBinary.CostType.L}, fun x => by cases x <;> simp⟩

/-- The base model of §2–§3 (pp. 5–11) with its standing assumptions:
values `u ∈ {u̲, ū}` with `Pr(ū) = φ ∈ (0,1)`; signal accuracy `α ∈ [α̲, ᾱ] ⊂ (1/2, 1)`;
type probabilities `θ_H = θ ∈ (0,1)`, `θ_L = 1 − θ`; costs `c_H > c_L > 0`;
selling cost `k` with `k(α̲) = 0`, increasing on `[α̲, ᾱ]`; and the standing assumption
`v_l(α̲) < c < v_h(α̲)` for both costs (p. 7). -/
structure Model where
  uLo : ℝ
  uHi : ℝ
  φ : ℝ
  aLo : ℝ
  aHi : ℝ
  θ : ℝ
  cL : ℝ
  cH : ℝ
  k : ℝ → ℝ
  uLo_lt_uHi : uLo < uHi
  φ_pos : 0 < φ
  φ_lt_one : φ < 1
  half_lt_aLo : 1 / 2 < aLo
  aLo_lt_aHi : aLo < aHi
  aHi_lt_one : aHi < 1
  θ_pos : 0 < θ
  θ_lt_one : θ < 1
  cL_pos : 0 < cL
  cL_lt_cH : cL < cH
  k_aLo : k aLo = 0
  k_mono : MonotoneOn k (Set.Icc aLo aHi)
  standing_cL : vLow uLo uHi φ aLo < cL ∧ cL < vHigh uLo uHi φ aLo
  standing_cH : vLow uLo uHi φ aLo < cH ∧ cH < vHigh uLo uHi φ aLo

/-- A menu of two service plans `(T_H, α_H)` and `(T_L, α_L)`. -/
structure Menu where
  TH : ℝ
  αH : ℝ
  TL : ℝ
  αL : ℝ

namespace Menu

/-- The fixed payment `T_j` of the plan intended for type `j`. -/
def T (m : Menu) : SellingData.ListsBinary.CostType → ℝ
  | SellingData.ListsBinary.CostType.H => m.TH
  | SellingData.ListsBinary.CostType.L => m.TL

/-- The informativeness `α_j` of the plan intended for type `j`. -/
def α (m : Menu) : SellingData.ListsBinary.CostType → ℝ
  | SellingData.ListsBinary.CostType.H => m.αH
  | SellingData.ListsBinary.CostType.L => m.αL

end Menu

namespace Model

variable (M : Model)

/-- `σ_h(α)`, (1). -/
def σh (α : ℝ) : ℝ := SellingData.ListsBinary.sigmaH M.φ α

/-- `σ_l(α)`, (1). -/
def σl (α : ℝ) : ℝ := SellingData.ListsBinary.sigmaL M.φ α

/-- `v_h(α)`. -/
def vh (α : ℝ) : ℝ := vHigh M.uLo M.uHi M.φ α

/-- `v_l(α)`. -/
def vl (α : ℝ) : ℝ := vLow M.uLo M.uHi M.φ α

/-- The prior mean `û = φū + (1 − φ)u̲` (p. 5). -/
def uHat : ℝ := M.φ * M.uHi + (1 - M.φ) * M.uLo

/-- The targeting cost `c_i` of type `i`. -/
def c : SellingData.ListsBinary.CostType → ℝ
  | SellingData.ListsBinary.CostType.H => M.cH
  | SellingData.ListsBinary.CostType.L => M.cL

/-- The type probability `θ_i`: `θ_H = θ`, `θ_L = 1 − θ`. -/
def θi : SellingData.ListsBinary.CostType → ℝ
  | SellingData.ListsBinary.CostType.H => M.θ
  | SellingData.ListsBinary.CostType.L => 1 - M.θ

/-- A marketer's expected payoff from information of accuracy `α` at cost `c`, before the payment:
`σ_h(α)[v_h(α) − c]`, as in (3) and (5). -/
def payoff (α c : ℝ) : ℝ := M.σh α * (M.vh α - c)

/-- The data-append outside option `U_i0 = max{û − c_i, 0}` at cost `c` (pp. 12–13). -/
def outside (c : ℝ) : ℝ := max (M.uHat - c) 0

/-- `U_ij = −T_j + σ_h(α_j)[v_h(α_j) − c_i]`, (5): type `i`'s payoff from plan `j` of menu `m`. -/
def U (m : Menu) (i j : SellingData.ListsBinary.CostType) : ℝ := -(m.T j) + M.payoff (m.α j) (M.c i)

/-- Feasibility in the data-append screening problem: (6) with `IR_i` replaced by
`U_ii ≥ U_i0` (p. 13): `T_j ≥ 0`, `α_j ∈ [α̲, ᾱ]`, `IR_i` and `IC_{i,i'}`. -/
def Feasible (m : Menu) : Prop :=
  (∀ j : SellingData.ListsBinary.CostType, 0 ≤ m.T j ∧ m.α j ∈ Set.Icc M.aLo M.aHi) ∧
  (∀ i : SellingData.ListsBinary.CostType, M.outside (M.c i) ≤ M.U m i i) ∧
  (∀ i i' : SellingData.ListsBinary.CostType, i ≠ i' → M.U m i i' ≤ M.U m i i)

/-- The seller's expected profit `Π = Σ_{i=H,L} θ_i [T_i − k(α_i)]`, (6). -/
def profit (m : Menu) : ℝ := ∑ i : SellingData.ListsBinary.CostType, M.θi i * (m.T i - M.k (m.α i))

/-- An optimal menu of the data-append screening problem: feasible, and no feasible menu earns
more. -/
def IsOptimalMenu (m : Menu) : Prop :=
  M.Feasible m ∧ ∀ m' : Menu, M.Feasible m' → M.profit m' ≤ M.profit m

/-- The benchmark profit (4) with observable cost: `Π_i = θ_i[σ_h(α)[v_h(α) − c_i] − k(α)]`. -/
def benchProfit (i : SellingData.ListsBinary.CostType) (α : ℝ) : ℝ :=
  M.θi i * (M.σh α * (M.vh α - M.c i) - M.k α)

/-- `a` is an efficient informativeness `α^e_i` for type `i`: a maximizer of (4) over `[α̲, ᾱ]`. -/
def IsEfficient (i : SellingData.ListsBinary.CostType) (a : ℝ) : Prop :=
  a ∈ Set.Icc M.aLo M.aHi ∧ ∀ a' ∈ Set.Icc M.aLo M.aHi, M.benchProfit i a' ≤ M.benchProfit i a

/-- The objective of the simplified problem (8), term by term. -/
def reducedProfit (αH αL : ℝ) : ℝ :=
  M.θ * (M.σh αH * (M.vh αH - M.cH) - M.σh αL * (M.cL - M.cH) - M.k αH)
    + (1 - M.θ) * (M.σh αL * (M.vh αL - M.cL) - M.k αL) - M.uHat + M.cL

/-- `(αH, αL)` maximizes (8) over `[α̲, ᾱ] × [α̲, ᾱ]`. -/
def IsReducedMax (αH αL : ℝ) : Prop :=
  αH ∈ Set.Icc M.aLo M.aHi ∧ αL ∈ Set.Icc M.aLo M.aHi ∧
    ∀ a ∈ Set.Icc M.aLo M.aHi, ∀ b ∈ Set.Icc M.aLo M.aHi,
      M.reducedProfit a b ≤ M.reducedProfit αH αL

/-- The menu with `IR_L` and `IC_{H,L}` binding at informativeness `(αH, αL)`:
`T_L = σ_h(α_L)[v_h(α_L) − c_L] − U_L0` and `T_H = T_L + σ_h(α_H)[v_h(α_H) − c_H] − σ_h(α_L)[v_h(α_L) − c_H]`. -/
def bindingMenu (αH αL : ℝ) : Menu where
  TL := M.payoff αL M.cL - M.outside M.cL
  αL := αL
  TH := (M.payoff αL M.cL - M.outside M.cL) + M.payoff αH M.cH - M.payoff αL M.cH
  αH := αH

end Model

end SellingData.AppendsBinary

end


