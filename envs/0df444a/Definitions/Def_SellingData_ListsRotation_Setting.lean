-- Prove2me | Definitions.Def_SellingData_ListsRotation_Setting
-- name    : SellingData_ListsRotation_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-14T03:09:04.504728+00:00
-- url     : https://prove2.me/theorems/7015a4f2-3889-4ef2-b688-6689688f9a4c
-- title:
--   §2, §3.1, §4, pp. 7–18 — rotation-order model (9), mean property, selling cost k, two cost types, menus, payoff (13), problem (6), benchmark (12), reduced problem (14)
-- statement:
--   This file sets up the generalized information structure of Section 4 of Guo, *Selling Data to Marketers*, together with the selling cost of Section 2 and the screening problem of Section 3.1.
--
--   **Information structure.** A marketer's targeting value $u$ is unknown. The data seller supplies a signal of informativeness $\alpha$; the marketer's posterior mean $v = E[u\mid w]$ has cumulative distribution function $H(v,\alpha)$ on a bounded support $[\underline v,\bar v]$, with a strictly positive continuous density $h(v,\alpha)$, so that $H(\underline v,\alpha)=0$ and $H(\bar v,\alpha)=1$. For every $\alpha\in(0,1)$ the mean of $H(\cdot,\alpha)$ equals the prior mean $\hat u$:
--   $$\int_{\underline v}^{\bar v} v\,h(v,\alpha)\,dv=\hat u .$$
--   The partial derivative $\partial H(v,\alpha)/\partial\alpha$ exists on the support, and informativeness is ordered by the **rotation order** (9): there is a rotation point $v^+\in(\underline v,\bar v)$ with
--   $$\frac{\partial H(v,\alpha)}{\partial\alpha}>0 \text{ for } v<v^+,\qquad \frac{\partial H(v,\alpha)}{\partial\alpha}<0 \text{ for } v>v^+,\qquad \alpha\in(0,1).$$
--
--   **Seller and marketers.** The seller chooses informativeness in $[\underline\alpha,\bar\alpha]\subset(0,1)$ at a selling cost $k(\alpha)$ with $k(\underline\alpha)=0$ and $k$ increasing. A marketer has targeting cost $c_H$ (probability $\theta\in(0,1)$) or $c_L$ (probability $1-\theta$), with $c_H>c_L>0$. A marketer with cost $c$ who receives informativeness $\alpha$ targets exactly when $v>c$ and earns the gross payoff
--   $$P(\alpha,c)=\int_c^{\bar v}(v-c)\,dH(v,\alpha)=\int_c^{\bar v}(v-c)\,h(v,\alpha)\,dv .$$
--
--   **Screening problem (6) with payoff (13).** A menu consists of two plans $(T_H,\alpha_H)$ and $(T_L,\alpha_L)$ with fees $T_j\ge 0$ and $\alpha_j\in[\underline\alpha,\bar\alpha]$. A type-$i$ marketer choosing plan $j$ gets $U_{ij}=-T_j+P(\alpha_j,c_i)$. The menu is feasible if $U_{ii}\ge 0$ for both types (IR) and $U_{ii}\ge U_{ii'}$ for $i\ne i'$ (IC); the seller maximizes
--   $$\Pi=\theta\,[T_H-k(\alpha_H)]+(1-\theta)\,[T_L-k(\alpha_L)]$$
--   over feasible menus. An optimal menu is a feasible menu attaining the maximum.
--
--   **Benchmark (12).** When the cost $c_i$ is observable, the seller chooses the informativeness for type $i$ to maximize $\Pi_i=\theta_i\,[P(\alpha,c_i)-k(\alpha)]$ over $[\underline\alpha,\bar\alpha]$; a maximizer is an *efficient* informativeness $\alpha^e_i$.
--
--   **Reduced problem (14).** Its objective is
--   $$\theta\,[P(\alpha_H,c_H)-k(\alpha_H)]+(1-\theta)\,[P(\alpha_L,c_L)-P(\alpha_H,c_L)+P(\alpha_H,c_H)-k(\alpha_L)],$$
--   maximized over $[\underline\alpha,\bar\alpha]^2$. The high type's rent is $R(\alpha_H)=\int_{c_L}^{c_H}[1-H(v,\alpha_H)]\,dv$.
--
--   Finally, two regularity conditions are packaged for the statements that need them: the footnote-5 conditions on $k$ (continuity on $[\underline\alpha,\bar\alpha]$, differentiability inside, $k'(\underline\alpha)=0$ from the right, $k'(\alpha)\to+\infty$ as $\alpha\to\bar\alpha^-$) and joint continuity of $\partial H/\partial\alpha$ on $[\underline v,\bar v]\times(0,1)$.
--
--   These definitions are shared by every statement of the mission: the propositions compare optimal menus of (6) with efficient levels of (12).
--
--   **Formalization Note** The paper allows a potentially unbounded support; here the support is a bounded real interval. The density, the continuity of $H(\cdot,\alpha)$ on the closed support and the existence of $\partial H/\partial\alpha$ are the paper's "continuous and differentiable" assumptions made explicit. The costs are assumed to lie inside the support ($\underline v<c_L$, $c_H<\bar v$), which the lower limit $c_i$ of $\int_{c_i}^{\bar v}$ presupposes. The rotation order (9) is imposed on the open support only (outside it $H$ is constant). Optimal menus and efficient levels are sets of maximizers, never a chosen maximizer. The cost types are an inductive type `CostType` with constructors `H`, `L`.
-- source:
--   Guo, Selling Data to Marketers, author's manuscript (Management Science, doi:10.1287/mnsc.2023.01350), pp. 7–18: §2 (k, footnote 5, p. 7), plans and types (pp. 8–9), (6) (p. 11), §4 (9)–(10) (pp. 15–16), (11)–(14) (pp. 17–18), rent R(α_H) (p. 32)

import Mathlib
import Definitions.Def_SellingData_ListsBinary_Setting

namespace SellingData.ListsRotation

open Set Filter Topology

/-- The generalized-information-structure model of §4 (pp. 15–16), with the selling cost of §2
(p. 7) and the two cost types of p. 9.

* `[vLo, vHi]` is the support of the posterior mean `v`; `H v α` is its CDF and `h v α` its density
  under informativeness `α`; `Hα v α` is the partial derivative `∂H(v, α)/∂α`.
* `vPlus` is the rotation point `v⁺` of (9); `uHat` is the prior mean `û`.
* `[aLo, aHi] ⊂ (0, 1)` is the range of informativeness; `k` is the selling cost.
* `θ` is the probability of type `H`; `cL < cH` are the targeting costs.

The support is a bounded real interval, `H(·, α)` is continuous on it with `H(v̲, α) = 0`,
`H(v̄, α) = 1`, and has the strictly positive continuous density `h(·, α)`; `H(v, ·)` is
differentiable in `α` (these read "continuous and differentiable", p. 15–16). The costs lie inside
the support. -/
structure Model where
  vLo : ℝ
  vHi : ℝ
  vPlus : ℝ
  uHat : ℝ
  aLo : ℝ
  aHi : ℝ
  θ : ℝ
  cL : ℝ
  cH : ℝ
  k : ℝ → ℝ
  H : ℝ → ℝ → ℝ
  h : ℝ → ℝ → ℝ
  Hα : ℝ → ℝ → ℝ
  /-- bounded support `[v̲, v̄]` -/
  vLo_lt_vHi : vLo < vHi
  /-- rotation point `v⁺ ∈ (v̲, v̄)` (p. 16) -/
  vPlus_mem : vPlus ∈ Ioo vLo vHi
  /-- `[α̲, ᾱ] ⊂ (0, 1)` (p. 16) -/
  aLo_pos : 0 < aLo
  aLo_lt_aHi : aLo < aHi
  aHi_lt_one : aHi < 1
  /-- `θ ∈ (0, 1)` (p. 9) -/
  θ_pos : 0 < θ
  θ_lt_one : θ < 1
  /-- `c_H > c_L > 0` (p. 9) -/
  cL_pos : 0 < cL
  cL_lt_cH : cL < cH
  /-- the costs lie inside the support (disclosed pin) -/
  vLo_lt_cL : vLo < cL
  cH_lt_vHi : cH < vHi
  /-- `k(α̲) = 0` and `k` is increasing (p. 7) -/
  k_aLo : k aLo = 0
  k_mono : MonotoneOn k (Icc aLo aHi)
  /-- `H(·, α)` is a CDF on `[v̲, v̄]` with density `h(·, α)` (p. 16) -/
  H_vLo : ∀ α ∈ Ioo (0 : ℝ) 1, H vLo α = 0
  H_vHi : ∀ α ∈ Ioo (0 : ℝ) 1, H vHi α = 1
  H_cont : ∀ α ∈ Ioo (0 : ℝ) 1, ContinuousOn (fun v => H v α) (Icc vLo vHi)
  H_hasDerivAt : ∀ α ∈ Ioo (0 : ℝ) 1, ∀ v ∈ Ioo vLo vHi, HasDerivAt (fun x => H x α) (h v α) v
  h_pos : ∀ α ∈ Ioo (0 : ℝ) 1, ∀ v ∈ Icc vLo vHi, 0 < h v α
  h_cont : ∀ α ∈ Ioo (0 : ℝ) 1, ContinuousOn (fun v => h v α) (Icc vLo vHi)
  /-- `∂H(v, α)/∂α` exists and equals `Hα v α` (p. 16) -/
  H_hasDerivAt_α : ∀ v ∈ Icc vLo vHi, ∀ α ∈ Ioo (0 : ℝ) 1, HasDerivAt (fun a => H v a) (Hα v α) α
  /-- the rotation order (9), on the support -/
  rotation : ∀ α ∈ Ioo (0 : ℝ) 1,
    (∀ v ∈ Ioo vLo vPlus, 0 < Hα v α) ∧ (∀ v ∈ Ioo vPlus vHi, Hα v α < 0)
  /-- the mean of `H(·, α)` is the prior mean `û` for every `α` (p. 16) -/
  mean_eq : ∀ α ∈ Ioo (0 : ℝ) 1, ∫ v in vLo..vHi, v * h v α = uHat

namespace Model

variable (M : Model)

/-- Footnote 5 (p. 7), the part used for strict comparisons: `k` is continuous on `[α̲, ᾱ]`,
differentiable inside, `k′(α̲) = 0` (one-sided) and `k′(α) → +∞` as `α → ᾱ⁻`. -/
def Footnote5 : Prop :=
  ContinuousOn M.k (Icc M.aLo M.aHi) ∧
  (∀ a ∈ Ioo M.aLo M.aHi, DifferentiableAt ℝ M.k a) ∧
  HasDerivWithinAt M.k 0 (Ici M.aLo) M.aLo ∧
  Tendsto (deriv M.k) (𝓝[<] M.aHi) atTop

/-- `∂H/∂α` is jointly continuous on `[v̲, v̄] × (0, 1)` (H continuously differentiable in `α`). -/
def HαContinuous : Prop :=
  ContinuousOn (Function.uncurry M.Hα) (Icc M.vLo M.vHi ×ˢ Ioo (0 : ℝ) 1)

/-- The cost of type `i`. -/
def c : SellingData.ListsBinary.CostType → ℝ
  | .H => M.cH
  | .L => M.cL

/-- The probability `θ_i` of type `i`: `θ_H = θ`, `θ_L = 1 - θ`. -/
def θof : SellingData.ListsBinary.CostType → ℝ
  | .H => M.θ
  | .L => 1 - M.θ

/-- A marketer's gross expected payoff from informativeness `α` at targeting cost `c`:
`∫_c^{v̄} (v - c) dH(v, α)`, with `dH(v, α) = h(v, α) dv` ((11), (13)). -/
noncomputable def payoff (α c : ℝ) : ℝ :=
  ∫ v in c..M.vHi, (v - c) * M.h v α

end Model

/-- A menu of two service plans `(T_H, α_H)` and `(T_L, α_L)` (p. 9). -/
structure Menu where
  TH : ℝ
  αH : ℝ
  TL : ℝ
  αL : ℝ

namespace Menu

/-- The fixed payment of plan `j`. -/
def T (m : Menu) : SellingData.ListsBinary.CostType → ℝ
  | .H => m.TH
  | .L => m.TL

/-- The informativeness of plan `j`. -/
def α (m : Menu) : SellingData.ListsBinary.CostType → ℝ
  | .H => m.αH
  | .L => m.αL

end Menu

namespace Model

variable (M : Model)

/-- (13): `U_ij = -T_j + ∫_{c_i}^{v̄} (v - c_i) dH(v, α_j)`. -/
noncomputable def U (m : Menu) (i j : SellingData.ListsBinary.CostType) : ℝ :=
  -(m.T j) + M.payoff (m.α j) (M.c i)

/-- The constraints of (6): `T_j ≥ 0`, `α_j ∈ [α̲, ᾱ]`, `IR_i : U_ii ≥ 0`,
`IC_{i,i'} : U_ii ≥ U_ii'` for `i ≠ i'`. -/
def Feasible (m : Menu) : Prop :=
  0 ≤ m.TH ∧ 0 ≤ m.TL ∧ m.αH ∈ Icc M.aLo M.aHi ∧ m.αL ∈ Icc M.aLo M.aHi ∧
  (∀ i : SellingData.ListsBinary.CostType, 0 ≤ M.U m i i) ∧
  (∀ i i' : SellingData.ListsBinary.CostType, i ≠ i' → M.U m i i' ≤ M.U m i i)

/-- The seller's objective (6): `Π = Σ_i θ_i [T_i - k(α_i)]`. -/
def profit (m : Menu) : ℝ :=
  M.θ * (m.TH - M.k m.αH) + (1 - M.θ) * (m.TL - M.k m.αL)

/-- `m` solves the screening problem (6) with payoff (13). -/
def IsOptimalMenu (m : Menu) : Prop :=
  M.Feasible m ∧ ∀ m' : Menu, M.Feasible m' → M.profit m' ≤ M.profit m

/-- The benchmark objective (12): `Π_i = θ_i [∫_{c}^{v̄} (v - c) dH(v, α) - k(α)]`. -/
noncomputable def benchProfit (θi α c : ℝ) : ℝ :=
  θi * (M.payoff α c - M.k α)

/-- `a` is an efficient informativeness: a maximizer of the benchmark (12) over `[α̲, ᾱ]`. -/
def IsEfficient (θi c a : ℝ) : Prop :=
  a ∈ Icc M.aLo M.aHi ∧ ∀ a' ∈ Icc M.aLo M.aHi, M.benchProfit θi a' c ≤ M.benchProfit θi a c

/-- The objective of the reduced problem (14), term by term. -/
noncomputable def reducedProfit (αH αL : ℝ) : ℝ :=
  M.θ * (M.payoff αH M.cH - M.k αH) +
    (1 - M.θ) * (M.payoff αL M.cL - M.payoff αH M.cL + M.payoff αH M.cH - M.k αL)

/-- `(αH, αL)` maximizes the reduced problem (14) over `[α̲, ᾱ]²`. -/
def IsReducedMax (αH αL : ℝ) : Prop :=
  αH ∈ Icc M.aLo M.aHi ∧ αL ∈ Icc M.aLo M.aHi ∧
  ∀ βH ∈ Icc M.aLo M.aHi, ∀ βL ∈ Icc M.aLo M.aHi, M.reducedProfit βH βL ≤ M.reducedProfit αH αL

/-- The high type's rent `R(α_H) = ∫_{c_L}^{c_H} [1 - H(v, α_H)] dv` (p. 32). -/
noncomputable def rent (α : ℝ) : ℝ :=
  ∫ v in M.cL..M.cH, (1 - M.H v α)

end Model

end SellingData.ListsRotation


