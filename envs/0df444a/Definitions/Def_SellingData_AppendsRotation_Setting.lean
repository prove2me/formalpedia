-- Prove2me | Definitions.Def_SellingData_AppendsRotation_Setting
-- name    : SellingData_AppendsRotation_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-13T22:34:55.809116+00:00
-- url     : https://prove2.me/theorems/03a0aab6-8af9-4c0a-82f6-99d0ccc9edd2
-- title:
--   §2–§3, §4–§4.2, pp. 7–20 — data-append screening: menus, payoffs (13), outside option max{û − c, 0}, problem (6), benchmark (12), objective (15)
-- statement:
--   This definition sets up the **selling of data appends** under the generalized information structure (§4.2).
--
--   **Model.** A data seller offers service plans $(T,\alpha)$: a fixed payment $T\ge 0$ for a service of informativeness $\alpha\in[\underline\alpha,\bar\alpha]\subset(0,1)$. Serving a marketer with a plan of informativeness $\alpha$ costs the seller $k(\alpha)$, where $k(\underline\alpha)=0$ and $k$ is increasing on $[\underline\alpha,\bar\alpha]$. A marketer's targeting cost is $c_H$ with probability $\theta\in(0,1)$ and $c_L$ with probability $1-\theta$, with $0<c_L<c_H$ and both costs inside the support $(\underline v,\bar v)$ of the posterior mean. The posterior mean has the rotation-ordered distribution $H(v,\alpha)$ with density $h$, rotation point $v^+$ and mean $\hat u$ (the definition `RotationFamily`).
--
--   **Payoffs.** A marketer with cost $c_i$ who buys the plan $(T_j,\alpha_j)$ targets exactly when $v>c_i$ and earns
--   $$
--   U_{ij}=-T_j+\int_{c_i}^{\bar v}(v-c_i)\,dH(v,\alpha_j). \qquad (13)
--   $$
--   For data appends the marketer can target without the seller's data, so its outside option is $U_{i0}=\max\{\hat u-c_i,0\}$.
--
--   **Screening problem.** A menu $(T_H,\alpha_H),(T_L,\alpha_L)$ is feasible if $T_H,T_L\ge0$, $\alpha_H,\alpha_L\in[\underline\alpha,\bar\alpha]$, $U_{ii}\ge U_{i0}$ ($IR_i$) and $U_{ii}\ge U_{ii'}$ ($IC_{i,i'}$) for both types. The seller maximizes
--   $$
--   \Pi=\theta\,[T_H-k(\alpha_H)]+(1-\theta)\,[T_L-k(\alpha_L)]
--   $$
--   over feasible menus; an **optimal menu** is a feasible menu that no feasible menu beats.
--
--   **Benchmark.** With observable cost, the seller's problem for type $i$ is (12),
--   $$
--   \max_{\alpha\in[\underline\alpha,\bar\alpha]}\ \Pi_i=\theta_i\Big[\int_{c_i}^{\bar v}(v-c_i)\,dH(v,\alpha)-k(\alpha)\Big],
--   $$
--   with $\theta_H=\theta$, $\theta_L=1-\theta$; an **efficient** informativeness $\alpha^e_i$ is any maximizer.
--
--   **Reduced problem (15).** For $c_L<c_H<\hat u$ the paper reduces the screening problem to
--   $$
--   \Pi(\alpha_H,\alpha_L)=\theta\Big[\int_{c_H}^{\bar v}(v-c_H)\,dH(v,\alpha_H)-\Big(\int_{c_H}^{\bar v}(v-c_H)\,dH(v,\alpha_L)-\int_{c_L}^{\bar v}(v-c_L)\,dH(v,\alpha_L)\Big)-k(\alpha_H)\Big]+(1-\theta)\Big[\int_{c_L}^{\bar v}(v-c_L)\,dH(v,\alpha_L)-k(\alpha_L)\Big]-\hat u+c_L ,
--   $$
--   and the definition also records maximizers of this function over $[\underline\alpha,\bar\alpha]^2$.
--
--   **Pinned regularity.** Two properties are defined for use as hypotheses: the part of footnote 5 the strict results need ($k$ continuous on $[\underline\alpha,\bar\alpha]$, differentiable on $(\underline\alpha,\bar\alpha)$, $k'(\underline\alpha)=0$ from the right, $k'(\alpha)\to+\infty$ as $\alpha\to\bar\alpha^-$), and joint continuity of $\partial H(v,\alpha)/\partial\alpha$ on $[\underline v,\bar v]\times(0,1)$.
--
--   **Formalization Note.** $dH(v,\alpha)$ is written with the density, $h(v,\alpha)\,dv$. Optimal menus and efficient levels are sets of maximizers, never "the" maximizer, since $k$ need not be convex. The optimal menu is defined on the full problem (6) with the data-append $IR$ constraints, not through (15). The page prints (15) without the "+" between the two brackets; the rewritten form on p. 33 has it, and the sum is used here.
-- source:
--   Guo, Selling Data to Marketers, author's manuscript (Management Science, doi:10.1287/mnsc.2023.01350), pp. 7–9 (§2, footnote 5), p. 11 ((6)), p. 13 (§3.2), pp. 16–18 ((11)–(13)), p. 20 (§4.2, (15))

import Mathlib
import Definitions.Def_SellingData_AppendsRotation_RotationFamily

namespace SellingData.AppendsRotation

open Set Filter Topology

/-- The data-append screening model of Guo, *Selling Data to Marketers*, §2–§3 and §4.2:
the rotation-ordered information structure of §4, informativeness levels `[aLo, aHi] ⊂ (0, 1)`,
the selling cost `k` with `k(α̲) = 0`, increasing, the probability `θ ∈ (0, 1)` of the high-cost
type, and two targeting costs `0 < cL < cH`, both inside the support `(v̲, v̄)`. -/
structure Model extends RotationFamily where
  /-- lowest informativeness `α̲` -/
  aLo : ℝ
  /-- highest informativeness `ᾱ` -/
  aHi : ℝ
  /-- probability `θ = θ_H` of the high-cost type; `θ_L = 1 - θ` -/
  θ : ℝ
  /-- targeting cost `c_L` of the low-cost type -/
  cL : ℝ
  /-- targeting cost `c_H` of the high-cost type -/
  cH : ℝ
  /-- the seller's selling cost `k(α)` per marketer served -/
  k : ℝ → ℝ
  aLo_pos : 0 < aLo
  aLo_lt_aHi : aLo < aHi
  aHi_lt_one : aHi < 1
  θ_pos : 0 < θ
  θ_lt_one : θ < 1
  cL_pos : 0 < cL
  cL_lt_cH : cL < cH
  vLo_lt_cL : vLo < cL
  cH_lt_vHi : cH < vHi
  k_aLo : k aLo = 0
  k_monotoneOn : MonotoneOn k (Icc aLo aHi)

namespace Model

variable (M : Model)

/-- `∫_c^{v̄} (v − c) dH(v, α)`, the expected targeting surplus of a marketer with cost `c` who
holds a plan of informativeness `α` ((11), (13)), written with the density. -/
noncomputable def payoff (α c : ℝ) : ℝ := ∫ v in c..M.vHi, (v - c) * M.h v α

/-- The outside option of a data-append buyer with cost `c`, `U_{i0} = max{û − c, 0}` (p. 20). -/
noncomputable def outside (c : ℝ) : ℝ := max (M.uHat - c) 0

/-- `U_{ij} = −T_j + ∫_{c_i}^{v̄} (v − c_i) dH(v, α_j)` (13): the payoff of a marketer with cost `c`
who buys the plan `(T, α)`. -/
noncomputable def U (c T α : ℝ) : ℝ := -T + M.payoff α c

end Model

/-- A menu of two service plans `(T_H, α_H)` and `(T_L, α_L)`. -/
structure Menu where
  TH : ℝ
  αH : ℝ
  TL : ℝ
  αL : ℝ

namespace Model

variable (M : Model)

/-- Feasibility in the data-append screening problem: (6) with `IR_i` replaced by
`U_ii ≥ U_i0` (p. 20), fixed payments `T ≥ 0` (p. 8) and informativeness in `[α̲, ᾱ]`. -/
def Feasible (m : Menu) : Prop :=
  0 ≤ m.TH ∧ 0 ≤ m.TL ∧ m.αH ∈ Icc M.aLo M.aHi ∧ m.αL ∈ Icc M.aLo M.aHi ∧
  -- IR_H
  M.outside M.cH ≤ M.U M.cH m.TH m.αH ∧
  -- IR_L
  M.outside M.cL ≤ M.U M.cL m.TL m.αL ∧
  -- IC_{H,L}
  M.U M.cH m.TL m.αL ≤ M.U M.cH m.TH m.αH ∧
  -- IC_{L,H}
  M.U M.cL m.TH m.αH ≤ M.U M.cL m.TL m.αL

/-- The seller's expected profit (6), `Π = θ[T_H − k(α_H)] + (1 − θ)[T_L − k(α_L)]`. -/
def profit (m : Menu) : ℝ := M.θ * (m.TH - M.k m.αH) + (1 - M.θ) * (m.TL - M.k m.αL)

/-- `m` is an optimal menu: feasible, and no feasible menu earns more. -/
def IsOptimalMenu (m : Menu) : Prop :=
  M.Feasible m ∧ ∀ m' : Menu, M.Feasible m' → M.profit m' ≤ M.profit m

/-- The observable-cost benchmark (12), `Π_i = θ_i [∫_{c_i}^{v̄} (v − c_i) dH(v, α) − k(α)]`. -/
noncomputable def benchProfit (θi α c : ℝ) : ℝ := θi * (M.payoff α c - M.k α)

/-- `a` is an efficient informativeness for the type with probability `θi` and cost `c`:
a maximizer of the benchmark (12) over `[α̲, ᾱ]`. -/
def IsEfficient (θi c a : ℝ) : Prop :=
  a ∈ Icc M.aLo M.aHi ∧ ∀ a' ∈ Icc M.aLo M.aHi, M.benchProfit θi a' c ≤ M.benchProfit θi a c

/-- The objective (15) of the reduced data-append problem (with the `+` that the page omits
between the two brackets):
`θ[∫_{c_H}^{v̄}(v − c_H)dH(v, α_H) − [∫_{c_H}^{v̄}(v − c_H)dH(v, α_L) − ∫_{c_L}^{v̄}(v − c_L)dH(v, α_L)]
 − k(α_H)] + (1 − θ)[∫_{c_L}^{v̄}(v − c_L)dH(v, α_L) − k(α_L)] − û + c_L`. -/
noncomputable def reducedProfit (αH αL : ℝ) : ℝ :=
  M.θ * (M.payoff αH M.cH - (M.payoff αL M.cH - M.payoff αL M.cL) - M.k αH) +
    (1 - M.θ) * (M.payoff αL M.cL - M.k αL) - M.uHat + M.cL

/-- `(αH, αL)` maximizes (15) over `[α̲, ᾱ]²`. -/
def IsReducedOptimal (αH αL : ℝ) : Prop :=
  αH ∈ Icc M.aLo M.aHi ∧ αL ∈ Icc M.aLo M.aHi ∧
    ∀ a ∈ Icc M.aLo M.aHi, ∀ b ∈ Icc M.aLo M.aHi, M.reducedProfit a b ≤ M.reducedProfit αH αL

/-- The part of footnote 5 (p. 7) that is pinned: `k` is continuous on `[α̲, ᾱ]`, differentiable
on `(α̲, ᾱ)`, `k′(α̲) = 0` (right derivative) and `k′(α) → +∞` as `α → ᾱ⁻`. -/
def Footnote5 : Prop :=
  ContinuousOn M.k (Icc M.aLo M.aHi) ∧
    (∀ a ∈ Ioo M.aLo M.aHi, DifferentiableAt ℝ M.k a) ∧
    HasDerivWithinAt M.k 0 (Ici M.aLo) M.aLo ∧
    Tendsto (deriv M.k) (𝓝[<] M.aHi) atTop

/-- `∂H(v, α)/∂α` is jointly continuous on `[v̲, v̄] × (0, 1)` (the reading of "continuous and
differentiable" needed to differentiate `∫ H(v, α) dv` in `α`). -/
def HαContinuous : Prop :=
  ContinuousOn (Function.uncurry M.Hα) (Icc M.vLo M.vHi ×ˢ Ioo 0 1)

end Model

end SellingData.AppendsRotation


