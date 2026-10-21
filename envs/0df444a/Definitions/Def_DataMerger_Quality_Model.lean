-- Prove2me | Definitions.Def_DataMerger_Quality_Model
-- name    : DataMerger_Quality_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-21T00:24:07.548385+00:00
-- url     : https://prove2.me/theorems/c63d578e-0ed1-4208-b453-48f5c7248869
-- title:
--   Sections 3–4 — data-connected monopoly and Hotelling duopoly model
-- statement:
--   Firm A sells in a monopoly market with demand $D_A(p)=\max\{\alpha-p,0\}$ and collects a data set of size $\delta=D_A(p)$. Two firms compete for consumers on a unit Hotelling segment. If one holds data of size $d$ and its rival holds $d'$, their product qualities are $V(d)$ and $V(d')$. The model fixes their interior demand, equilibrium prices and profits:
--
--   $$
--   D_B=\frac{1+V(d)-V(d')-p_j+p_k}{2},\qquad
--   p_B(d,d')=1+\frac{V(d)-V(d')}{3},\qquad
--   \pi_B(d,d')=\frac{(3+V(d)-V(d'))^2}{18}.
--   $$
--
--   It also defines consumer surplus in both markets, exclusive and nonexclusive licence prices $T^1$ and $T^2$, the resulting data allocation, and the independent and merged firms' first-stage objectives. Both objectives include the choice between exclusive and nonexclusive supply.
--
--   **Formalization Note** Prices range over all real numbers and data quantities used by the results are nonnegative. The standing conditions require $\alpha>0$, global differentiability of $V$, $V'(d)>0$ for $d\ge0$, $V(d)-V(0)<3$ for $d\ge0$, and $2V(0)\ge3$. The strict derivative condition strengthens the paper's stated non-decreasing assumption so its strict Lemma 2 conclusions hold. The final two bounds spell out covered demand and active B firms. The auction is represented by its data-price formulas, rather than bidding strategies.
-- source:
--   de Cornière & Taylor, Data-Driven Mergers, TSE Working Paper No. 1576 (Sept. 2024; manuscript of Dec. 20, 2023), pp. 5–9 (PDF 6–10), Sections 3–4, equations (1)–(2)

import Mathlib

namespace DataMerger.Quality

open Classical
noncomputable section

/-- The quality model's standing conditions, including the strict marginal improvement
needed by the strict conclusions of Lemma 2. -/
noncomputable def Standing (alpha : ℝ) (V : ℝ → ℝ) : Prop :=
  0 < alpha ∧ Differentiable ℝ V ∧
    (∀ δ, 0 ≤ δ → 0 < deriv V δ) ∧
    (∀ δ, 0 ≤ δ → V δ - V 0 < 3) ∧
    3 ≤ 2 * V 0

/-- Demand for A at price `p`. -/
noncomputable def DA (alpha p : ℝ) : ℝ := max (alpha - p) 0

/-- Consumer surplus in market A at price `p`. -/
noncomputable def CSA (alpha p : ℝ) : ℝ := ∫ s in p..alpha, DA alpha s

/-- Interior market share of a B firm at its own and rival prices. -/
def DB (V : ℝ → ℝ) (d d' pj pk : ℝ) : ℝ :=
  (1 + V d - V d' - pj + pk) / 2

/-- The B firm's equilibrium price, equation (2). -/
def pB (V : ℝ → ℝ) (d d' : ℝ) : ℝ := 1 + (V d - V d') / 3

/-- The B firm's equilibrium profit, equation (2). -/
def piB (V : ℝ → ℝ) (d d' : ℝ) : ℝ := (3 + V d - V d') ^ 2 / 18

/-- Consumer surplus on the covered Hotelling segment at the equilibrium B prices. -/
noncomputable def UB (V : ℝ → ℝ) (d1 d2 : ℝ) : ℝ :=
  let xh := DB V d1 d2 (pB V d1 d2) (pB V d2 d1)
  (∫ x in (0 : ℝ)..xh, (V d1 - x - pB V d1 d2)) +
    ∫ x in xh..1, (V d2 - (1 - x) - pB V d2 d1)

/-- The price net of the quality of the firm's own product. -/
def qaPrice (V : ℝ → ℝ) (d d' : ℝ) : ℝ := pB V d d' - V d

/-- Price of one exclusive data licence. -/
def T1 (pi : ℝ → ℝ → ℝ) (δ : ℝ) : ℝ := pi δ 0 - pi 0 δ

/-- Per-firm price of nonexclusive data licences. -/
def T2 (pi : ℝ → ℝ → ℝ) (δ : ℝ) : ℝ := pi δ δ - pi 0 δ

def ExclusiveI (pi : ℝ → ℝ → ℝ) (δ : ℝ) : Prop := 2 * T2 pi δ < T1 pi δ

def ExclusiveM (pi : ℝ → ℝ → ℝ) (δ : ℝ) : Prop :=
  pi δ δ + T2 pi δ < pi δ 0

/-- Data held by the buyer and its rival when A remains independent. -/
noncomputable def allocI (pi : ℝ → ℝ → ℝ) (δ : ℝ) : ℝ × ℝ :=
  if ExclusiveI pi δ then (δ, 0) else (δ, δ)

/-- Data held by B1 and B2 when A and B1 merge. -/
noncomputable def allocM (pi : ℝ → ℝ → ℝ) (δ : ℝ) : ℝ × ℝ :=
  if ExclusiveM pi δ then (δ, 0) else (δ, δ)

/-- Independent A's market-A profit and its optimal choice of one or two licences. -/
noncomputable def objI (alpha : ℝ) (V : ℝ → ℝ) (p : ℝ) : ℝ :=
  p * DA alpha p +
    max (T1 (piB V) (DA alpha p)) (2 * T2 (piB V) (DA alpha p))

/-- Merged A-B1's market-A profit and its optimal choice whether to license B2. -/
noncomputable def objM (alpha : ℝ) (V : ℝ → ℝ) (p : ℝ) : ℝ :=
  p * DA alpha p +
    max (piB V (DA alpha p) 0)
      (piB V (DA alpha p) (DA alpha p) + T2 (piB V) (DA alpha p))

end
end DataMerger.Quality


