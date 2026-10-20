-- Prove2me | Definitions.Def_OmniStores_ReturnRate_Model
-- name    : OmniStores_ReturnRate_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-20T02:19:34.661821+00:00
-- url     : https://prove2.me/theorems/702b74bb-b54f-4acd-aeaf-ac9b0cb97f03
-- title:
--   §3.1–§3.2, pp. 6–10 — circular-city store model and optimal decisions
-- statement:
--   The retailer offers a finite catalogue $I$ online and selects a real number $n\geq 0$ of equally spaced stores, each carrying the same subset $S\subseteq I$. Class $i$ has size $D_i>0$; a fraction $\theta$ is uninformed and dislikes the product with probability $\gamma\in(0,1)$. The online hassle cost is $h_o\geq0$, the return hassle cost is $h_r>0$, and travel costs $t$ per unit distance. Product $i$ has return-handling cost $k_i$, sales margin $m_i$, display area $\alpha_i$, and inventory-area coefficient $\beta_i$. Common store area is $\Omega_0>0$ and facility area costs $\xi>0$ per unit.
--
--   The definitions give the four online/store demands of (5)–(6), store size $\Omega$ of (8), and total expected profit of (9):
--
--   $$\pi(\gamma,n,S)=\sum_{i\in I}\left[m_i\bigl((1-\gamma)\theta D_i+(1-\theta)D_i\bigr)-k_i\gamma d_{i,o}\right]-n\xi\Omega.$$
--
--   An optimal decision maximizes this profit over all $n\geq0$ and $S\subseteq I$. Preference for stores means that a positive-store decision earns strictly more than the online-only decision. This shared model fixes the objects used throughout the mission.
--
--   **Formalization Note.** The paper's full-market-coverage assumption on p. 8 is used to start at the demand equations; valuations and prices are not separate fields. The paper relaxes store-count integrality on p. 11. At $n=0$, the displayed demand formulas give zero store demand and the store facility cost is zero. The bounds $0\leq\theta\leq1$ and $k_i\geq0$ make explicit the paper's meanings of “fraction” and “handling cost.”
-- source:
--   Gao, Agrawal & Cui, “The Effect of Multi-Channel and Omni-Channel Retailing on Physical Stores”, authors' manuscript (PDF of 2020-12-25), pp. 6–11, §3.1–§3.3, eqs. (5)–(9)

import Mathlib

namespace OmniStores.ReturnRate

/-- Parameters of the circular-city base model in §3.1–§3.2. The valuation and price
variables of (1)–(4) are omitted: the paper's full-market-coverage assumption on p. 8
gives the demands (5)–(6), from which the retailer's decisions are determined. -/
structure Params (ι : Type) where
  θ : ℝ
  D : ι → ℝ
  ho : ℝ
  hr : ℝ
  k : ι → ℝ
  m : ι → ℝ
  t : ℝ
  α : ι → ℝ
  β : ι → ℝ
  Ω0 : ℝ
  ξ : ℝ

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Standing assumptions on pp. 6–10. The explicit bounds `0 ≤ θ ≤ 1` and `0 ≤ k i`
read the page's “fraction” and “handling cost” as nonnegative quantities. The return
rate `γ ∈ (0,1)` is supplied by each theorem, since the results compare rates. -/
def Params.Standing (P : Params ι) : Prop :=
  0 ≤ P.θ ∧ P.θ ≤ 1 ∧ (∀ i, 0 < P.D i) ∧ 0 ≤ P.ho ∧ 0 < P.hr ∧
  (∀ i, 0 ≤ P.k i) ∧ 0 < P.t ∧ (∀ i, 0 < P.α i) ∧
  (∀ i, 0 < P.β i) ∧ 0 < P.Ω0 ∧ 0 < P.ξ

/-- Uninformed online demand, (5)–(6). At `n = 0`, Lean's `1 / 0 = 0` gives zero
store demand and the paper's online-only profit. -/
noncomputable def dUO (P : Params ι) (γ n : ℝ) (S : Finset ι) (i : ι) : ℝ :=
  if i ∈ S then
    (1 - 2 * min ((γ * P.hr + P.ho) / P.t) (1 / (2 * n)) * n) * P.θ * P.D i
  else P.θ * P.D i

/-- Uninformed store demand, (5)–(6). -/
noncomputable def dUS (P : Params ι) (γ n : ℝ) (S : Finset ι) (i : ι) : ℝ :=
  if i ∈ S then
    2 * min ((γ * P.hr + P.ho) / P.t) (1 / (2 * n)) * n * P.θ * P.D i
  else 0

/-- Informed online demand, (5)–(6). -/
noncomputable def dIO (P : Params ι) (n : ℝ) (S : Finset ι) (i : ι) : ℝ :=
  if i ∈ S then
    (1 - 2 * min (P.ho / P.t) (1 / (2 * n)) * n) * (1 - P.θ) * P.D i
  else (1 - P.θ) * P.D i

/-- Informed store demand, (5)–(6). -/
noncomputable def dIS (P : Params ι) (n : ℝ) (S : Finset ι) (i : ι) : ℝ :=
  if i ∈ S then
    2 * min (P.ho / P.t) (1 / (2 * n)) * n * (1 - P.θ) * P.D i
  else 0

/-- Size of one store, (8), including the common area. -/
noncomputable def storeSize (P : Params ι) (γ n : ℝ) (S : Finset ι) : ℝ :=
  S.sum (fun i => P.α i + P.β i * ((1 - γ) * dUS P γ n S i + dIS P n S i) / n) + P.Ω0

/-- Total expected profit (9): sales margins less online-return handling costs and
the facility cost of `n` identically sized stores. -/
noncomputable def profit (P : Params ι) (γ n : ℝ) (S : Finset ι) : ℝ :=
  (Finset.univ.sum (fun i => P.m i * ((1 - γ) * P.θ * P.D i + (1 - P.θ) * P.D i) -
    P.k i * γ * dUO P γ n S i)) - n * P.ξ * storeSize P γ n S

/-- The decision `(n,S)` maximizes (9) over all real `n ≥ 0` and store assortments.
The paper relaxes integrality of the store count on p. 11. -/
def IsOptimal (P : Params ι) (γ n : ℝ) (S : Finset ι) : Prop :=
  0 ≤ n ∧ ∀ (n' : ℝ) (S' : Finset ι), 0 ≤ n' → profit P γ n' S' ≤ profit P γ n S

/-- “The retailer prefers to have physical stores” means that a positive-store
decision strictly beats the online-only decision. This excludes threshold ties. -/
def PrefersStores (P : Params ι) (γ : ℝ) : Prop :=
  ∃ (n : ℝ) (S : Finset ι), 0 < n ∧ profit P γ 0 ∅ < profit P γ n S

end OmniStores.ReturnRate


