-- Prove2me | Definitions.Def_BilateralProfit_Model
-- name    : BilateralProfit_Model
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:18:27.947984+00:00
-- url     : https://prove2.me/theorems/3f9d321e-cf68-400a-a341-f652a5c6030e
-- title:
--   §2–§3 — the bilateral trade model: trade, profit, the grid $G_K$ and the action set $\mathcal A=G_K\cap\mathcal T$
-- statement:
--   A broker faces, in each round, a seller and a buyer with private valuations $v=(s,b)\in[0,1]^2$. It posts a price pair $a=(p,q)$, offering $p$ to the seller and charging $q$ to the buyer. **Trade** occurs if $s\le p$ and $q\le b$ (ties are resolved in favour of acceptance); the **trade bit** is
--   $$z_a(v)=\mathbb 1\{s\le p\}\,\mathbb 1\{q\le b\},$$
--   and the **profit** is $\mathrm{Profit}(v,a)=(q-p)\,z_a(v)$, which is negative when $p>q$ and trade occurs.
--
--   For an integer $K\ge1$, the uniform **grid** is $G_K=\{(i/K,j/K): i,j=0,\dots,K\}$, the **triangle** is $\mathcal T=\{(p,q)\in[0,1]^2:p\le q\}$, and the **action set** is $\mathcal A=G_K\cap\mathcal T$.
--
--   A **valuation law** is a probability measure on $[0,1]^2$; its **probability function of trade** is $P(p,q)=\Pr_{(s,b)}(s\le p,\ b\ge q)$, and its expected profit at $(p,q)$ is $\mu(p,q)=(q-p)P(p,q)$. A **probability vector** on a finite set is a non-negative vector summing to one.
--
--   These objects underlie every statement of the mission.
--
--   **Formalization Note** Points and price pairs live in $\mathbb R\times\mathbb R$ (seller coordinate first). Grid points are indexed by $(i,j)\in\{0,\dots,K\}^2$ with value $(i/K,j/K)$; $\mathcal A$ is the set of indices with $i\le j$. A valuation law is a probability measure on $\mathbb R^2$ giving mass $0$ outside $[0,1]^2$.
-- source:
--   Brüstle, di Gregorio, Fusco, Leonardi, Regret Bounds for Profit Maximization in Bilateral Trade: Learning the Best Posted-Price Mechanism (manuscript, STOC 2027 submission, sha256 e91e81279505b765c7c96c219d674c0fbbbd6ca47a00da8fe228d498ca25ac87), §2, pp.3–4 (PDF 5–6); §3 (discretization paragraph), p.5 (PDF 7); §4.1, p.17 (PDF 19)

import Mathlib

namespace BilateralProfit

open MeasureTheory

/-! # The learning model: trade, profit, the grid `G_K` and the action set `𝒜`

Brüstle, di Gregorio, Fusco, Leonardi, *Regret Bounds for Profit Maximization in Bilateral
Trade: Learning the Best Posted-Price Mechanism* (manuscript, sha256 e91e8127…), §2, pp.3–4
(PDF 5–6); the grid `G_K` and `𝒜 = G_K ∩ 𝒯`, §3, p.5 (PDF 7); `z_a(v)`, §4.1, p.17.

**Formalization Note.** A valuation pair `v = (s, b)` and a price pair `a = (p, q)` are points
of `ℝ × ℝ` (first coordinate: seller; second: buyer). Trade happens iff `s ≤ p` and `q ≤ b`
("ties resolved in favor of acceptance"). Grid points are indexed by `Fin (K+1) × Fin (K+1)`;
the index `(i, j)` stands for the point `(i/K, j/K)`. The action set `𝒜 = G_K ∩ 𝒯` is the
subtype of index pairs with `i ≤ j`. Every statement using the grid assumes `0 < K` (step size
`1/K`). -/

/-- Trade occurs at prices `a = (p, q)` for valuations `v = (s, b)` iff `s ≤ p` and `q ≤ b`
(§2, p.3). -/
def Trades (v a : ℝ × ℝ) : Prop := v.1 ≤ a.1 ∧ a.2 ≤ v.2

noncomputable instance (v a : ℝ × ℝ) : Decidable (Trades v a) := by
  unfold Trades; infer_instance

/-- The trade bit `z_a(v) = 1{s ≤ p}·1{q ≤ b}` (§2, p.4; §4.1, p.17). -/
noncomputable def tradeBit (v a : ℝ × ℝ) : ℝ := if Trades v a then 1 else 0

/-- The realized profit `Profit(v, a) = (q − p)·1{s ≤ p}·1{q ≤ b}` (§2, p.3). It may be negative
when `p > q`. -/
noncomputable def profit (v a : ℝ × ℝ) : ℝ := (a.2 - a.1) * tradeBit v a

/-- Index set of the uniform grid `G_K = {(i/K, j/K) : i, j = 0, …, K}` (§3, p.5). -/
abbrev Grid (K : ℕ) : Type := Fin (K + 1) × Fin (K + 1)

/-- The point `(i/K, j/K) ∈ [0,1]²` of the grid index `(i, j)`. -/
noncomputable def pt (K : ℕ) (x : Grid K) : ℝ × ℝ := ((x.1 : ℝ) / K, (x.2 : ℝ) / K)

/-- The action set `𝒜 = G_K ∩ 𝒯`, `𝒯 = {(p, q) ∈ [0,1]² : p ≤ q}` (pp.4–5): grid indices with
`i ≤ j`. -/
abbrev Act (K : ℕ) : Type := {x : Grid K // x.1 ≤ x.2}

instance (K : ℕ) : Inhabited (Act K) := ⟨⟨(0, 0), le_rfl⟩⟩

/-- `f` is a probability vector on the finite type `α`: non-negative entries summing to `1`. -/
def IsDist {α : Type} [Fintype α] (f : α → ℝ) : Prop := (∀ x, 0 ≤ f x) ∧ ∑ x, f x = 1

/-- A law of a random valuation pair: a probability measure on `ℝ × ℝ` carried by `[0,1]²`. -/
def IsValLaw (μ : Measure (ℝ × ℝ)) : Prop :=
  IsProbabilityMeasure μ ∧ μ (Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1)ᶜ = 0

/-- The probability function of trade of a valuation law `μ`:
`P(p, q) = P_{(s,b)∼μ}(s ≤ p, b ≥ q)` (§2, p.4). -/
noncomputable def Ptrade (μ : Measure (ℝ × ℝ)) (a : ℝ × ℝ) : ℝ :=
  (μ {v | Trades v a}).toReal

/-- The expected profit `µ(p, q) = E[Profit(p, q)] = (q − p)·P(p, q)` under the valuation law `μ`
(§2, p.4). -/
noncomputable def muP (μ : Measure (ℝ × ℝ)) (a : ℝ × ℝ) : ℝ := (a.2 - a.1) * Ptrade μ a

end BilateralProfit


