-- Prove2me | Definitions.Def_SpatialDemandEq_Optimal_Model
-- name    : SpatialDemandEq_Optimal_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-20T16:19:22.370989+00:00
-- url     : https://prove2.me/theorems/a66ea614-7969-49b6-8c75-0bde2a730097
-- title:
--   §3.1, §4.1, §4.3, pp. 6–18 — spatial service model: partitions, weighted Voronoi cells, decentralized equilibrium (1)/(3), partition problem (9)–(12), social cost (15), local optima
-- statement:
--   This file sets up the spatial service model of Carlsson, Peng and Ryzhov.
--
--   **Region, demand and facilities.** A closed convex region $\mathcal S \subseteq \mathbb R^n$ carries a normalized demand distribution $\nu$ (the measure $m(x)\,dx$): a probability measure, absolutely continuous with respect to Lebesgue measure, with $\nu(\mathcal S^{c}) = 0$. There are $K \ge 1$ facilities at locations $x_1,\dots,x_K \in \mathcal S$, and $d$ is a metric on $\mathbb R^n$, continuous for the Euclidean topology; the travel distance to facility $k$ is $d_k(x) = d(x, x_k)$. The constants $c > 0$ (weight of waiting time) and $\lambda > 0$ (aggregate arrival rate) are given.
--
--   **Partitions and areas.** A partition of $\mathcal S$ is a family $(\mathcal A_1,\dots,\mathcal A_K)$ of measurable subsets of $\mathcal S$ with $\bigcup_k \mathcal A_k = \mathcal S$ and $\nu(\mathcal A_j \cap \mathcal A_k) = 0$ for $j \ne k$. The area of a subregion is $A = \nu(\mathcal A)$.
--
--   **Weighted Voronoi cells.** For weights $w \in \mathbb R^K$, the cell of facility $k$ is
--   $$\mathcal A_k(w) = \{x \in \mathcal S : d_k(x) + w_k \le d_j(x) + w_j \text{ for all } j \ne k\}.$$
--
--   **Decentralized equilibrium.** Given service rates $\mu \in \mathbb R^K$, a partition is a demand equilibrium (1) if every facility is stable, $\lambda A_k < \mu_k$, and every customer $x \in \mathcal A_k$ weakly prefers facility $k$:
--   $$d_k(x) + \frac{c}{\mu_k - \lambda A_k} \le d_j(x) + \frac{c}{\mu_j - \lambda A_j} \qquad (j \ne k).$$
--   Weights $w$ solve the equilibrium condition (3) if $\lambda A_k(w) < \mu_k$ and $w_k = c/(\mu_k - \lambda A_k(w))$ for every $k$.
--
--   **General partitioning problem (9)–(12).** For functions $g_k$ and $G : \mathbb R^K \to \mathbb R$, the objective of a partition is $G(A_1,\dots,A_K) + \sum_k \int_{\mathcal A_k} g_k\,d\nu$. The standing assumptions of §4.1 are bundled as: $\mathcal S$ closed and convex, $\nu$ as above, each $g_k$ continuous and $\nu$-integrable, and the regularity condition that for $j \ne k$ the law of $g_j(Y) - g_k(Y)$, $Y \sim \nu$, has a density. A local optimum is a partition $\bar{\mathcal A}$ for which some $\varepsilon > 0$ makes every partition $\mathcal A'$ with $\nu(\mathcal A'_k \,\triangle\, \bar{\mathcal A}_k) < \varepsilon$ for all $k$ at least as costly.
--
--   **Social cost (15).** With a budget $B$, the social cost of rates $\mu$ and a partition is
--   $$\sum_k A_k\,\frac{c}{\mu_k - \lambda A_k} + \sum_k \int_{\mathcal A_k} d_k\,d\nu,$$
--   feasible when the partition is a partition of $\mathcal S$, $\sum_k \mu_k = B$ and $\lambda A_k < \mu_k$ for every $k$. A local optimum $(\mu^{**}, \mathcal A^{**})$ is feasible and, for some $\varepsilon > 0$, no more costly than any feasible $(\mu', \mathcal A')$ with $|\mu'_k - \mu^{**}_k| < \varepsilon$ and $\nu(\mathcal A'_k \,\triangle\, \mathcal A^{**}_k) < \varepsilon$ for all $k$.
--
--   **Closed forms.** For areas $A$ with $s = \sum_j \sqrt{A_j}$, the rates (17) and weights (16) are
--   $$\mu_k = \lambda A_k + (B - \lambda)\frac{\sqrt{A_k}}{s}, \qquad w_k = \frac{c}{B - \lambda}\, s\, \frac{1}{\sqrt{A_k}}.$$
--
--   These objects carry every statement of the mission: the decentralized model of §3 and the centralized social-optimum problem of §4.
--
--   **Formalization Note** The waiting cost $f_k(A) = c/(\mu_k - \lambda A)$, which the paper sets to $\infty$ for $A \ge \mu_k/\lambda$, is kept real-valued: every use carries the stability conjunct $\lambda A_k < \mu_k$. When all $\mu_k > 0$ and $\sum_k \mu_k > \lambda$ (as for the rates of Theorem 6), a paper equilibrium has no unstable cell, so nothing is lost; in (15) the conjunct restricts to where the objective is finite. Partitions are taken up to $\nu$-null overlaps, as in (11). Two hypotheses are added to the paper's standing assumptions: each $d_k$ (resp. $g_k$) is $\nu$-integrable, since otherwise the integral terms are not real numbers; and the paper's positive intensity $\lambda(x) > 0$ is dropped, which only weakens the hypotheses. The differentiability of the $g_k$ assumed in §4.1 is not part of the general setting (Theorem 4 holds without it). Since the maps $g_j - g_k$ are continuous, hence measurable, the regularity condition (a push-forward measure absolutely continuous w.r.t. Lebesgue measure) is not vacuous. "Local optimum" uses the smallest neighbourhood (closeness of the rates and of each cell in $\nu$-symmetric difference), which makes the hypothesis weakest.
-- source:
--   Carlsson, Peng & Ryzhov, Demand Equilibria in Spatial Service Systems, SSRN preprint 4794156 (version of 2024-04-14), pp. 6–18, §3.1 (equations (1)–(3)), §4.1 (regularity condition, (9)–(12)), §4.3 ((15)–(17))

import Mathlib

namespace SpatialDemandEq.Optimal

open MeasureTheory

/-- The ambient space `ℝⁿ` of §3.1, p. 6. -/
abbrev E (n : ℕ) := EuclideanSpace ℝ (Fin n)

/-- `dst` is a metric on `ℝⁿ` that is continuous for the Euclidean topology (p. 7: "any other
continuous metric can also be used"). -/
def IsContinuousMetric {n : ℕ} (dst : E n → E n → ℝ) : Prop :=
  Continuous (Function.uncurry dst) ∧ (∀ x y, dst x y = 0 ↔ x = y) ∧
    (∀ x y, dst x y = dst y x) ∧ (∀ x y z, dst x z ≤ dst x y + dst y z)

/-- The travel distances `d_k(x) = d(x, x_k)` to the facilities `x_1, …, x_K` (p. 7). -/
def distFn {n K : ℕ} (dst : E n → E n → ℝ) (xs : Fin K → E n) : Fin K → E n → ℝ :=
  fun k x => dst x (xs k)

/-- A geographical partition of `S` (p. 7) / constraints (11)–(12) (p. 14): measurable pieces
contained in `S`, covering `S`, with pairwise `ν`-null intersections. -/
def IsPartition {n K : ℕ} (ν : Measure (E n)) (S : Set (E n)) (A : Fin K → Set (E n)) : Prop :=
  (∀ k, MeasurableSet (A k)) ∧ (∀ k, A k ⊆ S) ∧ (⋃ k, A k) = S ∧
    ∀ j k, j ≠ k → ν (A j ∩ A k) = 0

/-- The area `A = ∬_𝒜 m(x) dx = ν(𝒜)` of a subregion (p. 6, constraint (10)). -/
noncomputable def area {n : ℕ} (ν : Measure (E n)) (A : Set (E n)) : ℝ := (ν A).toReal

/-- The vector of areas `(A_1, …, A_K)` of a family of subregions. -/
noncomputable def areas {n K : ℕ} (ν : Measure (E n)) (A : Fin K → Set (E n)) : Fin K → ℝ :=
  fun k => area ν (A k)

/-- The additively weighted Voronoi cell `𝒜_k(w)` of (2), p. 8: the points `x ∈ S` with
`d_k(x) + w_k ≤ d_j(x) + w_j` for every `j ≠ k`. -/
def cell {n K : ℕ} (S : Set (E n)) (d : Fin K → E n → ℝ) (w : Fin K → ℝ) (k : Fin K) :
    Set (E n) :=
  {x | x ∈ S ∧ ∀ j, j ≠ k → d k x + w k ≤ d j x + w j}

/-- The regularity condition of §4.1, p. 13: for `j ≠ k`, the law of `g_j(Y) − g_k(Y)` under
`Y ∼ ν` has a density (is absolutely continuous with respect to Lebesgue measure). -/
def Regular {n K : ℕ} (ν : Measure (E n)) (g : Fin K → E n → ℝ) : Prop :=
  ∀ j k, j ≠ k → ν.map (fun x => g j x - g k x) ≪ volume

/-- The standing assumptions of the general partitioning problem, §4.1, p. 13 (with §3.1's `S`
closed and convex, p. 6): `ν` is a probability measure on `S`, absolutely continuous with respect
to Lebesgue measure; the `g_k` are continuous, `ν`-integrable (added: otherwise (9) is not a real
number) and satisfy the regularity condition. -/
structure GeneralSetting {n K : ℕ} (S : Set (E n)) (ν : Measure (E n)) (g : Fin K → E n → ℝ) :
    Prop where
  closed : IsClosed S
  convex : Convex ℝ S
  prob : IsProbabilityMeasure ν
  ac : ν ≪ volume
  supp : ν Sᶜ = 0
  cont : ∀ k, Continuous (g k)
  integrable : ∀ k, Integrable (g k) ν
  regular : Regular ν g

/-- The standing assumptions of the spatial service model, §3.1 (pp. 6–7) and §4.1 (p. 13), with
`g_k = d_k`: `S` closed and convex; `ν` (the normalized demand `m(x) dx`) a probability measure on
`S`, absolutely continuous with respect to Lebesgue measure; `dst` a continuous metric; facilities
in `S`; the regularity condition for the `d_k`; each `d_k` `ν`-integrable (added); `c > 0`,
`λ > 0` and at least one facility. -/
structure Standing {n K : ℕ} (S : Set (E n)) (ν : Measure (E n)) (dst : E n → E n → ℝ)
    (xs : Fin K → E n) (c lam : ℝ) : Prop where
  closed : IsClosed S
  convex : Convex ℝ S
  prob : IsProbabilityMeasure ν
  ac : ν ≪ volume
  supp : ν Sᶜ = 0
  metric : IsContinuousMetric dst
  fac_mem : ∀ k, xs k ∈ S
  regular : Regular ν (distFn dst xs)
  integrable : ∀ k, Integrable (distFn dst xs k) ν
  c_pos : 0 < c
  lam_pos : 0 < lam
  K_pos : 0 < K

/-- The decentralized demand equilibrium (1), p. 7, under service rates `μ`: a partition of `S`
whose cells are all stable (`λ A_k < μ_k`, so `f_k(A_k) = c/(μ_k − λ A_k)` is finite) and such
that every customer `x ∈ 𝒜_k` weakly prefers facility `k`:
`d_k(x) + f_k(A_k) ≤ d_j(x) + f_j(A_j)` for all `j ≠ k`. -/
def IsDecentralizedEq {n K : ℕ} (ν : Measure (E n)) (S : Set (E n)) (d : Fin K → E n → ℝ)
    (c lam : ℝ) (μ : Fin K → ℝ) (A : Fin K → Set (E n)) : Prop :=
  IsPartition ν S A ∧ (∀ k, lam * area ν (A k) < μ k) ∧
    ∀ k, ∀ x ∈ A k, ∀ j, j ≠ k →
      d k x + c / (μ k - lam * area ν (A k)) ≤ d j x + c / (μ j - lam * area ν (A j))

/-- The equilibrium condition (3), p. 8: `w_k = f_k(A_k(w))` for every `k`, with `f_k(A_k(w))`
finite (`λ A_k(w) < μ_k`). -/
def IsEqWeight {n K : ℕ} (ν : Measure (E n)) (S : Set (E n)) (d : Fin K → E n → ℝ)
    (c lam : ℝ) (μ : Fin K → ℝ) (w : Fin K → ℝ) : Prop :=
  ∀ k, lam * area ν (cell S d w k) < μ k ∧ w k = c / (μ k - lam * area ν (cell S d w k))

/-- The linear part `∑_k ∬_{𝒜_k} g_k dν` of (9) and (28). -/
noncomputable def linCost {n K : ℕ} (ν : Measure (E n)) (g : Fin K → E n → ℝ)
    (A : Fin K → Set (E n)) : ℝ :=
  ∑ k, ∫ x in A k, g k x ∂ν

/-- The objective (9), p. 14: `G(A_1, …, A_K) + ∑_k ∬_{𝒜_k} g_k dν`. -/
noncomputable def partitionObj {n K : ℕ} (ν : Measure (E n)) (G : (Fin K → ℝ) → ℝ)
    (g : Fin K → E n → ℝ) (A : Fin K → Set (E n)) : ℝ :=
  G (areas ν A) + linCost ν g A

/-- A local optimum of (9)–(12): a partition such that, for some `ε > 0`, every partition `𝒜'`
with `ν(𝒜'_k △ 𝒜_k) < ε` for all `k` has an objective value at least as large. -/
def IsLocalOptPartition {n K : ℕ} (ν : Measure (E n)) (S : Set (E n)) (G : (Fin K → ℝ) → ℝ)
    (g : Fin K → E n → ℝ) (A : Fin K → Set (E n)) : Prop :=
  IsPartition ν S A ∧ ∃ ε : ℝ, 0 < ε ∧ ∀ A' : Fin K → Set (E n), IsPartition ν S A' →
    (∀ k, ν (symmDiff (A' k) (A k)) < ENNReal.ofReal ε) →
      partitionObj ν G g A ≤ partitionObj ν G g A'

/-- The waiting-cost term `∑_k A_k · c/(μ_k − λ A_k)` of (15) and (18), for areas `a`. -/
noncomputable def rateCost {K : ℕ} (c lam : ℝ) (μ : Fin K → ℝ) (a : Fin K → ℝ) : ℝ :=
  ∑ k, a k * (c / (μ k - lam * a k))

/-- The social cost (15), p. 17:
`∑_k A_k c/(μ_k − λ A_k) + ∑_k ∬_{𝒜_k} d_k(x) m(x) dx`. -/
noncomputable def socialCost {n K : ℕ} (ν : Measure (E n)) (d : Fin K → E n → ℝ) (c lam : ℝ)
    (μ : Fin K → ℝ) (A : Fin K → Set (E n)) : ℝ :=
  rateCost c lam μ (areas ν A) + linCost ν d A

/-- Feasibility for (15): a partition of `S` (constraints (10)–(12)), the budget `∑_k μ_k = B`,
and every facility stable (`λ A_k < μ_k`, where the objective is finite). -/
def Feasible {n K : ℕ} (ν : Measure (E n)) (S : Set (E n)) (lam B : ℝ) (μ : Fin K → ℝ)
    (A : Fin K → Set (E n)) : Prop :=
  IsPartition ν S A ∧ ∑ k, μ k = B ∧ ∀ k, lam * area ν (A k) < μ k

/-- A local optimum `(μ**, 𝒜**)` of (15): feasible, and for some `ε > 0` every feasible
`(μ', 𝒜')` with `|μ'_k − μ_k| < ε` and `ν(𝒜'_k △ 𝒜_k) < ε` for all `k` has social cost at
least as large. -/
def IsLocalOpt {n K : ℕ} (ν : Measure (E n)) (S : Set (E n)) (d : Fin K → E n → ℝ)
    (c lam B : ℝ) (μ : Fin K → ℝ) (A : Fin K → Set (E n)) : Prop :=
  Feasible ν S lam B μ A ∧ ∃ ε : ℝ, 0 < ε ∧ ∀ (μ' : Fin K → ℝ) (A' : Fin K → Set (E n)),
    Feasible ν S lam B μ' A' → (∀ k, |μ' k - μ k| < ε) →
      (∀ k, ν (symmDiff (A' k) (A k)) < ENNReal.ofReal ε) →
        socialCost ν d c lam μ A ≤ socialCost ν d c lam μ' A'

/-- The service rates (17), p. 18:
`μ_k = λ A_k + (B − λ) √A_k / ∑_j √A_j`. -/
noncomputable def optRates {K : ℕ} (lam B : ℝ) (a : Fin K → ℝ) : Fin K → ℝ :=
  fun k => lam * a k + (B - lam) * Real.sqrt (a k) / ∑ j, Real.sqrt (a j)

/-- The Voronoi weights (16), p. 17:
`w_k = c/(B − λ) · (∑_j √A_j) · 1/√A_k`. -/
noncomputable def optWeights {K : ℕ} (c lam B : ℝ) (a : Fin K → ℝ) : Fin K → ℝ :=
  fun k => c / (B - lam) * (∑ j, Real.sqrt (a j)) * (1 / Real.sqrt (a k))

end SpatialDemandEq.Optimal


