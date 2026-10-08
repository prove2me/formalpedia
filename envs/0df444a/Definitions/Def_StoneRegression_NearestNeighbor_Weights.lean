-- Prove2me | Definitions.Def_StoneRegression_NearestNeighbor_Weights
-- name    : StoneRegression_NearestNeighbor_Weights
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T19:20:45.182177+00:00
-- url     : https://prove2.me/theorems/39402aec-c561-4b70-bf79-0751268c3dad
-- title:
--   §3 and §11, pp. 599–613 — scales, the metric (6), regularity (7), nearest neighbor weights (8), cones and β(d, c)
-- statement:
--   This file defines the objects of Stone's nearest neighbor construction.
--
--   **Scales and the metric (6).** A scale $s_n$ is a nonnegative function $s_{nj} = s_{nj}(X, X_1, \dots, X_n)$, $1 \le j \le d$. The corresponding random pseudometric is
--   $$\rho_n(u,v) = \Big(\sum_{j:\ s_{nj} > 0} \Big(\frac{u_j - v_j}{s_{nj}}\Big)^2\Big)^{1/2}.$$
--
--   **Regularity.** $\{s_n\}$ is regular with constants $0 < a \le b$ if (i) $\lim_n P(s_{nj} > 0) = 1$ whenever the $j$th coordinate of $X$ has a nondegenerate distribution; (ii) $s_{nj}/s_{nl}$ is bounded in probability whenever the $j$th and $l$th coordinates are nondegenerate; and (iii) condition (7): whenever $n \ge 1$, $1 \le i \le n$ and the $j$th coordinates of $X_1,\dots,X_n$ do not all coincide,
--   $$a\, s_{nj}(X_i, X_1, \dots, X, \dots, X_n) \le s_{nj}(X, X_1, \dots, X_n) \le b\, s_{nj}(X_i, X_1, \dots, X, \dots, X_n),$$
--   where $(X_i, X_1, \dots, X, \dots, X_n)$ is the sequence with $X$ and $X_i$ interchanged. A sequence $Z_n$ is bounded in probability if $\lim_{M\to\infty}\limsup_n P(|Z_n| \ge M) = 0$.
--
--   **Nearest neighbor weights (8).** Let $c_{n1} \ge \dots \ge c_{nn} \ge 0$, $c_{ni} = 0$ for $i > n$, $\sum_i c_{ni} = 1$. The associated probability weight function is
--   $$W_{ni}(X) = \frac{c_{n\nu} + \dots + c_{n,\nu+\lambda-1}}{\lambda},$$
--   where $\nu = 1 + \#\{l \ne i : \rho_n(X_l, X) < \rho_n(X_i, X)\}$ and $\lambda = 1 + \#\{l \ne i : \rho_n(X_l, X) = \rho_n(X_i, X)\}$; tied points share the average of the coefficients of their ranks.
--
--   **Nearest neighbor index sets.** $I_{nt}(X)$ is the set of indices $i$ such that fewer than $k$ of the points $X_1,\dots,X_n$ are strictly closer to $X$ than $X_i$ in $\rho_n$, where $k \le t < k+1$; $I_{n0}(X) = \emptyset$.
--
--   **Cones and $\beta(d,c)$.** For $0 < c \le 1$, $\mathcal V(d,c)$ is the family of sets $V \subseteq \mathbb R^d$ any two nonzero elements of which satisfy $u\cdot v > (1 - c^2/2)\|u\|\|v\|$, and $\beta(d,c)$ is the least number of members of $\mathcal V(d,c)$ that cover $\mathbb R^d$.
--
--   **Swapped weights.** $U_{ni}(X) = W_{ni}(X_i, X_1, \dots, X, \dots, X_n)$: the weight evaluated with $X_i$ as the query and $X$ in its slot.
--
--   These are the objects of Theorem 2 and its supporting Propositions 9–12.
--
--   **Formalization Note** Sample indices and coordinates are 0-based, but the coefficients keep the paper's 1-based index ($c_{n,m}$ for $m\ge1$; $c_{n,0}$ is never read). Measurability of each $s_n$ is added to regularity (the paper treats $s_{nj}$ as random variables without saying so). (7) is read for all points, as Proposition 12's proof uses it ("think of $X, X_1, \dots, X_n$ as fixed points"). "Nondegenerate" means the law of the coordinate is not a point mass. The ratio $s_{nj}/s_{nl}$ is real division, which is $0$ where $s_{nl} = 0$; the first condition makes that event's probability tend to $0$, so boundedness in probability is unaffected. $I_{nt}$ uses $\lfloor t\rfloor$. $\beta(d,c)$ is an infimum over $\mathbb N$; the cover exists for $0 < c \le 1$ (compactness of the sphere), which is not proved here and is assumed by no statement.
-- source:
--   Stone (1977), Ann. Statist. 5, §3 p. 599 (scales, (6), regularity, (7), I_nk), p. 600 ((8)); §11 p. 611 (I_nt), p. 612 (𝒱(d, c), β(d, c)), p. 613 (U_ni)

import Mathlib
import Definitions.Def_StoneRegression_Criterion_Setting

namespace StoneRegression.NearestNeighbor

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

/-- A sequence of scales (p. 599): `s n x xs j = s_{n,j+1}(x, x₁, …, xₙ)`, with the StoneRegression.Criterion.sample `xs i = x_{i+1}`
and the coordinates `j` 0-based. -/
abbrev ScaleSeq (d : ℕ) : Type :=
  (n : ℕ) → EuclideanSpace ℝ (Fin d) → (Fin n → EuclideanSpace ℝ (Fin d)) → Fin d → ℝ

/-- The (pseudo) metric (6) of a scale vector `sv`:
`ρ(u, v) = (∑_{j : sv j > 0} ((u_j − v_j)/sv_j)²)^{1/2}`; coordinates with `sv j ≤ 0` are omitted.
`ρₙ` at the data `(x, xs)` is `rho (s n x xs)`. -/
noncomputable def rho {d : ℕ} (sv : Fin d → ℝ) (u v : EuclideanSpace ℝ (Fin d)) : ℝ :=
  Real.sqrt (∑ j ∈ Finset.univ.filter (fun j => 0 < sv j), ((u j - v j) / sv j) ^ 2)

/-- `ν` of (8) (p. 600): `1 + #{l ≠ i : ρ(X_l, X) < ρ(X_i, X)}`, for the metric `rho sv`. -/
noncomputable def nnNu {d n : ℕ} (sv : Fin d → ℝ) (x : EuclideanSpace ℝ (Fin d))
    (xs : Fin n → EuclideanSpace ℝ (Fin d)) (i : Fin n) : ℕ :=
  1 + (Finset.univ.filter fun l => l ≠ i ∧ rho sv (xs l) x < rho sv (xs i) x).card

/-- `λ` of (8) (p. 600): `1 + #{l ≠ i : ρ(X_l, X) = ρ(X_i, X)}`, for the metric `rho sv`. -/
noncomputable def nnLam {d n : ℕ} (sv : Fin d → ℝ) (x : EuclideanSpace ℝ (Fin d))
    (xs : Fin n → EuclideanSpace ℝ (Fin d)) (i : Fin n) : ℕ :=
  1 + (Finset.univ.filter fun l => l ≠ i ∧ rho sv (xs l) x = rho sv (xs i) x).card

/-- The nearest neighbor probability weight function (8) associated with coefficients `c` and scales `s`
(pp. 599–600): `W_{n,i+1}(x) = (c_{n,ν} + ⋯ + c_{n,ν+λ−1}) / λ`, ties in `ρₙ` being averaged over the tied
ranks. **The coefficients keep the paper's 1-based index**: `c n m` is `c_{n,m}` for `m ≥ 1`; `c n 0` is
never read (`ν ≥ 1`). The StoneRegression.Criterion.sample index `i : Fin n` is 0-based and stands for the paper's `i + 1`. -/
noncomputable def nnWeights {d : ℕ} (c : ℕ → ℕ → ℝ) (s : ScaleSeq d) : StoneRegression.Criterion.WeightSeq d :=
  fun n x xs i =>
    (∑ m ∈ Finset.Ico (nnNu (s n x xs) x xs i) (nnNu (s n x xs) x xs i + nnLam (s n x xs) x xs i), c n m) /
      (nnLam (s n x xs) x xs i : ℝ)

/-- A coefficient row `c_n` (p. 599): `c_{n1} ≥ ⋯ ≥ c_{nn} ≥ 0`, `c_{ni} = 0` for `i > n`, and
`c_{n1} + ⋯ + c_{nn} = 1` (1-based index). -/
def IsCoeffRow (c : ℕ → ℕ → ℝ) (n : ℕ) : Prop :=
  (∀ i j, 1 ≤ i → i ≤ j → j ≤ n → c n j ≤ c n i) ∧ 0 ≤ c n n ∧ (∀ i, n < i → c n i = 0) ∧
    ∑ i ∈ Finset.Icc 1 n, c n i = 1

/-- "The `j`th coordinate of `X` has a nondegenerate distribution" (p. 599): the law of `X_j` is not a
point mass. -/
def CoordNondeg {d : ℕ} (μ : Measure (EuclideanSpace ℝ (Fin d))) (j : Fin d) : Prop :=
  ∀ t : ℝ, μ {x | x j = t} < 1

/-- Boundedness in probability (p. 598): `lim_{M→∞} limsupₙ P(|Zₙ| ≥ M) = 0` (the `limsup` in `ℝ≥0∞`). -/
def BoundedInProb {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (Z : ℕ → Ω → ℝ) : Prop :=
  Tendsto (fun M : ℝ => limsup (fun n => P {ω | M ≤ |Z n ω|}) atTop) atTop (𝓝 0)

/-- Condition (7) with constants `a, b` (p. 599), read for all points: whenever `n ≥ 1`, `1 ≤ i ≤ n`,
`1 ≤ j ≤ d` and the `j`th coordinates of `x₁, …, xₙ` are not all equal,
`a·s_{nj}(xᵢ, x₁, …, x, …, xₙ) ≤ s_{nj}(x, x₁, …, xₙ) ≤ b·s_{nj}(xᵢ, x₁, …, x, …, xₙ)`.
`(xs i, Function.update xs i x)` is the sequence with `x` and `xᵢ` interchanged. -/
def Cond7 {d : ℕ} (s : ScaleSeq d) (a b : ℝ) : Prop :=
  ∀ n, 1 ≤ n → ∀ (x : EuclideanSpace ℝ (Fin d)) (xs : Fin n → EuclideanSpace ℝ (Fin d)) (i : Fin n)
    (j : Fin d), (∃ k l, xs k j ≠ xs l j) →
      a * s n (xs i) (Function.update xs i x) j ≤ s n x xs j ∧
        s n x xs j ≤ b * s n (xs i) (Function.update xs i x) j

/-- A regular sequence of scales with constants `0 < a ≤ b` (p. 599): each `s n` is Borel (added,
disclosed) and nonnegative; `P(s_{nj} > 0) → 1` for every coordinate with a nondegenerate distribution;
`s_{nj}/s_{nl}` is bounded in probability for every two such coordinates (real division, `0` where
`s_{nl} = 0`); and (7) holds. -/
def IsRegular {d : ℕ} (μ : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure μ] (s : ScaleSeq d)
    (a b : ℝ) : Prop :=
  (∀ n, Measurable (fun p : EuclideanSpace ℝ (Fin d) × (Fin n → EuclideanSpace ℝ (Fin d)) => s n p.1 p.2)) ∧
  (∀ n x xs j, 0 ≤ s n x xs j) ∧
  (∀ j, CoordNondeg μ j →
    Tendsto (fun n => StoneRegression.Criterion.xLaw μ {ω | 0 < s n (ω 0) (StoneRegression.Criterion.sample ω n) j}) atTop (𝓝 1)) ∧
  (∀ j l, CoordNondeg μ j → CoordNondeg μ l →
    BoundedInProb (StoneRegression.Criterion.xLaw μ) (fun n ω => s n (ω 0) (StoneRegression.Criterion.sample ω n) j / s n (ω 0) (StoneRegression.Criterion.sample ω n) l)) ∧
  0 < a ∧ a ≤ b ∧ Cond7 s a b

/-- `I_{n,t}(x)` (p. 599 and p. 611): the indices `i` such that fewer than `⌊t⌋` of the points `x₁, …, xₙ`
are strictly closer to `x` than `xᵢ` in the metric `rho sv`. For `k ≤ t < k + 1` this is `I_{nk}(x)`, and
for `0 ≤ t < 1` it is empty, which is `I_{n0}(x) = ∅`. -/
noncomputable def nearIdx {d n : ℕ} (sv : Fin d → ℝ) (x : EuclideanSpace ℝ (Fin d))
    (xs : Fin n → EuclideanSpace ℝ (Fin d)) (t : ℝ) : Finset (Fin n) :=
  Finset.univ.filter fun i => (Finset.univ.filter fun l => rho sv (xs l) x < rho sv (xs i) x).card < ⌊t⌋₊

/-- The family `𝒱(d, c)` (p. 612): sets `V ⊆ ℝᵈ` such that any two nonzero `u, v ∈ V` satisfy
`u·v > (1 − c²/2)‖u‖‖v‖`. The page defines it for `0 < c ≤ 1`. -/
def ConeFamily (d : ℕ) (c : ℝ) : Set (Set (EuclideanSpace ℝ (Fin d))) :=
  {V | ∀ u ∈ V, ∀ v ∈ V, u ≠ 0 → v ≠ 0 → (1 - c ^ 2 / 2) * (‖u‖ * ‖v‖) < inner ℝ u v}

/-- `β(d, c)` (p. 612): the minimum cardinality of a subcollection of `𝒱(d, c)` covering `ℝᵈ`, as an
`sInf` over `ℕ`. For `0 < c ≤ 1` the set is nonempty (the unit sphere is compact, so finitely many cones
cover `ℝᵈ`), hence the `sInf` is the page's minimum; this fact is not proved here and no statement
assumes it (were the set empty, the `sInf` would be `0`). -/
noncomputable def beta (d : ℕ) (c : ℝ) : ℕ :=
  sInf {k | ∃ V : Fin k → Set (EuclideanSpace ℝ (Fin d)), (∀ m, V m ∈ ConeFamily d c) ∧ (⋃ m, V m) = Set.univ}

/-- The swapped weights `U_{n,i+1}(x) = W_{n,i+1}(xᵢ₊₁, x₁, …, x, …, xₙ)` (p. 613): the query is the
`i`th StoneRegression.Criterion.sample point and `x` takes its slot, both in the weights and in the scales. -/
def swapW {d : ℕ} (W : StoneRegression.Criterion.WeightSeq d) : StoneRegression.Criterion.WeightSeq d :=
  fun n x xs i => W n (xs i) (Function.update xs i x) i

/-- Coordinatewise scaling `(coordScale bv u)_j = bv_j · u_j` (Proposition 10's `ũ`, `ṽ`). -/
noncomputable def coordScale {d : ℕ} (bv : Fin d → ℝ) (u : EuclideanSpace ℝ (Fin d)) :
    EuclideanSpace ℝ (Fin d) :=
  WithLp.toLp 2 (fun j => bv j * u j)

end StoneRegression.NearestNeighbor


