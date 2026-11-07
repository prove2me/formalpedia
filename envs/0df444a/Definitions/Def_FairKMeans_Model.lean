-- Prove2me | Definitions.Def_FairKMeans_Model
-- name    : FairKMeans_Model
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T22:29:53.966337+00:00
-- url     : https://prove2.me/theorems/0029f462-01a5-414e-9afe-de2a1c5666c6
-- title:
--   Fair $k$-means: instances, fair fractional assignments, cost, $\mathrm{OPT}_{\mathrm{frac}}$ and $\mathrm{OPT}$
-- statement:
--   An **instance of fair $k$-means** consists of $n$ points $P=(p_1,\dots,p_n)$ of $\mathbb R^d$ (an indexed family, so points at the same location are distinguished), $m$ groups $P^{(1)},\dots,P^{(m)}\subseteq P$, which may overlap, an integer $k\ge 1$, and vectors $\alpha,\beta\in[0,1]^m$ of upper and lower bounds.
--
--   For a family $S=(s_1,\dots,s_r)$ of centers, an **assignment matrix** $\phi_S\in\mathbb R^{n\times r}$ has nonnegative entries and rows summing to one; it is **integral** if all entries are $0$ or $1$. The cluster of the center $s$ has weight $w(s)=\sum_{p\in P}\phi_S(p,s)$, of which group $i$ contributes $w^{(i)}(s)=\sum_{p\in P^{(i)}}\phi_S(p,s)$. The assignment is **$(\alpha,\beta)$-fair** if
--
--   $$\beta_i\,w(s)\le w^{(i)}(s)\le \alpha_i\,w(s)\qquad\text{for all } s\in S,\ i\in[m],$$
--
--   and its cost is $\mathrm{Cost}(P,S,\phi_S)=\sum_{p\in P}\sum_{s\in S}\phi_S(p,s)\|p-s\|^2$. An optimal solution of the **fair assignment LP** of $S$ is a fair fractional assignment to $S$ of minimum cost among all of them.
--
--   $\mathrm{OPT}_{\mathrm{frac}}$ is the infimum of the cost over all families of at most $k$ centers anywhere in $\mathbb R^d$ and all fair fractional assignments; $\mathrm{OPT}$ is the same infimum over fair integral assignments. The instance **has a fair solution** if some family of at most $k$ centers admits a fair fractional assignment; the paper assumes this throughout (p.19).
--
--   These objects carry every statement of the mission.
--
--   **Formalization Note** Center sets are indexed families `Fin s → E d`, duplicates allowed; merging equal centers adds their columns, which keeps fairness and integrality and leaves the cost unchanged, so the infima agree with the paper's. The optima are real infima of sets that are nonempty under the standing assumption and bounded below by $0$.
-- source:
--   Cheng–Mo–Song–Ding, A (3+ε)-Approximation for Fair k-Means and a Matching Lower Bound, arXiv:2609.07974 (held version, sha256 73e9312c…), Section 1.1 and Definition 1, pp.1–2 (PDF pp.3–4); Definitions 11–12, p.18 (PDF p.20); standing assumption, p.19 (PDF p.21)

import Mathlib

namespace FairKMeans

/-!
# Fair k-means: instances, assignments, fairness, cost, and the two optima

Cheng–Mo–Song–Ding, *A (3+ε)-Approximation for Fair k-Means and a Matching Lower Bound*,
arXiv:2609.07974 (held version, sha256 73e9312c…), Section 1.1 and Definition 1, pp.1–2
(PDF 3–4); Definitions 11–12, p.18 (PDF 20); standing assumption, p.19 (PDF 21).

**Formalization Note.** Points are an indexed family `Fin n → E d` (points at the same location
are distinguished, p.18). Groups are `Fin m → Finset (Fin n)` (they may overlap). A center set
is an indexed family `S : Fin s → E d`; duplicates are allowed. Merging equal centers sums their
columns, which keeps fairness and integrality and leaves the cost unchanged, so the infima below
equal the paper's. All input points have unit weight.
-/

/-- Euclidean space `ℝ^d`. -/
abbrev E (d : ℕ) : Type := EuclideanSpace ℝ (Fin d)

/-- An instance of fair k-means (p.1, PDF 3): `n` points of `ℝ^d`, `m` possibly overlapping
groups, an integer `k ≥ 1`, and upper and lower bounds `α, β ∈ [0,1]^m`. Nothing else is
assumed (in particular not `β ≤ α`, not `n ≥ 1`, not distinct points). -/
structure Instance (d n m : ℕ) where
  /-- The input points `P`. -/
  pts : Fin n → E d
  /-- The groups `P⁽¹⁾, …, P⁽ᵐ⁾ ⊆ P`. -/
  grp : Fin m → Finset (Fin n)
  /-- The number of centers. -/
  k : ℕ
  one_le_k : 1 ≤ k
  /-- Upper bounds `α`. -/
  α : Fin m → ℝ
  /-- Lower bounds `β`. -/
  β : Fin m → ℝ
  α_mem : ∀ i, α i ∈ Set.Icc (0 : ℝ) 1
  β_mem : ∀ i, β i ∈ Set.Icc (0 : ℝ) 1

variable {d n m : ℕ}

/-- An assignment matrix (p.1): nonnegative entries, every row sums to one. -/
def IsAssignment {s : ℕ} (φ : Fin n → Fin s → ℝ) : Prop :=
  (∀ p j, 0 ≤ φ p j) ∧ ∀ p, ∑ j, φ p j = 1

/-- An integral assignment matrix (p.1): all entries are `0` or `1`. -/
def IsIntegral {s : ℕ} (φ : Fin n → Fin s → ℝ) : Prop :=
  ∀ p j, φ p j = 0 ∨ φ p j = 1

/-- The weight `w(s) = ∑_p φ(p,s)` of the cluster of center `j` (p.2, (11) with unit weights). -/
def clusterWeight {s : ℕ} (φ : Fin n → Fin s → ℝ) (j : Fin s) : ℝ :=
  ∑ p, φ p j

/-- The weight `w⁽ⁱ⁾(s) = ∑_{p ∈ P⁽ⁱ⁾} φ(p,s)` of group `i` in the cluster of `j` (p.2). -/
def groupWeight {s : ℕ} (I : Instance d n m) (φ : Fin n → Fin s → ℝ) (i : Fin m) (j : Fin s) :
    ℝ :=
  ∑ p ∈ I.grp i, φ p j

/-- `(α, β)`-fairness (p.2; Definition 11, (12), p.18): `β_i w(s) ≤ w⁽ⁱ⁾(s) ≤ α_i w(s)` for
every center `s` and every group `i`. -/
def IsFair {s : ℕ} (I : Instance d n m) (φ : Fin n → Fin s → ℝ) : Prop :=
  ∀ (j : Fin s) (i : Fin m), I.β i * clusterWeight φ j ≤ groupWeight I φ i j ∧
    groupWeight I φ i j ≤ I.α i * clusterWeight φ j

/-- The cost `Cost(P, S, φ_S) = ∑_p ∑_s φ_S(p,s) ‖p − s‖²` (p.2; (10) with unit weights). -/
noncomputable def cost {s : ℕ} (I : Instance d n m) (S : Fin s → E d) (φ : Fin n → Fin s → ℝ) :
    ℝ :=
  ∑ p, ∑ j, φ p j * ‖I.pts p - S j‖ ^ 2

/-- `φ` is an optimal solution of the fair assignment LP of `S` (Definition 12, p.18): a fair
fractional assignment of `P` to `S` of minimum cost among all fair fractional assignments. -/
def IsOptFairAssign {s : ℕ} (I : Instance d n m) (S : Fin s → E d) (φ : Fin n → Fin s → ℝ) :
    Prop :=
  IsAssignment φ ∧ IsFair I φ ∧
    ∀ ψ : Fin n → Fin s → ℝ, IsAssignment ψ → IsFair I ψ → cost I S φ ≤ cost I S ψ

/-- The standing assumption of p.19 (PDF 21), "the instance has a fair solution": some set of at
most `k` centers admits an `(α, β)`-fair fractional assignment. -/
def HasFairSolution (I : Instance d n m) : Prop :=
  ∃ s ≤ I.k, ∃ (S : Fin s → E d) (φ : Fin n → Fin s → ℝ), IsAssignment φ ∧ IsFair I φ

/-- `OPT_frac` (p.2): the infimum of `Cost(P, S, φ_S)` over all center sets with at most `k`
centers anywhere in `ℝ^d` and all `(α, β)`-fair fractional assignments. Under
`HasFairSolution` the set is nonempty, and it is bounded below by `0`. -/
noncomputable def OPTfrac (I : Instance d n m) : ℝ :=
  sInf {c : ℝ | ∃ s ≤ I.k, ∃ (S : Fin s → E d) (φ : Fin n → Fin s → ℝ),
    IsAssignment φ ∧ IsFair I φ ∧ cost I S φ = c}

/-- `OPT` (p.2): the optimal cost of the integral version, the infimum of the costs of
`(α, β)`-fair integral assignments to at most `k` centers (p.19 shows that a fair instance has an
integral fair solution, so the set is nonempty under `HasFairSolution`). -/
noncomputable def OPT (I : Instance d n m) : ℝ :=
  sInf {c : ℝ | ∃ s ≤ I.k, ∃ (S : Fin s → E d) (φ : Fin n → Fin s → ℝ),
    IsAssignment φ ∧ IsIntegral φ ∧ IsFair I φ ∧ cost I S φ = c}

end FairKMeans


