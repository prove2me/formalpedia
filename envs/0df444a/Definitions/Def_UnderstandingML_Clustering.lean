-- Prove2me | Definitions.Def_UnderstandingML_Clustering
-- name    : UnderstandingML_Clustering
-- status  : Definition
-- author  : @naimengye
-- created : 2026-09-24T05:16:00.554952+00:00
-- url     : https://prove2.me/theorems/a20aa2c6-8766-45a1-82b2-94115e812869
-- title:
--   Chapter 22: partitions and nearest-center assignments, centroids and the k-means objective, the graph Laplacian and RatioCut, Kleinberg's axioms (SI, Richness, Consistency), farthest-first centers
-- statement:
--   Chapter 22 of Shalev-Shwartz and Ben-David. `IsPartition S C` says $C = (C_1, \dots, C_k)$ partitions $S$ (each $C_i \subseteq S$, every point of $S$ in exactly one $C_i$); `IsNearestAssignment μ C` says every $x \in C_i$ has $d(x, \mu_i) \le d(x, \mu_j)$ for all $j$ (ties arbitrary). **k-means (§22.2):** `centroid C` $= \frac1{|C|}\sum_{x \in C}x$, `centerCost C μ` $= \sum_i\sum_{x \in C_i}\|x - \mu_i\|^2$ and `kmeansObjective C` $= \sum_i\sum_{x \in C_i}\|x - \mu(C_i)\|^2$ (22.3). **Spectral clustering (§22.3):** `degreeMatrix W` $= \operatorname{diag}(\sum_j W_{i,j})$, `laplacian W` $= D - W$ (Definition 22.2), `ratioCut W C` $= \sum_i \frac1{|C_i|}\sum_{r \in C_i, s \notin C_i} W_{r,s}$, and `clusterIndicator C` is the matrix $H_{i,j} = |C_j|^{-1/2}\mathbb{1}[i \in C_j]$ of Lemma 22.3. **Kleinberg's axioms (§22.5):** a `Dissimilarity X` is symmetric, zero on the diagonal and positive on distinct points; `Dissimilarity.scale` is $\alpha d$; for a clustering function $F$ from dissimilarities to partitions (`Setoid X`), `ScaleInvariant F` ($F(\alpha d) = F(d)$), `Rich F` (every partition is some $F(d)$) and `Consistent F` (shrinking within-cluster and expanding between-cluster dissimilarities does not change $F$). **k-diam (Exercise 3):** `IsFarthestFirst μ` says $\mu_1$ is arbitrary and each $\mu_j$ maximizes $\min_{i<j} d(x, \mu_i)$.
-- source:
--   Shalev-Shwartz and Ben-David, Understanding Machine Learning: From Theory to Algorithms, Cambridge University Press 2014, doi:10.1017/CBO9781107298019, §22 p. 309 (the clustering model), §22.2 pp. 312-314 (k-means objective, (22.1)-(22.3), the k-means algorithm), §22.3 pp. 315-316 (Definition 22.2, RatioCut, the matrix H), §22.5 pp. 318-319 (Scale Invariance, Richness, Consistency), §22.8 p. 321 (Exercise 3)

import Definitions.Def_UnderstandingML_Linear
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Topology.MetricSpace.Bounded

/-!
# Shalev-Shwartz and Ben-David, *Understanding Machine Learning*, Chapter 22: clustering

Shalev-Shwartz and Ben-David, *Understanding Machine Learning: From Theory to Algorithms*,
Cambridge University Press 2014, doi:10.1017/CBO9781107298019, §22.2, §22.3, §22.5, §22.8.

**The clustering model (p. 309).** Input: a finite set `X` with a distance (dissimilarity)
function `d : X × X → ℝ₊`, symmetric with `d(x, x) = 0`, and possibly a number `k` of clusters.
Output: a partition `C = (C₁, …, C_k)` of `X`.

**k-means (§22.2, pp. 312–313).** For `X ⊆ ℝⁿ` and a partition `C₁, …, C_k`, the centroid of
`Cᵢ` is `μ(Cᵢ) = (1/|Cᵢ|) ∑_{x ∈ Cᵢ} x = argmin_μ ∑_{x ∈ Cᵢ} ‖x − μ‖²`, and the k-means
objective is `G(C₁, …, C_k) = ∑ᵢ ∑_{x ∈ Cᵢ} ‖x − μ(Cᵢ)‖² = min_{μ₁, …, μ_k} ∑ᵢ ∑_{x ∈ Cᵢ} ‖x − μᵢ‖²`
(22.1)–(22.3). The **k-means algorithm** alternates `Cᵢ = {x : i = argminⱼ ‖x − μⱼ‖}` (ties
arbitrary) and `μᵢ = μ(Cᵢ)`.

**Spectral clustering (§22.3, pp. 315–316).** For a similarity matrix `W ∈ ℝ^{m×m}`, the degree
matrix `D = diag(∑ⱼ W_{i,j})`, the unnormalized graph Laplacian `L = D − W` (Definition 22.2),
`RatioCut(C₁, …, C_k) = ∑ᵢ (1/|Cᵢ|) ∑_{r ∈ Cᵢ, s ∉ Cᵢ} W_{r,s}`, and the matrix
`H_{i,j} = |Cⱼ|^{−1/2} 𝟙[i ∈ Cⱼ]` of Lemma 22.3.

**Kleinberg's axioms (§22.5, pp. 318–319).** A clustering function `F` takes a finite domain
with a dissimilarity function and returns a partition. **Scale Invariance:** `F(X, αd) = F(X, d)`
for `α > 0`. **Richness:** every partition of `X` is `F(X, d)` for some `d`. **Consistency:** if
`d'` shrinks within-cluster distances and expands between-cluster distances of `F(X, d)`, then
`F(X, d') = F(X, d)`.

**k-diam (Exercise 3, p. 321).** `G_{k−diam}(C) = maxⱼ diam(Cⱼ)`, and the farthest-first
centers `μ₁ = x`, `μⱼ = argmax_x min_{i<j} d(x, μᵢ)`, with clusters by nearest center.

**Conventions.** Clusterings of a finite type are `Setoid`s (the relation "same cluster") in
the axiomatic section and `Fin k`-indexed finsets elsewhere; a partition of `S` is a family of
subsets of `S` covering each point exactly once. Dissimilarities are positive on distinct
points, as in Kleinberg (2003); this is what the proof of Theorem 22.4 uses to scale `d₂`
above `d₁`. The centroid of an empty cluster is `0`, harmless since it is never summed over.
Nearest-center assignments and farthest-first centers are predicates, so ties are broken
arbitrarily.
-/

open MeasureTheory

namespace UnderstandingML

/-! ### Partitions and nearest-center assignments -/

section Partitions

variable {X : Type*}

/-- `C = (C₁, …, C_k)` is a **partition** of `S`: each `Cᵢ ⊆ S`, and every point of `S` lies in
exactly one `Cᵢ` (p. 309). -/
def IsPartition {k : ℕ} (S : Finset X) (C : Fin k → Finset X) : Prop :=
  (∀ i, C i ⊆ S) ∧ ∀ x ∈ S, ∃! i, x ∈ C i

/-- `C` assigns every point to a nearest center among `μ₁, …, μ_k`:
`x ∈ Cᵢ → d(x, μᵢ) ≤ d(x, μⱼ)` for all `j` (ties broken arbitrarily; p. 313, p. 321). -/
def IsNearestAssignment [MetricSpace X] {k : ℕ} (μ : Fin k → X) (C : Fin k → Finset X) : Prop :=
  ∀ i, ∀ x ∈ C i, ∀ j, dist x (μ i) ≤ dist x (μ j)

end Partitions

/-! ### k-means -/

section KMeans

variable {n : ℕ}

/-- The **centroid** `μ(C) = (1/|C|) ∑_{x ∈ C} x` of a finite set of points (p. 314). -/
noncomputable def centroid (C : Finset (Vec n)) : Vec n := (C.card : ℝ)⁻¹ • ∑ x ∈ C, x

/-- The cost `∑ᵢ ∑_{x ∈ Cᵢ} ‖x − μᵢ‖²` of a clustering with prescribed centers (22.1)–(22.2). -/
noncomputable def centerCost {k : ℕ} (C : Fin k → Finset (Vec n)) (μ : Fin k → Vec n) : ℝ :=
  ∑ i, ∑ x ∈ C i, ‖x - μ i‖ ^ 2

/-- The **k-means objective** `G(C₁, …, C_k) = ∑ᵢ ∑_{x ∈ Cᵢ} ‖x − μ(Cᵢ)‖²` (22.3). -/
noncomputable def kmeansObjective {k : ℕ} (C : Fin k → Finset (Vec n)) : ℝ :=
  centerCost C (fun i ↦ centroid (C i))

end KMeans

/-! ### Graph Laplacian and RatioCut -/

section Spectral

variable {m : ℕ}

/-- The **degree matrix** `D = diag(∑ⱼ W_{i,j})` (Definition 22.2). -/
noncomputable def degreeMatrix (W : Matrix (Fin m) (Fin m) ℝ) : Matrix (Fin m) (Fin m) ℝ :=
  Matrix.diagonal (fun i ↦ ∑ j, W i j)

/-- The **unnormalized graph Laplacian** `L = D − W` (Definition 22.2). -/
noncomputable def laplacian (W : Matrix (Fin m) (Fin m) ℝ) : Matrix (Fin m) (Fin m) ℝ :=
  degreeMatrix W - W

/-- `RatioCut(C₁, …, C_k) = ∑ᵢ (1/|Cᵢ|) ∑_{r ∈ Cᵢ, s ∉ Cᵢ} W_{r,s}` (p. 315). -/
noncomputable def ratioCut {k : ℕ} (W : Matrix (Fin m) (Fin m) ℝ) (C : Fin k → Finset (Fin m)) :
    ℝ :=
  ∑ i, ((C i).card : ℝ)⁻¹ * ∑ r ∈ C i, ∑ s ∈ (C i)ᶜ, W r s

/-- The matrix `H ∈ ℝ^{m×k}` with `H_{i,j} = |Cⱼ|^{−1/2} 𝟙[i ∈ Cⱼ]` (Lemma 22.3). -/
noncomputable def clusterIndicator {k : ℕ} (C : Fin k → Finset (Fin m)) : Matrix (Fin m) (Fin k) ℝ :=
  fun i j ↦ if i ∈ C j then 1 / Real.sqrt ((C j).card) else 0

end Spectral

/-! ### Kleinberg's axioms -/

section Kleinberg

variable {X : Type*}

/-- A **dissimilarity function** over `X` (p. 309, Kleinberg 2003): symmetric, zero on the
diagonal and positive on distinct points. -/
structure Dissimilarity (X : Type*) where
  d : X → X → ℝ
  symm : ∀ x y, d x y = d y x
  self : ∀ x, d x x = 0
  pos : ∀ x y, x ≠ y → 0 < d x y

/-- The scaled dissimilarity `αd` for `α > 0` (Scale Invariance, p. 318). -/
def Dissimilarity.scale (D : Dissimilarity X) (α : ℝ) (hα : 0 < α) : Dissimilarity X where
  d := fun x y ↦ α * D.d x y
  symm := fun x y ↦ by simp [D.symm x y]
  self := fun x ↦ by simp [D.self x]
  pos := fun x y hxy ↦ mul_pos hα (D.pos x y hxy)

/-- **Scale Invariance (SI)** (p. 318): `F(X, αd) = F(X, d)` for every `α > 0`. -/
def ScaleInvariant (F : Dissimilarity X → Setoid X) : Prop :=
  ∀ (D : Dissimilarity X) (α : ℝ) (hα : 0 < α), F (D.scale α hα) = F D

/-- **Richness (Ri)** (p. 318): every partition of `X` is the output for some dissimilarity. -/
def Rich (F : Dissimilarity X → Setoid X) : Prop :=
  ∀ s : Setoid X, ∃ D : Dissimilarity X, F D = s

/-- **Consistency (Co)** (p. 319): if `d'` does not increase within-cluster dissimilarities and
does not decrease between-cluster dissimilarities of `F(X, d)`, then `F(X, d') = F(X, d)`. -/
def Consistent (F : Dissimilarity X → Setoid X) : Prop :=
  ∀ D D' : Dissimilarity X,
    (∀ x y, (F D).r x y → D'.d x y ≤ D.d x y) →
    (∀ x y, ¬ (F D).r x y → D.d x y ≤ D'.d x y) → F D' = F D

end Kleinberg

/-! ### k-diam and farthest-first traversal -/

section KDiam

variable {X : Type*} [MetricSpace X]

/-- The centers `μ₁, …, μ_k` are a **farthest-first traversal** (Exercise 3, p. 321): `μ₁` is
arbitrary and each `μⱼ` maximizes `min_{i<j} d(x, μᵢ)` over `x ∈ X` (ties arbitrary). -/
def IsFarthestFirst {k : ℕ} (μ : Fin k → X) : Prop :=
  ∀ (j : Fin k) (x : X),
    (⨅ i : {i : Fin k // i < j}, dist x (μ i)) ≤ ⨅ i : {i : Fin k // i < j}, dist (μ j) (μ i)

end KDiam

end UnderstandingML


