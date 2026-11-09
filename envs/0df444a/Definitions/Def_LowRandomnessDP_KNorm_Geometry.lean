-- Prove2me | Definitions.Def_LowRandomnessDP_KNorm_Geometry
-- name    : LowRandomnessDP_KNorm_Geometry
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T11:00:47.373611+00:00
-- url     : https://prove2.me/theorems/3e5099bc-c1e0-4503-b062-1f5fa7fcb073
-- title:
--   Absorbing disks, K-norms and multi-scale secluded partitions
-- statement:
--   Work in $\mathbb R^d$ with its usual topology. An admissible body $K$ is compact, convex, symmetric about zero and absorbing: every vector belongs to $tK$ for some $t>0$. Its Minkowski gauge is
--
--   $$\|x\|_K=\inf\{t>0:x\in tK\}.$$
--
--   A cell partition covers all space by nonempty pairwise disjoint cells and attaches to each cell a representative in that cell. A $(k,\gamma;\rho)$-secluded partition has representative radius at most $\rho$ and at most $k$ cells intersecting each closed norm ball of radius $\gamma\rho$. A multi-scale secluded partition uses the same partition and representatives at every reciprocal scale $1/\ell$, $1\le\ell\le d$. The distance $\Delta_P(v)$ is the infimum of the norm distance to points of the cell, and $\mathcal P_{<\gamma}(v)$ uses the strict inequality $\Delta_P(v)<\gamma\rho$.
--
--   These definitions provide the geometry used by Algorithm 2. Cell distance is finite because cells are nonempty and the distances are bounded below by zero. Cells need not be closed or measurable. Finite-subset cardinal bounds express actual cardinal upper bounds without a default value for infinite sets. Compactness implies the source's exclusion of a nontrivial subspace. Positive-dilation and nonnegative-dilation gauge infima coincide on these disks, including at zero. Euclidean balls use the coordinate sum of squares, not the default coordinate sup norm.
-- source:
--   Surendra Ghentiyala, Pritish Kamath, Ravi Kumar, Pasin Manurangsi, STOC 2027 submission #514 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/514.pdf, §2.1 equation (1), Definition 1.3 (PDF 4 / printed 2), Definition 1.5 (PDF 5,8 / printed 3,6), §3.3 (PDF 14 / printed 12)

import Mathlib

set_option autoImplicit false

noncomputable section

namespace LowRandomnessDP.KNorm

abbrev Vec (d : ℕ) := Fin d → ℝ

/-- Section 2.1 and footnote 5: compact, convex, zero-symmetric, absorbing disk.
Compactness already excludes a nontrivial linear subspace. -/
def IsBody {d : ℕ} (K : Set (Vec d)) : Prop :=
  IsCompact K ∧ Convex ℝ K ∧ (∀ x, x ∈ K ↔ -x ∈ K) ∧
    ∀ x, ∃ t : ℝ, 0 < t ∧ ∃ z ∈ K, x = t • z

/-- Equation (1); Mathlib takes the infimum over positive dilations, which gives the
same gauge as the source's nonnegative dilations for every absorbing disk. -/
def kNorm {d : ℕ} (K : Set (Vec d)) (x : Vec d) : ℝ := gauge K x

/-- Euclidean balls, independent of the default sup norm on coordinate functions. -/
def euclideanBall (d : ℕ) (r : ℝ) : Set (Vec d) :=
  {x | Real.sqrt (∑ j, (x j) ^ 2) ≤ r}

/-- A finite cardinal bound, expressed by bounds on every finite subset. This never
assigns cardinal zero to an infinite collection. -/
def CountLe {ι : Type} (S : Set ι) (b : ℝ) : Prop :=
  ∀ t : Finset ι, (∀ i ∈ t, i ∈ S) → (t.card : ℝ) ≤ b

/-- An actual partition, with a representative belonging to each nonempty cell. -/
structure CellPartition (d : ℕ) where
  cells : Set (Set (Vec d))
  nonempty : ∀ c ∈ cells, c.Nonempty
  covers_uniquely : ∀ x : Vec d, ∃! c : Set (Vec d), c ∈ cells ∧ x ∈ c
  representative : cells → Vec d
  representative_mem : ∀ c, representative c ∈ c.val

abbrev CellPartition.Cell {d : ℕ} (P : CellPartition d) := P.cells

/-- Cells intersecting a closed K-norm ball, Definition 1.3. -/
def intersectingCells {d : ℕ} (K : Set (Vec d)) (P : CellPartition d)
    (v : Vec d) (r : ℝ) : Set P.Cell :=
  {c | ∃ x ∈ c.val, kNorm K (x - v) ≤ r}

def IsSecluded {d : ℕ} (K : Set (Vec d)) (P : CellPartition d)
    (k : ℕ) (γ ρ : ℝ) : Prop :=
  0 < ρ ∧ (∀ c : P.Cell, ∀ x ∈ c.val, kNorm K (P.representative c - x) ≤ ρ) ∧
    ∀ v, CountLe (intersectingCells K P v (γ * ρ)) k

/-- The SAME partition and representative map for all one-based scales 1,...,d. -/
def IsMSSP {d : ℕ} (K : Set (Vec d)) (P : CellPartition d)
    (k : ℕ → ℕ) (ρ : ℝ) : Prop :=
  0 < d ∧ 0 < ρ ∧ ∀ ℓ : ℕ, 1 ≤ ℓ → ℓ ≤ d →
    0 < k ℓ ∧ IsSecluded K P (k ℓ) (1 / (ℓ : ℝ)) ρ

/-- Infimal distance, not distance to the representative; cells need not be closed. -/
def cellDistance {d : ℕ} (K : Set (Vec d)) (P : CellPartition d)
    (c : P.Cell) (v : Vec d) : ℝ :=
  sInf ((fun x => kNorm K (v - x)) '' c.val)

/-- The strict sublevel collection in Section 3.3. -/
def nearCells {d : ℕ} (K : Set (Vec d)) (P : CellPartition d)
    (ρ γ : ℝ) (v : Vec d) : Set P.Cell :=
  {c | cellDistance K P c v < γ * ρ}

/-- Uniform quantitative envelope supplied by the proof on PDF 9--10. -/
def RateBound (C : ℝ) (d : ℕ) (k : ℕ → ℕ) : Prop :=
  ∀ ℓ : ℕ, 1 ≤ ℓ → ℓ ≤ d →
    (k ℓ : ℝ) ≤ C * d * Real.log (d + 1) * Real.exp ((d : ℝ) / ℓ)

end LowRandomnessDP.KNorm


