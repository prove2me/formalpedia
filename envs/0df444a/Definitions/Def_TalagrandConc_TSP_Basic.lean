-- Prove2me | Definitions.Def_TalagrandConc_TSP_Basic
-- name    : TalagrandConc_TSP_Basic
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T15:43:34.075684+00:00
-- url     : https://prove2.me/theorems/a23708d1-5c5e-403a-b587-f09b31afb96a
-- title:
--   The Euclidean sample, dyadic squares, tour length, and isolation weight
-- statement:
--   A point is a pair of coordinates in $[0,1]$, with Euclidean distance
--   $$d(x,y)=\sqrt{(x_1-y_1)^2+(x_2-y_2)^2}.$$
--   A finite set $F$ of points has tour length $T(F)$, the minimum total Euclidean length of a closed tour visiting all points in $F$. The sample $X_1,\ldots,X_N$ consists of independent uniform points in the square; $F=\{X_1,\ldots,X_N\}$ keeps distinct locations. A median $M$ of $L(F)$ leaves probability at least one half on each side.
--
--   At level $k$, dyadic squares have side $2^{-k}$. The count $m_k$ is the number of those squares containing at most $N2^{-2k-6}$ points of $F$. Here $k_0$ is the largest level with $2^{2k_0}\le N$; $k_1$ follows criterion (11.1.9) with Poisson intensity $N/8$. The isolation weight $\alpha(x)$ is the largest scale $2^{-k}$, $k_1\le k\le k_0$, whose assigned square contains at most $N2^{-2k-7}$ points, or $2^{-k_0}$ if no scale qualifies.
--
--   These definitions state the geometric quantities used by the chapter's concentration argument. The local regularity condition on a functional $L$ says, for every level-$k$ square $C$, finite $F$ and finite $G\subseteq C$, that if $F$ has a point within $2^{-k+2}$ of $C$, then
--   $$L(F)\le L(F\cup G)\le L(F)+K2^{-k}\sqrt{|G|}.$$
--
--   **Formalization Note** The point-to-square assignment uses half-open cells at grid lines and puts coordinate $1$ in the last cell. Tour costs use the $\ell^2$ metric. The probability law is a product of coordinatewise uniform measures. Tour length uses the published `MetricTSP.tspOpt` model.
-- source:
--   Talagrand, Concentration of measure and isoperimetric inequalities in product spaces, Publ. Math. IHÉS 81 (1995), pp. 170–176, §11.1, (11.1.9), (11.1.13), §11.2, (11.2.1), and p. 176 definition of α

import Mathlib
import Definitions.Def_MetricTSP_model

namespace TalagrandConc.TSP

open MeasureTheory

/-- Points of the unit square, with both coordinates in `[0,1]`. -/
abbrev Point := Fin 2 → unitInterval

/-- Euclidean distance, rather than the supremum norm on function spaces. -/
noncomputable def edist (x y : Point) : ℝ :=
  Real.sqrt (∑ i : Fin 2, ((x i : ℝ) - (y i : ℝ)) ^ 2)

/-- The shortest closed Euclidean tour through a finite set of points. -/
noncomputable def tourLength (F : Finset Point) : ℝ :=
  let e : Fin (Fintype.card F) ≃ F := (Fintype.equivFin F).symm
  MetricTSP.tspOpt (fun i j => edist (e i).1 (e j).1)

/-- The set of distinct locations among the `N` sampled points. -/
noncomputable def sampleSet {N : ℕ} (x : Fin N → Point) : Finset Point :=
  Finset.univ.image x

/-- Independent uniform points of the unit square. -/
noncomputable def sampleLaw (N : ℕ) : Measure (Fin N → Point) :=
  Measure.pi (fun _ : Fin N => Measure.pi (fun _ : Fin 2 => (volume : Measure unitInterval)))

/-- A median: each closed half-line from `M` has probability at least one half. -/
def IsMedian {N : ℕ} (L : Finset Point → ℝ) (M : ℝ) : Prop :=
  (1 / 2 : ENNReal) ≤ sampleLaw N {x | L (sampleSet x) ≤ M} ∧
  (1 / 2 : ENNReal) ≤ sampleLaw N {x | M ≤ L (sampleSet x)}

/-- A level-`k` dyadic square is indexed by two integers in `0,...,2^k-1`. -/
abbrev Grid (k : ℕ) := Fin 2 → Fin (2 ^ k)

/-- The closed dyadic square of side `2^{-k}`. Shared edges are assigned to
one square by `squareIndex` when a single containing square is needed. -/
def dyadicSquare (k : ℕ) (c : Grid k) : Set Point :=
  {x | ∀ i : Fin 2,
    (c i).val * (2 : ℝ) ^ (-(k : ℤ)) ≤ (x i : ℝ) ∧
    (x i : ℝ) ≤ ((c i).val + 1) * (2 : ℝ) ^ (-(k : ℤ))}

/-- The half-open cell containing `x`, with the right endpoint `1` put in the
last cell. This resolves the source's boundary ambiguity on a null set. -/
noncomputable def squareIndex (k : ℕ) (x : Point) : Grid k :=
  fun i => Fin.ofNat (2 ^ k)
    (min (Nat.floor ((2 : ℝ) ^ k * (x i : ℝ))) (2 ^ k - 1))

/-- Number of distinct sample points in one dyadic square. -/
noncomputable def occupancy (F : Finset Point) (k : ℕ) (c : Grid k) : ℕ :=
  by classical exact (F.filter (fun x => x ∈ dyadicSquare k c)).card

/-- Number of squares at level `k` meeting the low-occupancy condition
`(11.1.13)`. -/
noncomputable def holeCount (N : ℕ) (F : Finset Point) (k : ℕ) : ℕ :=
  by classical exact (Finset.univ.filter (fun c : Grid k =>
    (occupancy F k c : ℝ) ≤ (N : ℝ) * (2 : ℝ) ^ (-(2 * k + 6 : ℕ) : ℤ))).card

/-- `k₀` of Proposition 11.1.4, the largest `k` with `2^{2k} ≤ N`. -/
def k0 (N : ℕ) : ℕ := Nat.log 4 N

/-- The criterion `(11.1.9)` with `μ=N/8`, used to choose `k₁` in the
proof of Proposition 11.1.4. -/
def k1Criterion (N : ℕ) (t : ℝ) (k : ℕ) : Prop :=
  Real.exp 2 * (2 : ℝ) ^ (2 * k) *
    Real.exp (-((N : ℝ) / 8) * (2 : ℝ) ^ (-(2 * k + 1 : ℕ) : ℤ)) ≤ t ^ 2

/-- `k₁` is the largest admissible level through `k₀`; `0` is its value
when no level is admissible, a case excluded in the propositions using it. -/
noncomputable def k1 (N : ℕ) (t : ℝ) : ℕ :=
  by classical exact ((Finset.range (k0 N + 1)).filter (k1Criterion N t)).sup id

/-- The set of levels where the square containing `x` has very few
sample points, as on p. 176. -/
noncomputable def sparseScales (N : ℕ) (t : ℝ) (F : Finset Point) (x : Point) : Set ℝ :=
  {a | ∃ k : ℕ, k1 N t ≤ k ∧ k ≤ k0 N ∧
    (occupancy F k (squareIndex k x) : ℝ) ≤
      (N : ℝ) * (2 : ℝ) ^ (-(2 * k + 7 : ℕ) : ℤ) ∧
    a = (2 : ℝ) ^ (-(k : ℤ))}

/-- The isolation weight `α(x)` of p. 176: the largest admissible scale,
or `2^{-k₀}` if none is admissible. -/
noncomputable def alpha (N : ℕ) (t : ℝ) (F : Finset Point) (x : Point) : ℝ :=
  by
    classical
    exact if (sparseScales N t F x).Nonempty then
      sSup (sparseScales N t F x)
    else (2 : ℝ) ^ (-(k0 N : ℤ))

/-- The regularity condition `(11.2.1)`, including monotonicity. -/
def Regular (K : ℝ) (L : Finset Point → ℝ) : Prop :=
  ∀ (k : ℕ) (_ : 1 ≤ k) (F G : Finset Point) (c : Grid k),
    (∀ x ∈ G, x ∈ dyadicSquare k c) →
    (∃ x ∈ F, ∃ y ∈ dyadicSquare k c,
      edist x y ≤ (2 : ℝ) ^ (-(k : ℤ) + 2)) →
    L F ≤ L (F ∪ G) ∧
      L (F ∪ G) ≤ L F + K * (2 : ℝ) ^ (-(k : ℤ)) * Real.sqrt G.card

end TalagrandConc.TSP


