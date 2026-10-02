-- Prove2me | Definitions.Def_Disjunctive_GeneralDisjunctions_Basic
-- name    : Disjunctive_GeneralDisjunctions_Basic
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T16:57:50.415318+00:00
-- url     : https://prove2.me/theorems/31a07088-1e6c-4215-9b64-39c0a218500c
-- title:
--   Extreme rays, P_I-freeness, facets, and the intersection-cut set
-- statement:
--   This definition collects the vocabulary Chapter 11's first goal (Theorem 11.2, this
--   mission's goal) is built from, restated locally from `01-intro-duality` (Chapter 1's
--   intersection-cut apparatus) and `02b-polarity` (Chapter 2's facet apparatus), per the series
--   convention against importing another draft mission's definitions.
--
--   `extremeRay I abar j` is the direction of the LP cone's `j`-th extreme ray at a basic solution
--   with basic index set `I` and tableau coefficients `ā`. A convex set `S` is **`P_I`-free** at
--   `x̄` if `x̄` lies in its interior and that interior contains no point of the mixed-integer
--   feasible set `P_I`. `PolyDim` is the affine dimension of a set (via `Module.finrank` of its
--   `vectorSpan`), and `F` **is a facet** of `Q` if it is a proper extreme subset of codimension
--   exactly $1$. `IntersectionCutSet J lam` packages the intersection-cut inequality
--   $\sum_{j\in J} (1/\lambda_j) x_j \ge 1$ as a set.
--
--   **Formalization Note.** All definitions are stated generically (over an abstract finite index
--   type `ι`, or an abstract real vector space `E` for `PolyDim`/`IsFacet`), matching how
--   `01-intro-duality` and `02b-polarity` themselves state them, so this chunk's goal theorem
--   reads as a direct continuation of those chapters' own vocabulary.
-- source:
--   Balas, Disjunctive Programming, Springer 2018, DOI 10.1007/978-3-030-00148-3, p. 3-4, 27-30 (restated for Chapter 11)

import Mathlib

namespace Disjunctive.GeneralDisjunctions

/-- The extreme-ray direction `r^j` of the LP cone `C(J)` at a basic solution with basic index
set `I` and tableau coefficients `ā` (restated from `01-intro-duality`, Balas §1.2, p. 3): for
`i ∈ I`, `r^j_i = -ā_{ij}`; `r^j_j = 1`; and `r^j_i = 0` for `i ∈ J \ {j}`. -/
def extremeRay {ι : Type*} [DecidableEq ι] (I : Finset ι) (abar : ι → ι → ℝ) (j : ι) : ι → ℝ :=
  fun i => if i = j then 1 else if i ∈ I then -abar i j else 0

/-- A convex set `S` is `P_I`-free at `x̄` (restated from `01-intro-duality`, Balas §1.2, p. 4):
`x̄ ∈ int S` and `int S` contains no point of `P_I`. -/
def PIFree {ι : Type*} [Fintype ι] (S : Set (ι → ℝ)) (PI : Set (ι → ℝ)) (xbar : ι → ℝ) : Prop :=
  Convex ℝ S ∧ xbar ∈ interior S ∧ interior S ∩ PI = ∅

open Classical in
/-- The dimension of a polyhedron (or any set) `P` in a real vector space `E`: the dimension of
the linear span of its difference set, i.e. of its affine hull (restated from `02b-polarity`,
Balas §2.2.2, p. 29, `dim(Q)`). -/
noncomputable def PolyDim {E : Type*} [AddCommGroup E] [Module ℝ E] (P : Set E) : ℤ :=
  if P.Nonempty then (Module.finrank ℝ (vectorSpan ℝ P) : ℤ) else -1

/-- `F` is a facet of `Q`: a proper extreme subset (face) of codimension exactly `1` (restated
from `02b-polarity`, Balas §2.2.3, p. 30, used implicitly via "`dim(FQ) = dim(Q) - 1`" for a
facet `FQ` of `Q`).  Dimensions are carried in `ℤ` with
`dim ∅ = -1`: with `ℕ` and truncated subtraction the empty set is a facet of every
one-dimensional polyhedron and a point is a facet of itself. A facet is also required to be
nonempty; properness then follows from the dimension drop. -/
def IsFacet {E : Type*} [AddCommGroup E] [Module ℝ E] (Q F : Set E) : Prop :=
  IsExtreme ℝ Q F ∧ F.Nonempty ∧ PolyDim F = PolyDim Q - 1

/-- `v` is an extreme ray of a cone `W` in a real vector space `E` (restated from `02b-polarity`,
Balas §2.2, p. 27, `extr W`). -/
def IsExtremeRay {E : Type*} [AddCommGroup E] [Module ℝ E] (W : Set E) (v : E) : Prop :=
  v ≠ 0 ∧ v ∈ W ∧ IsExtreme ℝ W {x | ∃ t : ℝ, 0 ≤ t ∧ x = t • v}

/-- `dir` is an extreme-ray direction of the polyhedron `CK` at the apex `v` (Balas §11.3, p.
152): an extreme ray of the recentered cone `{y : v + y ∈ CK}`. -/
def IsExtremeRayAt {n : ℕ} (CK : Set (Fin n → ℝ)) (v dir : Fin n → ℝ) : Prop :=
  IsExtremeRay {y | v + y ∈ CK} dir

/-- The intersection cut `∑_{j∈J} (1/λ_j) x_j ≥ 1` (restated from `01-intro-duality`'s Theorem
1.1, as a set), for a nonbasic index set `J` and exit parameters `λ_j`. -/
def IntersectionCutSet {ι : Type*} (J : Finset ι) (lam : ι → ℝ) : Set (ι → ℝ) :=
  {x | 1 ≤ ∑ j ∈ J, (lam j)⁻¹ * x j}

end Disjunctive.GeneralDisjunctions


