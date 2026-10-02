-- Prove2me | Definitions.Def_Disjunctive_Dominants_Basic
-- name    : Disjunctive_Dominants_Basic
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T17:08:28.925022+00:00
-- url     : https://prove2.me/theorems/9bebb5a5-76ac-4704-a395-1335366a5a97
-- title:
--   The dominant, the blocker, upper separation, upper monotonicity, and I^S
-- statement:
--   This definition collects the vocabulary Chapter 13's dominant/blocker theory is built from.
--
--   For a polyhedron $P \subseteq \mathbb{R}^n_+$, the **dominant** $P^+ := P + \mathbb{R}^n_+$ is
--   the set of points dominating some point of $P$; the **blocker** $P^* := \{\pi \in
--   \mathbb{R}^n_+ : \pi x \ge 1\ \forall x \in P\}$ collects the valid "covering" inequalities
--   (distinct from the reverse polar of `02b-polarity`, which is not restricted to
--   $\mathbb{R}^n_+$). The **upper-separation value** $\alpha_P(x^*) := \min\{\pi x^* : \pi \in
--   P^*\}$ measures how far $x^*$ is from satisfying every valid covering inequality. $P \subseteq
--   [0,1]^n$ is **upper monotone** if $P = P^+ \cap [0,1]^n$.
--
--   `SAlpha`/`GAlpha` implement the constructive apparatus of §13.1 (`S(\alpha)`, `g(\alpha)`) for
--   a single-inequality upper monotone polytope. `PolyDim`/`IsFacet` restate the affine-
--   dimension/facet vocabulary already used in `02b-polarity`/`11a-intersection-cuts`. `ProjS`/
--   `IsInIS` set up Theorem 13.7's general facet characterization: `P^S` is the projection of `P`
--   onto coordinates `S`, and `IsInIS S P π` says `π` (supported exactly on `S`, positive there)
--   is a valid inequality of `P^S` tight at `|S|` linearly independent points of `P^S`.
--
--   **Formalization Note.** `Blocker`/`Dominant` are kept syntactically distinct from any reverse-
--   polar definition (no shared name, no shared file), per `BRIEF.md`'s explicit warning that the
--   nonnegativity restriction makes these different objects from `02b-polarity`'s polar/reverse
--   polar even though the formulas look similar.
-- source:
--   Balas, Disjunctive Programming, Springer 2018, DOI 10.1007/978-3-030-00148-3, p. 215-219, Section 13.1-13.2

import Mathlib

namespace Disjunctive.Dominants

/-- The unit cube `[0,1]^n` (Balas §13.1, p. 216). -/
def UnitCube (n : ℕ) : Set (Fin n → ℝ) :=
  {x | ∀ i, 0 ≤ x i ∧ x i ≤ 1}

/-- The dominant `P⁺ := P + ℝⁿ_+ = {y : y≥x for some x∈P}` of a polyhedron `P ⊆ ℝⁿ_+` (Balas
§13.1, p. 215, Definition 1). -/
def Dominant {n : ℕ} (P : Set (Fin n → ℝ)) : Set (Fin n → ℝ) :=
  {y | 0 ≤ y ∧ ∃ x ∈ P, x ≤ y}

/-- The blocker `P* := {π∈ℝⁿ_+ : πx≥1 for all x∈P}` of `P ⊆ ℝⁿ_+` (Balas §13.1, p. 217,
Definition 3; distinct from the reverse polar of `02b-polarity`, which is not restricted to the
nonnegative orthant). -/
def Blocker {n : ℕ} (P : Set (Fin n → ℝ)) : Set (Fin n → ℝ) :=
  {pi | 0 ≤ pi ∧ ∀ x ∈ P, 1 ≤ dotProduct pi x}

/-- The upper-separation value `α_P := min{πx* : πx≥1 for all x∈P, π≥0}` for `(P,x*)` (Balas
§13.1, p. 217, Definition 2). -/
noncomputable def AlphaP {n : ℕ} (P : Set (Fin n → ℝ)) (xstar : Fin n → ℝ) : ℝ :=
  sInf {v : ℝ | ∃ pi ∈ Blocker P, v = dotProduct pi xstar}

/-- `P ⊆ [0,1]ⁿ` is upper monotone (wrt `[0,1]ⁿ`) if `P = P⁺ ∩ [0,1]ⁿ` (Balas §13.1, p. 217,
Definition 4). -/
def IsUpperMonotone {n : ℕ} (P : Set (Fin n → ℝ)) : Prop :=
  P = Dominant P ∩ UnitCube n

/-- `a(S) := Σ_{j∈S} a_j` (Balas §13.1, p. 218, notation preceding (13.2)). -/
def SumOver {n : ℕ} (a : Fin n → ℝ) (S : Finset (Fin n)) : ℝ :=
  ∑ j ∈ S, a j

/-- `S(α) := {j∈N : x*_j ≤ α}` (Balas §13.1, p. 218). -/
noncomputable def SAlpha {n : ℕ} (xstar : Fin n → ℝ) (alpha : ℝ) : Finset (Fin n) :=
  Finset.univ.filter (fun j => xstar j ≤ alpha)

/-- `g(α) := Σ_{j∈S(α)} a_jx*_j / (1-a(N\S(α)))` (Balas §13.1, p. 218). -/
noncomputable def GAlpha {n : ℕ} (a xstar : Fin n → ℝ) (alpha : ℝ) : ℝ :=
  (∑ j ∈ SAlpha xstar alpha, a j * xstar j) / (1 - SumOver a (Finset.univ \ SAlpha xstar alpha))

open Classical in
/-- The dimension of a set `P` in a real vector space `E`, via the affine span of its difference
set (restated from `02b-polarity`/`11a-intersection-cuts`, Balas §2.2.2, p. 29, `dim(Q)`). -/
noncomputable def PolyDim {E : Type*} [AddCommGroup E] [Module ℝ E] (P : Set E) : ℤ :=
  if P.Nonempty then (Module.finrank ℝ (vectorSpan ℝ P) : ℤ) else -1

/-- `F` is a facet of `Q`: a proper extreme subset (face) of codimension exactly `1` (restated
from `02b-polarity`/`11a-intersection-cuts`). -/
def IsFacet {E : Type*} [AddCommGroup E] [Module ℝ E] (Q F : Set E) : Prop :=
  IsExtreme ℝ Q F ∧ F.Nonempty ∧ PolyDim F = PolyDim Q - 1

/-- The projection `P^S := {y : ∃x∈P, ∀j∈S, x_j=y_j}` of `P` onto the coordinates `S` (Balas
§13.2, p. 219: `P^S = \mathrm{Proj}_{x_S}(P)`, kept in the ambient space `Fin n → ℝ` with the
`S`-coordinates constrained and the rest free). -/
def ProjS {n : ℕ} (S : Finset (Fin n)) (P : Set (Fin n → ℝ)) : Set (Fin n → ℝ) :=
  {y | ∃ x ∈ P, ∀ j ∈ S, x j = y j}

/-- `π` (with support exactly `S`) defines a member of `I^S`: a valid inequality `πx≥1` of `P^S`
with `π_j>0` for `j∈S`, `π_j=0` off `S`, satisfied at equality by `|S|` linearly independent
points of `P^S` (Balas §13.2, p. 219-220, Theorem 13.7). The page works in `ℝ^{|S|}`, so the
independence is that of the points' `S`-coordinates: `ProjS` keeps the coordinates off `S` free,
and independence in `ℝⁿ` would let one point of `P^S` with two free coordinates count as two
(`n = 3`, `S = {0,1}`, `P = {(1,1,0)}` would put `π = (1/2,1/2,0)` in `I^S` though
`(1/2)x₀ + (1/2)x₁ ≥ 1` meets `P⁺` in a one-dimensional face). -/
def IsInIS {n : ℕ} (S : Finset (Fin n)) (P : Set (Fin n → ℝ)) (pi : Fin n → ℝ) : Prop :=
  (∀ j ∉ S, pi j = 0) ∧ (∀ j ∈ S, 0 < pi j) ∧ (∀ x ∈ ProjS S P, 1 ≤ dotProduct pi x) ∧
    ∃ pts : Fin S.card → (Fin n → ℝ), (∀ i, pts i ∈ ProjS S P) ∧
      (∀ i, dotProduct pi (pts i) = 1) ∧
      LinearIndependent ℝ (fun i => fun j : {j : Fin n // j ∈ S} => pts i (j : Fin n))

end Disjunctive.Dominants


