-- Prove2me | Definitions.Def_Disjunctive_Polymatroids_Basic
-- name    : Disjunctive_Polymatroids_Basic
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T17:11:48.071354+00:00
-- url     : https://prove2.me/theorems/c783ae17-fbf8-4289-8b05-f73218e4bc1d
-- title:
--   Polymatroid rank functions, P(r), Z(r1,r2), and the Π/U projection system
-- statement:
--   This definition collects the polymatroid vocabulary the book's closing chapter (and this
--   mission, its final one) is built from.
--
--   A set function `r` satisfies **conditions 1-3 of Application 1** if `r(∅)=0`, `r(A)≤|A|` on
--   every proper subset, and `r` is nondecreasing; it is a **polymatroid rank function** if
--   instead `r(∅)=0`, nondecreasing, and submodular (dropping the `|A|`-bound, adding
--   submodularity — a strictly different, more general condition, per the book's own "satisfying
--   1 and 3... and submodular"). `PolymatroidP r := \{x\ge0 : x(A)\le r(A)\ \forall A\subseteq
--   N\}$ is the associated polytope. `ZDisjoint r₁ r₂` is the disjoint-space union of two such
--   polytopes. `PiSet`/`PiProjSystem` package Proposition 13.22's object `Π` and its projection
--   characterization; `USet` is Proposition 13.23's polytope `U`.
--
--   **Formalization Note.** `IsApp1SetFunction` and `IsPolymatroidRankFunction` are two genuinely
--   different predicates (not one general definition specialized by a flag), matching how the
--   book itself treats §13.4's "Application 1" set functions and §13.8's polymatroid rank
--   functions as related but distinct hypotheses on `r` — conflating them would misrepresent
--   which theorem needs which condition (per `BRIEF.md`'s explicit warning to locate the exact
--   numbered conditions rather than guess).
-- source:
--   Balas, Disjunctive Programming, Springer 2018, DOI 10.1007/978-3-030-00148-3, p. 224, 231, Sections 13.4, 13.7-13.8

import Mathlib

namespace Disjunctive.Polymatroids

/-- `x(A) := Σ_{j∈A} x_j` (Balas §13, notation used throughout, restated locally). -/
def SumOver {n : ℕ} (x : Fin n → ℝ) (A : Finset (Fin n)) : ℝ :=
  ∑ j ∈ A, x j

/-- `r` satisfies conditions 1-3 of Application 1 (Balas §13.4, p. 224): `r(∅)=0`; `r(A)≤|A|` for
every proper subset `A⊂N`; and `r` is nondecreasing (`A⊆B → r(A)≤r(B)`). -/
def IsApp1SetFunction {n : ℕ} (r : Finset (Fin n) → ℝ) : Prop :=
  r ∅ = 0 ∧ (∀ A : Finset (Fin n), A ⊂ Finset.univ → r A ≤ A.card) ∧
    ∀ A B : Finset (Fin n), A ⊆ B → r A ≤ r B

/-- `r` is a polymatroid rank function (Balas §13.8, p. 231: "satisfying 1 and 3 in Application 1
and submodular"): `r(∅)=0`, nondecreasing, and submodular (`r(A)+r(B) ≥ r(A∪B)+r(A∩B)`). -/
def IsPolymatroidRankFunction {n : ℕ} (r : Finset (Fin n) → ℝ) : Prop :=
  r ∅ = 0 ∧ (∀ A B : Finset (Fin n), A ⊆ B → r A ≤ r B) ∧
    ∀ A B : Finset (Fin n), r (A ∪ B) + r (A ∩ B) ≤ r A + r B

/-- The polymatroid (or Application-1) polytope `P(r) := {x∈ℝ^k_+ : x(A)≤r(A) for A⊆N}` (Balas
§13.4, p. 224, and §13.7, p. 231). -/
def PolymatroidP {k : ℕ} (r : Finset (Fin k) → ℝ) : Set (Fin k → ℝ) :=
  {x | 0 ≤ x ∧ ∀ A : Finset (Fin k), SumOver x A ≤ r A}

/-- The disjoint-space union `Z(r₁,r₂) := {(x,y)∈[0,1]^m×[0,1]^n : x∈P(r₁) or y∈P(r₂)}` (Balas
§13.4, p. 224). -/
def ZDisjoint {m n : ℕ} (r1 : Finset (Fin m) → ℝ) (r2 : Finset (Fin n) → ℝ) :
    Set ((Fin m → ℝ) × (Fin n → ℝ)) :=
  {p | (∀ i, 0 ≤ p.1 i ∧ p.1 i ≤ 1) ∧ (∀ j, 0 ≤ p.2 j ∧ p.2 j ≤ 1) ∧
    (p.1 ∈ PolymatroidP r1 ∨ p.2 ∈ PolymatroidP r2)}

/-- `Π := {π∈ℝⁿ_+ : πx≤1 for x∈P(r₁)∪P(r₂)}` (Balas §13.8, p. 231), the object whose projection
characterization is Proposition 13.22. -/
def PiSet {n : ℕ} (r1 r2 : Finset (Fin n) → ℝ) : Set (Fin n → ℝ) :=
  {pi | 0 ≤ pi ∧ ∀ x ∈ PolymatroidP r1 ∪ PolymatroidP r2, dotProduct pi x ≤ 1}

/-- The projection system defining `Π` (Balas §13.8, p. 231, Proposition 13.22's right side):
`π_j ≤ Σ_{A∋j} u_A` for `j∈N`, `Σ_A u_Ar_i(A)≤1` for `i=1,2`, `π,u≥0`. -/
def PiProjSystem {n : ℕ} (r1 r2 : Finset (Fin n) → ℝ) : Set (Fin n → ℝ) :=
  {pi | ∃ u : Finset (Fin n) → ℝ, (∀ A, 0 ≤ u A) ∧ 0 ≤ pi ∧
    (∀ j, pi j ≤ ∑ A ∈ Finset.univ.filter (fun A => j ∈ A), u A) ∧
    (∑ A, u A * r1 A) ≤ 1 ∧ (∑ A, u A * r2 A) ≤ 1}

/-- `U := {u≥0 : Σ_A u_Ar_i(A)≤1, i=1,2}` (Balas §13.8, p. 231, Proposition 13.23). -/
def USet {n : ℕ} (r1 r2 : Finset (Fin n) → ℝ) : Set (Finset (Fin n) → ℝ) :=
  {u | (∀ A, 0 ≤ u A) ∧ (∑ A, u A * r1 A) ≤ 1 ∧ (∑ A, u A * r2 A) ≤ 1}

end Disjunctive.Polymatroids


