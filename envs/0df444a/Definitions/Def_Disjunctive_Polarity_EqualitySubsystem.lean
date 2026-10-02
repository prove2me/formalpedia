-- Prove2me | Definitions.Def_Disjunctive_Polarity_EqualitySubsystem
-- name    : Disjunctive_Polarity_EqualitySubsystem
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T16:14:41.73234+00:00
-- url     : https://prove2.me/theorems/7efd8a1a-da00-4a01-878d-480d82ce56f2
-- title:
--   The equality subsystem of a polyhedron and its rank
-- statement:
--   This definition fixes the rank quantities Theorem 2.7 and Corollaries 2.8-2.10 are stated in
--   terms of: the equality subsystem of a polyhedron (or of a candidate facet), and its rank.
--
--   Given a system $(A,B,b)$ with $m$ rows and a target set (e.g. $Q$ itself, or a candidate facet
--   $F_Q$), the **tight rows** are those indices $i$ for which the $i$-th inequality
--   $A_i u + B_i x \le b_i$ is satisfied at equality throughout the target. Writing $A_=, B_=$ for the
--   restriction of $A, B$ to the tight rows, define $r := \mathrm{rank}(A_=, B_=)$ (rank of the
--   combined matrix, columns $u$ and $x$ together) and $r^* := \mathrm{rank}(A_=)$ (rank of the
--   $u$-columns alone). Applied to $Q$ itself these give the quantities the book calls $r$, $r^*$;
--   applied to a facet's own augmented system (the facet's defining inequality appended as an
--   additional row) they give the facet's own $r_F$, $r_F^*$.
--
--   **Formalization Note.** `TightRows` takes an explicit `target` set (rather than being hardwired
--   to `Poly2 A B b`) precisely so the same rank machinery serves both $Q$'s own equality subsystem
--   (via `EqRank`/`EqRankA`, `target = Poly2 A B b`) and a facet's equality subsystem (via
--   `SystemRank`/`SystemRankA` applied to the row-augmented system with `target` set to the facet).
-- source:
--   Balas, Disjunctive Programming, Springer 2018, DOI 10.1007/978-3-030-00148-3, p. 29, Section 2.2.2

import Mathlib
import Definitions.Def_Disjunctive_Polarity_Projection

namespace Disjunctive.Polarity

/-- The rows of `(A,B,b)` that are tight (satisfied at equality) throughout a target set,
e.g. throughout `Q` itself or throughout a facet `FQ` of `Q` (Balas §2.2.2, p. 29: "the equality
subsystem of `Q`", generalized here to an arbitrary target set so the same definition also gives
a facet's own equality subsystem, needed by Corollaries 2.8-2.10). -/
def TightRows {m p q : ℕ} (A : Matrix (Fin m) (Fin p) ℝ) (B : Matrix (Fin m) (Fin q) ℝ)
    (b : Fin m → ℝ) (target : Set ((Fin p → ℝ) × (Fin q → ℝ))) : Set (Fin m) :=
  {i | ∀ ux ∈ target, A.mulVec ux.1 i + B.mulVec ux.2 i = b i}

/-- `rank(A=, B=)` for the equality-subsystem rows `rows` (Balas §2.2.2, p. 29, `r`). -/
noncomputable def SystemRank {m p q : ℕ} (A : Matrix (Fin m) (Fin p) ℝ)
    (B : Matrix (Fin m) (Fin q) ℝ) (rows : Set (Fin m)) : ℕ :=
  (Matrix.fromCols (A.submatrix (Subtype.val : {i // i ∈ rows} → Fin m) id)
                    (B.submatrix (Subtype.val : {i // i ∈ rows} → Fin m) id)).rank

/-- `rank(A=)` for the equality-subsystem rows `rows` (Balas §2.2.2, p. 29, `r*`). -/
noncomputable def SystemRankA {m p : ℕ} (A : Matrix (Fin m) (Fin p) ℝ) (rows : Set (Fin m)) :
    ℕ :=
  (A.submatrix (Subtype.val : {i // i ∈ rows} → Fin m) id).rank

/-- `r := rank(A=, B=)` for `Q` itself (Balas §2.2.2, p. 29). -/
noncomputable def EqRank {m p q : ℕ} (A : Matrix (Fin m) (Fin p) ℝ) (B : Matrix (Fin m) (Fin q) ℝ)
    (b : Fin m → ℝ) : ℕ :=
  SystemRank A B (TightRows A B b (Poly2 A B b))

/-- `r* := rank(A=)` for `Q` itself (Balas §2.2.2, p. 29). -/
noncomputable def EqRankA {m p q : ℕ} (A : Matrix (Fin m) (Fin p) ℝ) (B : Matrix (Fin m) (Fin q) ℝ)
    (b : Fin m → ℝ) : ℕ :=
  SystemRankA A (TightRows A B b (Poly2 A B b))

end Disjunctive.Polarity


