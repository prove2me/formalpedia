-- Prove2me | Definitions.Def_CatalyticMatching_General_Supplement_MixedMatrix
-- name    : CatalyticMatching_General_Supplement_MixedMatrix
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T19:05:34.058811+00:00
-- url     : https://prove2.me/theorems/b3dce872-fb21-4c72-806a-f6d1684fb1e0
-- title:
--   Rectangular mixed matrices, evaluations, generic rank and tagged row/column deficiency
-- statement:
--   Let $F$ be a field. An $r\times c$ **mixed matrix** $A$ has, at each position $(i,j)$, either a fixed scalar of $F$ or an indeterminate $x_{ij}$, with a distinct indeterminate at every such position; $E$ is the set of variable positions and $X=\{x_{ij}:(i,j)\in E\}$. An **evaluation** $A'$ assigns one value of $F$ to each variable and leaves every fixed entry unchanged; $A'_{x_i\leftarrow b}$ changes the single variable $x_i$ to $b$. The **generic matrix** places each $x_{ij}$ in the rational function field $F(X)$, and $\operatorname{rank}A$ denotes its rank there.
--
--   Rows are tagged by $L_r$ and columns by $L_c$, kept disjoint. For any $r\times c$ matrix $B$ over a field,
--
--   $$D(B)=\{u\in L_r\cup L_c:\ \operatorname{rank}(B\setminus\{u\})=\operatorname{rank}B\},$$
--
--   where $B\setminus\{u\}$ deletes the single row $u$ (if $u\in L_r$) or the single column $u$ (if $u\in L_c$). The same tag type is used for the generic matrix and for evaluations, so $D(A)=D(A')$ is a comparison of subsets of one set.
--
--   These objects are the common setting of Lemmas 4.2, 4.3, 4.5, Claim 4.4 and Theorem 4.6.
--
--   **Formalization Note** A mixed matrix is a function $\mathrm{Fin}\,r\to\mathrm{Fin}\,c\to\mathrm{Option}\,F$, `none` marking an indeterminate. Dimensions $0$ are allowed. The deficiency here is rectangular, unlike the principal-deletion deficiency of the Tutte matrix in the base mission.
-- source:
--   Srijan Chakraborty, Samir Datta, Aryan Kusre, Partha Mukhopadhyay, Amit Sinhababu, Maximum Matching and Related Problems in Catalytic Logspace, STOC 2027 submission #479 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/479.pdf, Definition 4.1 and the definition of D(A), printed/PDF pp.22–23

import Mathlib

namespace CatalyticMatching.General.Supplement

/-- Definition 4.1 pp.22--23: an r×c mixed matrix over a field F. `none` marks an
indeterminate entry (one distinct variable per such position); `some s` is the fixed
scalar s. Arbitrary rectangular dimensions, including r = 0 or c = 0. -/
abbrev MixedMatrix (r c : ℕ) (F : Type) := Fin r → Fin c → Option F

/-- The variable set X, indexed by its positions E = {(i,j) : A i j is an indeterminate}. -/
def MixedVar {r c : ℕ} {F : Type} (A : MixedMatrix r c F) : Type :=
  {p : Fin r × Fin c // A p.1 p.2 = none}

noncomputable instance {r c : ℕ} {F : Type} (A : MixedMatrix r c F) :
    Fintype (MixedVar A) := by
  classical
  unfold MixedVar
  infer_instance

instance {r c : ℕ} {F : Type} (A : MixedMatrix r c F) : DecidableEq (MixedVar A) := by
  unfold MixedVar
  infer_instance

/-- Substitute values from an F-algebra R for the variables; scalar entries are mapped
into R unchanged. -/
noncomputable def mixedSubst {r c : ℕ} {F : Type} [Field F] (A : MixedMatrix r c F)
    {R : Type} [CommRing R] [Algebra F R] (a : MixedVar A → R) : Matrix (Fin r) (Fin c) R :=
  fun i j => match h : A i j with
    | none => a ⟨(i, j), h⟩
    | some s => algebraMap F R s

/-- An evaluation A′ of A: one field element per variable; every fixed entry unchanged. -/
noncomputable def mixedEval {r c : ℕ} {F : Type} [Field F] (A : MixedMatrix r c F)
    (a : MixedVar A → F) : Matrix (Fin r) (Fin c) F :=
  mixedSubst A a

/-- The rational function field F(X) in the variables of A. -/
abbrev MixedField {r c : ℕ} {F : Type} [Field F] (A : MixedMatrix r c F) :=
  FractionRing (MvPolynomial (MixedVar A) F)

/-- The generic matrix A over F(X): each variable position holds its own indeterminate. -/
noncomputable def genericMixed {r c : ℕ} {F : Type} [Field F] (A : MixedMatrix r c F) :
    Matrix (Fin r) (Fin c) (MixedField A) :=
  mixedSubst A (fun v => algebraMap (MvPolynomial (MixedVar A) F) (MixedField A)
    (MvPolynomial.X v))

/-- Row tags L_r and column tags L_c, kept disjoint: row i and column i differ. -/
abbrev Tag (r c : ℕ) := Fin r ⊕ Fin c

/-- Rank after deleting the single tagged row, or the single tagged column. -/
noncomputable def deletedRank {r c : ℕ} {K : Type} [Field K]
    (B : Matrix (Fin r) (Fin c) K) : Tag r c → ℕ
  | Sum.inl i => (B.submatrix (fun v : {v : Fin r // v ≠ i} => v.val) id).rank
  | Sum.inr j => (B.submatrix id (fun v : {v : Fin c // v ≠ j} => v.val)).rank

/-- p.23: D(B) = {u ∈ L_r ∪ L_c : rank(B \ {u}) = rank B}, one row or one column deleted. -/
def rectDeficiency {r c : ℕ} {K : Type} [Field K] (B : Matrix (Fin r) (Fin c) K) :
    Set (Tag r c) :=
  {u | deletedRank B u = B.rank}

/-- A′_{x_i ← b}: change the single variable x_i to b, all other values unchanged. -/
def perturbVar {r c : ℕ} {F : Type} {A : MixedMatrix r c F} (a : MixedVar A → F)
    (i : MixedVar A) (b : F) : MixedVar A → F :=
  Function.update a i b

end CatalyticMatching.General.Supplement


