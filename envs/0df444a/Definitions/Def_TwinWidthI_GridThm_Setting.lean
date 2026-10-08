-- Prove2me | Definitions.Def_TwinWidthI_GridThm_Setting
-- name    : TwinWidthI_GridThm_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T07:43:12.279644+00:00
-- url     : https://prove2.me/theorems/79d14fb0-fb8f-4103-821a-47ef2ebdd767
-- title:
--   pp. 3:16–3:20 — matrix contraction sequences, error value, divisions, twin-ordered matrices, mixed and grid minors, mixed value, corners
-- statement:
--   Let $M=(m_{i,j})$ be an $n\times m$ matrix with entries in a finite alphabet $A$; rows are indexed by $\{0,\dots,n-1\}$ and columns by $\{0,\dots,m-1\}$. For a set $R$ of rows and a set $C$ of columns, the **zone** $R\cap C$ is the submatrix of entries $m_{i,j}$ with $i\in R$, $j\in C$.
--
--   **Partitions and contractions (p. 3:17).** A row-partition $\mathcal R$ and a column-partition $\mathcal C$ form a partition $(\mathcal R,\mathcal C)$ of $M$. A *contraction* of a partition of a set replaces two distinct parts $P\neq P'$ by $P\cup P'$. A partition $\mathcal P$ *$k$-refines* $\mathcal P'$ if every part of $\mathcal P$ lies inside a part of $\mathcal P'$ and every part of $\mathcal P'$ contains at most $k$ parts of $\mathcal P$.
--
--   **Error value and twin-width (pp. 3:17–3:18).** A zone is *constant* if all its entries are equal. The pair $(\mathcal R,\mathcal C)$ has *error value at most $t$* if every row part $R_i$ forms a non-constant zone $R_i\cap C_j$ with at most $t$ column parts $C_j$, and symmetrically every column part forms a non-constant zone with at most $t$ row parts. The matrix $M$ has *twin-width at most $t$* if there is a *contraction sequence* $(\mathcal R^0,\mathcal C^0),\dots,(\mathcal R^N,\mathcal C^N)$ such that
--
--   1. $(\mathcal R^0,\mathcal C^0)$ is the finest partition (all parts singletons);
--   2. $(\mathcal R^N,\mathcal C^N)$ is the coarsest partition (at most one row part and at most one column part);
--   3. each $(\mathcal R^{i+1},\mathcal C^{i+1})$ arises from $(\mathcal R^i,\mathcal C^i)$ by one contraction, either of two row parts or of two column parts;
--   4. every $(\mathcal R^i,\mathcal C^i)$ has error value at most $t$.
--
--   **Divisions (p. 3:18).** A *division* is a partition whose parts consist of consecutive indices. A $(k,\ell)$-division of $M$ is described by cut points $0=r_0<r_1<\dots<r_k=n$ and $0=c_0<\dots<c_\ell=m$, the $i$-th row part being $\{a: r_{i-1}\le a<r_i\}$. $M$ is *$t$-twin-ordered* (p. 3:16, p. 3:21) if it has a contraction sequence as above in which every partition is a division and every partition has error value at most $t$.
--
--   **Vertical, horizontal, mixed (p. 3:19).** A zone is *vertical* if all its rows coincide, *horizontal* if all its columns coincide, and *mixed* if it is neither. A *$t$-mixed minor* is a $(t,t)$-division all of whose $t^2$ zones are mixed; $M$ is *$t$-mixed free* if it has none. For a $0,1$-matrix, a *$t$-grid minor* is a $(t,t)$-division every zone of which contains an entry $1$.
--
--   **Marcus–Tardos constant (pp. 3:18–3:19).** $$c_t=\tfrac83\,(t+1)^2\,2^{4t}.$$
--
--   **Mixed value (p. 3:20).** Let $\mathcal R=\{R_1,\dots,R_k\}$ be a row-division and $C$ a set of columns. A *mixed zone* of $C$ on $\mathcal R$ is a mixed zone $R_i\cap C$; a *mixed cut* is an index $i$ such that the $2\times|C|$ zone formed by the last row of $R_i$, the first row of $R_{i+1}$ and $C$ is mixed. The *mixed value* of $C$ on $\mathcal R$ is the number of mixed zones plus the number of mixed cuts; the column version is symmetric. A division $(\mathcal R,\mathcal C)$ has *mixed value at most $t$* if every $C_j$ has mixed value at most $t$ on $\mathcal R$ and every $R_i$ has mixed value at most $t$ on $\mathcal C$.
--
--   **Corners (p. 3:19).** A *corner* is a mixed $2\times2$ submatrix on consecutive rows $i,i+1$ and consecutive columns $j,j+1$.
--
--   These are the objects of Section 5 of the paper: the Grid Minor Theorem for twin-width (Theorem 5.4) and every lemma of its proof are stated in terms of them.
--
--   **Formalization Note** Matrices are `Matrix (Fin n) (Fin m) A`; partitions are Mathlib `Finpartition`s of `univ`, with `⊥` the partition into singletons. Twin-width is the *partition form* of p. 3:18 (the paper states it is a restatement of the red-number definition of p. 3:16); it is a predicate `MatTwinWidthLE M t`, never an infimum. "Coarsest" is "at most one part", which also covers empty index sets. Vertical/horizontal are encoded as "all rows (columns) of the zone agree", equivalent to the page's consecutive-index condition on the intervals where it is used. Divisions in minors are given by strictly increasing cut points, so every part is non-empty. Grid minors use `Bool` entries (`true` = 1). In a mixed value, a mixed cut between consecutive parts $X,X'$ is counted once, at $X$; "last row of $X$" and "first row of $X'$" are encoded as the maximum $a\in X$ and minimum $b\in X'$ with $b=a+1$. Counts use classical decidability.
-- source:
--   Bonnet, Kim, Thomassé and Watrigant, Twin-width I: Tractable FO Model Checking, J. ACM 69(1), Article 3 (2021), pp. 3:16–3:20, §5.1–5.6

import Mathlib
import Definitions.Def_TwinWidthI_BoolWidth_Setting

namespace TwinWidthI.GridThm

open Finset

/-- p. 3:17: `P` `k`-refines `P'`: every part of `P` is contained in a part of `P'`, and every part
of `P'` contains at most `k` parts of `P`. -/
def KRefines {α : Type*} [DecidableEq α] {s : Finset α} (k : ℕ) (P P' : Finpartition s) : Prop :=
  (∀ X ∈ P.parts, ∃ Y ∈ P'.parts, X ⊆ Y) ∧
    ∀ Y ∈ P'.parts, #{X ∈ P.parts | X ⊆ Y} ≤ k

section Matrices

variable {A : Type*} {n m : ℕ}

/-- p. 3:18: the zone `R ∩ C` (rows `R`, columns `C`) of `M` is constant: all its entries are
identical. -/
def ZoneConst (M : Matrix (Fin n) (Fin m) A) (R : Finset (Fin n)) (C : Finset (Fin m)) : Prop :=
  ∀ i ∈ R, ∀ i' ∈ R, ∀ j ∈ C, ∀ j' ∈ C, M i j = M i' j'

open Classical in
/-- p. 3:18: the partition pair `(R, C)` of `M` has error value at most `t`: every row part `X`
forms a non-constant zone with at most `t` column parts, and every column part `Y` forms a
non-constant zone with at most `t` row parts. -/
def ErrorLE (M : Matrix (Fin n) (Fin m) A) (R : Finpartition (univ : Finset (Fin n)))
    (C : Finpartition (univ : Finset (Fin m))) (t : ℕ) : Prop :=
  (∀ X ∈ R.parts, #{Y ∈ C.parts | ¬ ZoneConst M X Y} ≤ t) ∧
  (∀ Y ∈ C.parts, #{X ∈ R.parts | ¬ ZoneConst M X Y} ≤ t)

/-- pp. 3:17–3:18: `M` has twin-width at most `t`. There is a contraction sequence
`(R 0, C 0), …, (R N, C N)` starting at the finest partition (singletons, `⊥`), ending at the
coarsest partition (at most one row part and at most one column part), in which each step merges
two parts of the row partition or two parts of the column partition (never both), and every
partition pair of the sequence has error value at most `t`. -/
def MatTwinWidthLE (M : Matrix (Fin n) (Fin m) A) (t : ℕ) : Prop :=
  ∃ (N : ℕ) (R : Fin (N + 1) → Finpartition (univ : Finset (Fin n)))
    (C : Fin (N + 1) → Finpartition (univ : Finset (Fin m))),
    R 0 = ⊥ ∧ C 0 = ⊥ ∧ #(R (Fin.last N)).parts ≤ 1 ∧ #(C (Fin.last N)).parts ≤ 1 ∧
    (∀ i : Fin N, (TwinWidthI.BoolWidth.IsMergeStep (R i.castSucc) (R i.succ) ∧ C i.succ = C i.castSucc) ∨
                  (R i.succ = R i.castSucc ∧ TwinWidthI.BoolWidth.IsMergeStep (C i.castSucc) (C i.succ))) ∧
    ∀ i, ErrorLE M (R i) (C i) t

end Matrices

/-- p. 3:18: a set of indices consisting of consecutive indices (an interval of `Fin k`). -/
def IsIntervalSet {k : ℕ} (X : Finset (Fin k)) : Prop :=
  ∀ a ∈ X, ∀ b ∈ X, ∀ c, a ≤ c → c ≤ b → c ∈ X

/-- p. 3:18: a row-division (resp. column-division): a partition every part of which consists of
consecutive indices. -/
def IsDivision {k : ℕ} (P : Finpartition (univ : Finset (Fin k))) : Prop :=
  ∀ X ∈ P.parts, IsIntervalSet X

section Matrices2

variable {A : Type*} {n m : ℕ}

/-- p. 3:16 and p. 3:21: `M` is `t`-twin-ordered: it has a division sequence (a contraction
sequence as in `MatTwinWidthLE` in which every row and column partition is a division, so every
contraction fuses two consecutive parts) all of whose divisions have error value at most `t`. -/
def TwinOrdered (M : Matrix (Fin n) (Fin m) A) (t : ℕ) : Prop :=
  ∃ (N : ℕ) (R : Fin (N + 1) → Finpartition (univ : Finset (Fin n)))
    (C : Fin (N + 1) → Finpartition (univ : Finset (Fin m))),
    R 0 = ⊥ ∧ C 0 = ⊥ ∧ #(R (Fin.last N)).parts ≤ 1 ∧ #(C (Fin.last N)).parts ≤ 1 ∧
    (∀ i : Fin N, (TwinWidthI.BoolWidth.IsMergeStep (R i.castSucc) (R i.succ) ∧ C i.succ = C i.castSucc) ∨
                  (R i.succ = R i.castSucc ∧ TwinWidthI.BoolWidth.IsMergeStep (C i.castSucc) (C i.succ))) ∧
    ∀ i, ErrorLE M (R i) (C i) t ∧ IsDivision (R i) ∧ IsDivision (C i)

/-- p. 3:19: the zone `R ∩ C` is vertical: all its rows agree (`m_{i,j} = m_{i+1,j}` inside the
zone; for a zone of consecutive rows this is the same as all rows being equal). -/
def IsVertical (M : Matrix (Fin n) (Fin m) A) (R : Finset (Fin n)) (C : Finset (Fin m)) : Prop :=
  ∀ i ∈ R, ∀ i' ∈ R, ∀ j ∈ C, M i j = M i' j

/-- p. 3:19: the zone `R ∩ C` is horizontal: all its columns agree (`m_{i,j} = m_{i,j+1}` inside
the zone). -/
def IsHorizontal (M : Matrix (Fin n) (Fin m) A) (R : Finset (Fin n)) (C : Finset (Fin m)) :
    Prop :=
  ∀ i ∈ R, ∀ j ∈ C, ∀ j' ∈ C, M i j = M i j'

/-- p. 3:19: the zone `R ∩ C` is mixed: neither vertical nor horizontal. -/
def IsMixed (M : Matrix (Fin n) (Fin m) A) (R : Finset (Fin n)) (C : Finset (Fin m)) : Prop :=
  ¬ IsVertical M R C ∧ ¬ IsHorizontal M R C

/-- Cut points of a division of the index set `Fin n` into `k` consecutive non-empty parts:
`r 0 = 0 < r 1 < ⋯ < r k = n`. -/
def IsCutSeq (k n : ℕ) (r : Fin (k + 1) → ℕ) : Prop :=
  StrictMono r ∧ r 0 = 0 ∧ r (Fin.last k) = n

/-- The `i`-th part `{a | r i ≤ a < r (i+1)}` of the division with cut points `r`. -/
def cutPart {n k : ℕ} (r : Fin (k + 1) → ℕ) (i : Fin k) : Finset (Fin n) :=
  univ.filter (fun a : Fin n => r i.castSucc ≤ (a : ℕ) ∧ (a : ℕ) < r i.succ)

/-- p. 3:19: `M` has a `t`-mixed minor: a `(t, t)`-division `(R, C)` (given by cut points) such
that every zone `R_i ∩ C_j` is mixed. -/
def HasMixedMinor (M : Matrix (Fin n) (Fin m) A) (t : ℕ) : Prop :=
  ∃ (r c : Fin (t + 1) → ℕ), IsCutSeq t n r ∧ IsCutSeq t m c ∧
    ∀ i j : Fin t, IsMixed M (cutPart r i) (cutPart c j)

/-- p. 3:19: `M` is `t`-mixed free: it has no `t`-mixed minor. -/
def MixedFree (M : Matrix (Fin n) (Fin m) A) (t : ℕ) : Prop :=
  ¬ HasMixedMinor M t

/-- p. 3:18: a `0,1`-matrix (entries in `Bool`, `true` = 1) has a `t`-grid minor: a
`(t, t)`-division (given by cut points) in which every zone contains a 1. -/
def HasGridMinor (M : Matrix (Fin n) (Fin m) Bool) (t : ℕ) : Prop :=
  ∃ (r c : Fin (t + 1) → ℕ), IsCutSeq t n r ∧ IsCutSeq t m c ∧
    ∀ i j : Fin t, ∃ a ∈ cutPart r i, ∃ b ∈ cutPart c j, M a b = true

/-- p. 3:18–3:19: the Marcus–Tardos constant in the form of Cibulka and Kynčl,
`c_t = 8/3 (t + 1)^2 2^{4t}`. -/
noncomputable def cMT (t : ℕ) : ℝ := 8 / 3 * ((t : ℝ) + 1) ^ 2 * 2 ^ (4 * t)

/-- p. 3:20: the rows `X` and `X'` of a row-division are consecutive parts and the mixed-cut
condition holds for the column set `C`: `a` is the last row of `X`, `b = a + 1` is the first row
of `X'`, and the `2 × |C|` zone `{a, b} ∩ C` is mixed. -/
def IsMixedCutRow (M : Matrix (Fin n) (Fin m) A) (X X' : Finset (Fin n)) (C : Finset (Fin m)) :
    Prop :=
  ∃ a ∈ X, ∃ b ∈ X', (∀ x ∈ X, x ≤ a) ∧ (∀ y ∈ X', b ≤ y) ∧ (a : ℕ) + 1 = b ∧
    IsMixed M {a, b} C

/-- p. 3:20: the column analogue: `Y`, `Y'` consecutive column parts, `a` the last column of `Y`,
`b = a + 1` the first column of `Y'`, and the `|R| × 2` zone `R ∩ {a, b}` is mixed. -/
def IsMixedCutCol (M : Matrix (Fin n) (Fin m) A) (R : Finset (Fin n)) (Y Y' : Finset (Fin m)) :
    Prop :=
  ∃ a ∈ Y, ∃ b ∈ Y', (∀ x ∈ Y, x ≤ a) ∧ (∀ y ∈ Y', b ≤ y) ∧ (a : ℕ) + 1 = b ∧
    IsMixed M R {a, b}

open Classical in
/-- p. 3:20: the mixed value of a set `C` of consecutive columns on a row-division `R`: the number
of mixed zones `X ∩ C` (`X ∈ R`) plus the number of mixed cuts (each cut between consecutive
parts `X`, `X'` is counted once, at its upper part `X`). -/
noncomputable def mixedValueRow (M : Matrix (Fin n) (Fin m) A)
    (R : Finpartition (univ : Finset (Fin n))) (C : Finset (Fin m)) : ℕ :=
  #{X ∈ R.parts | IsMixed M X C} + #{X ∈ R.parts | ∃ X' ∈ R.parts, IsMixedCutRow M X X' C}

open Classical in
/-- p. 3:20: the mixed value of a set `R` of consecutive rows on a column-division `C`. -/
noncomputable def mixedValueCol (M : Matrix (Fin n) (Fin m) A) (R : Finset (Fin n))
    (C : Finpartition (univ : Finset (Fin m))) : ℕ :=
  #{Y ∈ C.parts | IsMixed M R Y} + #{Y ∈ C.parts | ∃ Y' ∈ C.parts, IsMixedCutCol M R Y Y'}

/-- p. 3:20: the division `(R, C)` has mixed value at most `t`: every column part has mixed value
at most `t` on `R`, and every row part has mixed value at most `t` on `C`. -/
def MixedValueLE (M : Matrix (Fin n) (Fin m) A) (R : Finpartition (univ : Finset (Fin n)))
    (C : Finpartition (univ : Finset (Fin m))) (t : ℕ) : Prop :=
  (∀ Y ∈ C.parts, mixedValueRow M R Y ≤ t) ∧ (∀ X ∈ R.parts, mixedValueCol M X C ≤ t)

/-- p. 3:19: a corner at `(i, j)`: rows `i, i+1` and columns `j, j+1` exist and the `2 × 2`
submatrix `(m_{i,j}, m_{i+1,j}, m_{i,j+1}, m_{i+1,j+1})` is mixed. -/
def IsCorner (M : Matrix (Fin n) (Fin m) A) (i : Fin n) (j : Fin m) : Prop :=
  ∃ (i' : Fin n) (j' : Fin m), (i' : ℕ) = i + 1 ∧ (j' : ℕ) = j + 1 ∧ IsMixed M {i, i'} {j, j'}

end Matrices2

end TwinWidthI.GridThm


