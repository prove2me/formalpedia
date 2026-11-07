-- Prove2me | Definitions.Def_RealAPSP_Triangles
-- name    : RealAPSP_Triangles
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T20:57:08.333199+00:00
-- url     : https://prove2.me/theorems/56e3498a-0851-4868-8d1e-afbfac9c7ea9
-- title:
--   Matrices with missing values, $\Delta$-approximate triangles, and their counts
-- statement:
--   A matrix $A\in(\mathbb R\cup\{\bot\})^{n\times n}$ may have missing entries, with $x+\bot=\bot$ and $\bot\not<0$. For three matrices $A,B,C$ a triple $(i,k,j)\in[n]^3$ has weight
--
--   $$A[i,k]+B[k,j]+C[i,j]$$
--
--   when all three entries are present. It is a **negative triangle** if its weight is below $0$, and a **$\Delta$-approximate triangle** if its weight is $0\pm\Delta$; at $\Delta=0$ it is an **exact triangle**. An $\infty$-approximate solution is a triple with all three entries present.
--
--   This file also fixes the counts of such triples: in all, through one edge, and with only popular edges or with some unpopular edge (the three solution types of p.17). The proof of Theorem 1.1 is driven by these counts.
--
--   **Formalization Note** Indices are $0$-based in `Fin n` and ⊥ is `none`. Matrices are written to memory row-major, as a flag and a value per entry.
-- source:
--   Fischer, Polak, Schmidt, Real-to-Integer Reduction for All-Pairs Shortest Paths, arXiv:2611.04847 (held file sha256 a3dc0096…), §3.2, p.10 (PDF p.12); §5.1, p.16 (PDF p.18); p.17 (PDF p.19)

import Mathlib
import Definitions.Def_RealAPSP_Machine

namespace RealAPSP

/-!
# Matrices with missing values, triangles and their counts

Fischer, Polak, Schmidt, arXiv:2611.04847 (held file sha256 a3dc0096…), §3.2, p.10 (PDF p.12): "we also allow
integer and real instances of any of the defined problem to contain missing values replaced by a dummy symbol
⊥ … x + ⊥ = ⊥ for x ∈ R or ⊥ ≮ 0"; §5.1, p.16 (PDF p.18): "We call a triple (i, k, j) ∈ [n]³ a ∆-approximate
triangle (or ∆-approximate solution) if A[i, k] + B[k, j] + C[i, j] = 0 ± ∆."

**Formalization Note.** Indices are `Fin n` (0-based). ⊥ is `none`. A triple with a ⊥ entry has no weight, so it
is not negative, not exact and not approximate at any finite scale; an "∞-approximate" solution is a triple
with all three entries present (proof of Lemma 5.1, p.16). Matrices are written to memory in row-major order,
with flag `1` for a present entry and `0` for ⊥, and value `0` for ⊥.
-/

/-- An `n × n` matrix with entries in `α ∪ {⊥}`. -/
abbrev Mat (α : Type) (n : ℕ) : Type := Fin n → Fin n → Option α

/-- An integer matrix read as a real one. -/
def castMat {n : ℕ} (X : Mat ℤ n) : Mat ℝ n := fun i j => (X i j).map fun z => (z : ℝ)

/-- A rectangular array in row-major order. -/
def rowMajor {α : Type} {a b : ℕ} (f : Fin a → Fin b → α) : List α :=
  (List.finRange a).flatMap fun i => (List.finRange b).map (f i)

/-- The presence flags of a matrix, row-major. -/
def flagCells {α : Type} {n : ℕ} (X : Mat α n) : List ℤ :=
  rowMajor fun i j => if (X i j).isSome then 1 else 0

/-- The values of a matrix, row-major, `0` for ⊥. -/
def valueCells {α : Type} [Zero α] {n : ℕ} (X : Mat α n) : List α :=
  rowMajor fun i j => (X i j).getD 0

/-- Integer input cells of a real three-matrix instance: parameters, then the flags of `A`, `B`, `C`. -/
def triInts {n : ℕ} (params : List ℤ) (A B C : Mat ℝ n) : List ℤ :=
  params ++ flagCells A ++ flagCells B ++ flagCells C

/-- Real input cells of a real three-matrix instance: parameters, then the values of `A`, `B`, `C`. -/
def triReals {n : ℕ} (params : List ℝ) (A B C : Mat ℝ n) : List ℝ :=
  params ++ valueCells A ++ valueCells B ++ valueCells C

/-- Integer input cells of an integer three-matrix instance: parameters, flags, then values. -/
def intTriInts {n : ℕ} (params : List ℤ) (X Y Z : Mat ℤ n) : List ℤ :=
  params ++ flagCells X ++ flagCells Y ++ flagCells Z ++ valueCells X ++ valueCells Y ++ valueCells Z

/-- The weight `A[i,k] + B[k,j] + C[i,j]`, or ⊥ if an entry is missing. -/
def triSum {n : ℕ} (A B C : Mat ℝ n) (i k j : Fin n) : Option ℝ :=
  match A i k, B k j, C i j with
  | some a, some b, some c => some (a + b + c)
  | _, _, _ => none

/-- A negative triangle (Problems 3.3, 3.4, p.10). -/
def IsNegTri {n : ℕ} (A B C : Mat ℝ n) (i k j : Fin n) : Prop :=
  ∃ x, triSum A B C i k j = some x ∧ x < 0

/-- A `∆`-approximate triangle, that is `A[i,k] + B[k,j] + C[i,j] = 0 ± ∆` (§5.1, p.16). At `∆ = 0` it is an
exact triangle. -/
def IsApproxTri {n : ℕ} (Δ : ℝ) (A B C : Mat ℝ n) (i k j : Fin n) : Prop :=
  ∃ x, triSum A B C i k j = some x ∧ |x| ≤ Δ

/-- A triple of `[n]³`. -/
abbrev Triple (n : ℕ) : Type := Fin n × Fin n × Fin n

open Classical in
/-- The number of `∆`-approximate solutions. -/
noncomputable def approxCount {n : ℕ} (Δ : ℝ) (A B C : Mat ℝ n) : ℕ :=
  (Finset.univ.filter fun t : Triple n => IsApproxTri Δ A B C t.1 t.2.1 t.2.2).card

open Classical in
/-- The number of negative triangles. -/
noncomputable def negCount {n : ℕ} (A B C : Mat ℝ n) : ℕ :=
  (Finset.univ.filter fun t : Triple n => IsNegTri A B C t.1 t.2.1 t.2.2).card

open Classical in
/-- The number of `∞`-approximate solutions: triples with all three entries present. -/
noncomputable def presentCount {n : ℕ} (A B C : Mat ℝ n) : ℕ :=
  (Finset.univ.filter fun t : Triple n => (triSum A B C t.1 t.2.1 t.2.2).isSome = true).card

open Classical in
/-- The number of `∆`-approximate solutions through the `A`-edge `(i, k)`. -/
noncomputable def edgeCountA {n : ℕ} (Δ : ℝ) (A B C : Mat ℝ n) (i k : Fin n) : ℕ :=
  (Finset.univ.filter fun j : Fin n => IsApproxTri Δ A B C i k j).card

open Classical in
/-- The number of `∆`-approximate solutions through the `B`-edge `(k, j)`. -/
noncomputable def edgeCountB {n : ℕ} (Δ : ℝ) (A B C : Mat ℝ n) (k j : Fin n) : ℕ :=
  (Finset.univ.filter fun i : Fin n => IsApproxTri Δ A B C i k j).card

open Classical in
/-- The number of `∆`-approximate solutions through the `C`-edge `(i, j)`. -/
noncomputable def edgeCountC {n : ℕ} (Δ : ℝ) (A B C : Mat ℝ n) (i j : Fin n) : ℕ :=
  (Finset.univ.filter fun k : Fin n => IsApproxTri Δ A B C i k j).card

/-- A marking of the entries of the three matrices as popular (index `0`, `1`, `2` for `A`, `B`, `C`). -/
abbrev Marking (n : ℕ) : Type := Fin 3 → Fin n → Fin n → Prop

/-- All three edges of `(i, k, j)` are popular. -/
def AllPopular {n : ℕ} (pop : Marking n) (i k j : Fin n) : Prop :=
  pop 0 i k ∧ pop 1 k j ∧ pop 2 i j

open Classical in
/-- Solutions of type 1 (p.17): `∆`-approximate solutions with only popular edges. -/
noncomputable def popularCount {n : ℕ} (Δ : ℝ) (pop : Marking n) (A B C : Mat ℝ n) : ℕ :=
  (Finset.univ.filter fun t : Triple n =>
    IsApproxTri Δ A B C t.1 t.2.1 t.2.2 ∧ AllPopular pop t.1 t.2.1 t.2.2).card

open Classical in
/-- Solutions of types 2 and 3 (p.17): `∆`-approximate solutions involving an unpopular edge. -/
noncomputable def unpopularCount {n : ℕ} (Δ : ℝ) (pop : Marking n) (A B C : Mat ℝ n) : ℕ :=
  (Finset.univ.filter fun t : Triple n =>
    IsApproxTri Δ A B C t.1 t.2.1 t.2.2 ∧ ¬ AllPopular pop t.1 t.2.1 t.2.2).card

/-- The triple `t` is written in three consecutive output cells from `base`. -/
def TripleAt {n : ℕ} (σ : State) (base : ℕ) (t : Triple n) : Prop :=
  σ.imem (outCell base) = ((t.1 : ℕ) : ℤ) ∧ σ.imem (outCell (base + 1)) = ((t.2.1 : ℕ) : ℤ) ∧
    σ.imem (outCell (base + 2)) = ((t.2.2 : ℕ) : ℤ)

open Classical in
/-- The set of triples reported by a list of length `len` from output cell `base`, three cells each. -/
noncomputable def reportedTriples (n : ℕ) (σ : State) (base len : ℕ) : Finset (Triple n) :=
  Finset.univ.filter fun t : Triple n => ∃ l < len, TripleAt σ (base + 3 * l) t

/-- The matrix with index `m`: `0`, `1`, `2` for `A`, `B`, `C`. -/
def pick {n : ℕ} (m : Fin 3) (A B C : Mat ℝ n) : Mat ℝ n := ![A, B, C] m

end RealAPSP


