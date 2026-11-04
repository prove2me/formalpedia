-- Prove2me | Definitions.Def_QMCLeafB_MatQ
-- name    : QMCLeafB_MatQ
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T22:26:13.336948+00:00
-- url     : https://prove2.me/theorems/ceb1b014-3af2-4483-911b-02e1098129ee
-- title:
--   QMCLeafB MatQ
-- statement:
--   The Check_MatQ module of the QMCLeafB library.
--
--   Published as part of the QMCLeafB library mirror supporting the quantum max-cut campaign's polynomial-time SDP-value certificate (AGM20, TQC 2020, arXiv 2003.14394).

import Mathlib
import Definitions.Def_QuantumMaxCutFiniteNumericRuntime

/-!
# Leaf B, brick `matq`: row-major rational matrices over `List ℚ`

Self-contained deliverable for the `brick-matq` piece of the certified polynomial-time
SDP lower-value program of the 0.53 Quantum Max-Cut campaign.  Imports only `Mathlib` and
`Definitions.Def_QuantumMaxCutFiniteNumericRuntime` (the platform's allowed surface).

## Layer (i): storage + correctness against `Mathlib.Matrix`

Storage is row-major: `entry n xs i j = xs.getD (i*n+j) 0`.
`MatQ.mk n f` is the row-major builder; the read-back theorem is
`MatQ.mk_getD (hj : j < n) : (mk n f).getD (i*n+j) 0 = if i < n then f i j else 0`,
from which `MatQ.entry_mk (hi : i<n) (hj : j<n) : entry n (mk n f) i j = f i j`.

The predicate `MatQ.correct n M xs` says `xs` is the row-major code of
`M : Matrix (Fin n) (Fin n) ℚ` (length `n*n` plus entrywise agreement), and every operation
comes with a `correct`-preservation theorem:

| op | definition | correctness |
|---|---|---|
| `MatQ.sum` | sum of all entries | `MatQ.sum_eq : sum n xs = ∑ i, ∑ j, M i j` |
| `MatQ.trace` | trace | `MatQ.trace_eq : trace n xs = M.trace` |
| `MatQ.add` / `sub` / `neg` | entrywise | `correct_add` / `correct_sub` / `correct_neg` |
| `MatQ.smul` | scalar | `correct_smul` |
| `MatQ.transpose` | transpose | `correct_transpose` |
| `MatQ.mul` | product | `correct_mul` |
| `MatQ.mulVec` / `vecMul` | matrix–vector | `correct_mulVec` / `correct_vecMul` |
| `MatQ.dot` | rational inner product | `dot_eq : dot n ys zs = dotProduct v w` |
| `MatQ.qform` | `vᵀ M v` | `qform_eq : qform n xs ys = dotProduct v (Matrix.mulVec M v)` |
| `MatQ.diagOfVec` | diagonal | `correct_diagOfVec` |
| `MatQ.ident` / `zero` | identity / zero | `correct_ident` / `correct_zero` |
| `MatQ.trProd` | `∑ᵢ ∑ⱼ Aᵢⱼ Xⱼᵢ` | `trProd_eq : trProd n xs ys = (M * N).trace` |

Also `MatQ.ofMatrix` / `correct_ofMatrix` (every matrix has a code), `MatQ.toMatrix`
(the matrix read off a code), `MatQ.correct_iff` (a code is correct iff `toMatrix = M`) and
`MatQ.correct_unique` (a code determines the matrix).

**Interface note for the coordinator.** Everything is in `namespace MatQ`; aliasing only
needs the names above.  `MatQ.correct` is a `Prop`, so it is safe to keep as a hypothesis.

## Layer (ii): runtime

Each program is an explicit `PolyProgram.comp` chain of the library's machines
(`natMul`, `natAdd`, `ratMul`, `ratSum`, `listTake`, `listGetD`, `listIndices`,
`listMapWith`, `listFlatMapWith`, `listZipWith`, `fst`, `snd`, `fanout`, `identity`);
the time bound is whatever the framework's `compTime`/`sizeBound` give (`PolyProgram.time`,
`PolyProgram.sizeBound`, `PolyProgram.length_bound`), never hand-optimised.

Programs (`MatQ.Runtime`), all on the packed inputs
`ESt = (List ℚ × ℕ) × ℕ × ℕ` (a list, `n`, `i`, `j`), `MSt = ℕ × List ℚ` (`n`, `A`)
and `VSt = ℕ × List ℚ × List ℚ` (`n`, `A`, `B`):

| program | computes | specification |
|---|---|---|
| `entryProgram` | `A[i*n+j]` | `entryProgram_spec` |
| `dotProgram` | `∑ₖ vₖ wₖ` | (states `dot` directly) |
| `traceProgram` | `∑ᵢ A[i*n+i]` | `traceProgram_spec` |
| `sumProgram` | `∑ᵢ ∑ⱼ A[i*n+j]` | `sumProgram_spec` |
| `trProdProgram` | `∑ᵢ ∑ⱼ A[i*n+j]·B[j*n+i]` | `trProdProgram_spec` |
| `mulVecProgram` | `A·v` (list of row inner products) | `mulVecProgram_spec` |
| `addProgram` | `A + B` | `addProgram_spec` |
| `transposeProgram` | `Aᵀ` | `transposeProgram_spec` |
| `gapProgram` | `V(A) − tr(A B)` | `gapProgram_spec` |

The `_spec` theorems relate each machine to the layer-(i) operation under the evident
length hypotheses (`A.length = n*n` for matrices, `v.length = n` for vectors); the machines
themselves are total and compute the "raw" function (row index list built as
`List.range (A.take n).length`, which is `List.range n` exactly under those hypotheses,
lemma `MatQ.Runtime.range_take` / `m_idx_spec'`).
`MatQ.Runtime.{traceProgram,dotProgram,mulVecProgram}_length_bound` record the framework's
polynomial output-size bound (`PolyProgram.length_bound`).

**Not covered here** (same pattern, left to the assembly if needed): the `PolyProgram`s for
`smul`/`sub`/`neg`/`mul`/`vecMul`/`diagOfVec`, and the numerical search for the certified
pair (the ellipsoid brick's job). Everything of layer (i) is complete.

**Trap (important, contradicted by the platform probe).** `fun_prop`-driven synthesis of
`Poly` does *not* work for list-mapped functions with this library version: the
`list_map`/`list_flatMap` rules fail to instantiate (`Poly fun x => x.1.1 x.2`).
The platform's own `Solutions/Check_PolyProbe.lean` fails to compile for this reason.
All runtime content here is therefore written as explicit `PolyProgram` chains.
-/

namespace MatQ

/-! ## 1. Storage and the row-major builder -/

/-- Entry `(i,j)` of the row-major `n × n` matrix stored in `xs`. -/
def entry (n : ℕ) (xs : List ℚ) (i j : ℕ) : ℚ := xs.getD (i * n + j) 0

/-- The row-major list of the `n × n` matrix with entries `f i j`. -/
def mk (n : ℕ) (f : ℕ → ℕ → ℚ) : List ℚ :=
  (List.range n).flatMap (fun i => (List.range n).map (fun j => f i j))

theorem mk_eq_flatten (n : ℕ) (f : ℕ → ℕ → ℚ) :
    mk n f = ((List.range n).map (fun i => (List.range n).map (fun j => f i j))).flatten :=
  rfl

/-! ## 2. Reading the builder back -/

theorem length_flatten_blocks (m : ℕ) :
    ∀ (bs : List (List ℚ)), (∀ b ∈ bs, b.length = m) → bs.flatten.length = m * bs.length
  | [], _ => by simp
  | b :: bs, h => by
    have hb : b.length = m := h b (by simp)
    have hbs : ∀ c ∈ bs, c.length = m := fun c hc => h c (by simp [hc])
    rw [List.flatten_cons, List.length_append, hb, length_flatten_blocks m bs hbs,
      List.length_cons]
    ring

theorem mk_length (n : ℕ) (f : ℕ → ℕ → ℚ) : (mk n f).length = n * n := by
  rw [mk_eq_flatten,
    length_flatten_blocks n ((List.range n).map (fun i => (List.range n).map (fun j => f i j)))
      (by
        intro b hb
        obtain ⟨i, -, rfl⟩ := List.mem_map.mp hb
        simp)]
  simp

theorem getElem?_map_range {β : Type} (n : ℕ) (g : ℕ → β) (i : ℕ) :
    ((List.range n).map g)[i]? = if i < n then some (g i) else none := by
  rw [List.getElem?_map]
  split_ifs with h
  · rw [List.getElem?_range h]; rfl
  · rw [List.getElem?_eq_none (by simp; omega)]
    rfl

theorem getD_map_range {β : Type} (n : ℕ) (g : ℕ → β) (d : β) {j : ℕ} (hj : j < n) :
    ((List.range n).map g).getD j d = g j := by
  rw [List.getD_eq_getElem?_getD, getElem?_map_range n g j, if_pos hj]
  rfl

theorem getD_flatten_blocks (m : ℕ) :
    ∀ (bs : List (List ℚ)) (i j : ℕ), (∀ b ∈ bs, b.length = m) → j < m →
      bs.flatten.getD (i * m + j) 0 = (bs[i]?.getD []).getD j 0
  | [], i, j, _, _ => by simp
  | b :: bs, i, j, hlen, hj => by
    have hb : b.length = m := hlen b (by simp)
    have hbs : ∀ c ∈ bs, c.length = m := fun c hc => hlen c (by simp [hc])
    rw [List.flatten_cons]
    cases i with
    | zero =>
      have hlt : j < b.length := by rw [hb]; exact hj
      have hstep := List.getD_append b bs.flatten (0 : ℚ) j hlt
      rw [Nat.zero_mul, Nat.zero_add, hstep]
      simp
    | succ i' =>
      have hmul : m ≤ (i' + 1) * m := Nat.le_mul_of_pos_left m (Nat.succ_pos i')
      have hle : b.length ≤ (i' + 1) * m + j := by rw [hb]; omega
      have hstep := List.getD_append_right b bs.flatten (0 : ℚ) ((i' + 1) * m + j) hle
      rw [hstep, hb]
      have hidx : (i' + 1) * m + j - m = i' * m + j := by
        rw [Nat.succ_mul]; omega
      rw [hidx, getD_flatten_blocks m bs i' j hbs hj]
      simp

/-- Reading back the builder: for in-range indices, `entry (mk n f) i j = f i j`. -/
theorem mk_getD (n : ℕ) (f : ℕ → ℕ → ℚ) {i j : ℕ} (hj : j < n) :
    (mk n f).getD (i * n + j) 0 = if i < n then f i j else 0 := by
  rw [mk_eq_flatten,
    getD_flatten_blocks n _ i j
      (by
        intro b hb
        obtain ⟨k, -, rfl⟩ := List.mem_map.mp hb
        simp) hj]
  split_ifs with hi
  · rw [getElem?_map_range, if_pos hi]
    exact getD_map_range n (fun j => f i j) 0 hj
  · rw [getElem?_map_range, if_neg hi]
    rfl

/-- The central read-back lemma. -/
theorem entry_mk (n : ℕ) (f : ℕ → ℕ → ℚ) {i j : ℕ} (hi : i < n) (hj : j < n) :
    entry n (mk n f) i j = f i j := by
  rw [entry, mk_getD n f hj, if_pos hi]

theorem mk_inj {n : ℕ} {f g : ℕ → ℕ → ℚ} (h : mk n f = mk n g) :
    ∀ {i j : ℕ}, i < n → j < n → f i j = g i j := by
  intro i j hi hj
  rw [← entry_mk n f hi hj, h, entry_mk n g hi hj]

/-! ## 3. The operations -/

/-- Sum of all entries. -/
def sum (n : ℕ) (xs : List ℚ) : ℚ :=
  ((List.range n).flatMap (fun i => (List.range n).map (fun j => entry n xs i j))).sum

/-- Trace. -/
def trace (n : ℕ) (xs : List ℚ) : ℚ :=
  (List.range n).map (fun i => entry n xs i i) |>.sum

/-- Entrywise sum. -/
def add (n : ℕ) (xs ys : List ℚ) : List ℚ :=
  mk n (fun i j => entry n xs i j + entry n ys i j)

/-- Scalar multiple. -/
def smul (c : ℚ) (n : ℕ) (xs : List ℚ) : List ℚ :=
  mk n (fun i j => c * entry n xs i j)

/-- Negative. -/
def neg (n : ℕ) (xs : List ℚ) : List ℚ := smul (-1) n xs

/-- Difference. -/
def sub (n : ℕ) (xs ys : List ℚ) : List ℚ := add n xs (neg n ys)

/-- Transpose. -/
def transpose (n : ℕ) (xs : List ℚ) : List ℚ :=
  mk n (fun i j => entry n xs j i)

/-- Matrix product. -/
def mul (n : ℕ) (xs ys : List ℚ) : List ℚ :=
  mk n (fun i j => ((List.range n).map (fun k => entry n xs i k * entry n ys k j)).sum)

/-- Matrix times vector. -/
def mulVec (n : ℕ) (xs ys : List ℚ) : List ℚ :=
  (List.range n).map (fun i => ((List.range n).map
    (fun k => entry n xs i k * ys.getD k 0)).sum)

/-- Vector times matrix. -/
def vecMul (n : ℕ) (ys xs : List ℚ) : List ℚ :=
  (List.range n).map (fun j => ((List.range n).map
    (fun k => ys.getD k 0 * entry n xs k j)).sum)

/-- Dot product of two vectors given as lists. -/
def dot (n : ℕ) (ys zs : List ℚ) : ℚ :=
  ((List.range n).map (fun k => ys.getD k 0 * zs.getD k 0)).sum

/-- The quadratic form `vᵀ M v`. -/
def qform (n : ℕ) (xs ys : List ℚ) : ℚ :=
  ((List.range n).map (fun i => ys.getD i 0 *
    ((List.range n).map (fun k => entry n xs i k * ys.getD k 0)).sum)).sum

/-- Diagonal matrix from a vector. -/
def diagOfVec (n : ℕ) (ys : List ℚ) : List ℚ :=
  mk n (fun i j => if i = j then ys.getD i 0 else 0)

/-- Identity matrix. -/
def ident (n : ℕ) : List ℚ := mk n (fun i j => if i = j then 1 else 0)

/-- Zero matrix. -/
def zero (n : ℕ) : List ℚ := mk n (fun _ _ => 0)

/-! ## 4. The correctness predicate -/

/-- `xs` is the row-major code of the `n × n` matrix `M`. -/
def correct (n : ℕ) (M : Matrix (Fin n) (Fin n) ℚ) (xs : List ℚ) : Prop :=
  xs.length = n * n ∧ ∀ i j : Fin n, entry n xs i j = M i j

/-- `xs` is the code of the vector `v`. -/
def correctVec (n : ℕ) (v : Fin n → ℚ) (xs : List ℚ) : Prop :=
  xs.length = n ∧ ∀ i : Fin n, xs.getD i 0 = v i

/-- The matrix read off a row-major list. -/
def toMatrix (n : ℕ) (xs : List ℚ) : Matrix (Fin n) (Fin n) ℚ :=
  Matrix.of (fun i j => entry n xs i j)

theorem correct_iff {n : ℕ} {M : Matrix (Fin n) (Fin n) ℚ} {xs : List ℚ} :
    correct n M xs ↔ xs.length = n * n ∧ toMatrix n xs = M := by
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨h1, ?_⟩
    ext i j
    exact h2 i j
  · rintro ⟨h1, h2⟩
    refine ⟨h1, fun i j => ?_⟩
    rw [← h2]
    rfl

theorem toMatrix_correct {n : ℕ} {xs : List ℚ} (h : xs.length = n * n) :
    correct n (toMatrix n xs) xs :=
  correct_iff.mpr ⟨h, rfl⟩

theorem correct_length {n : ℕ} {M : Matrix (Fin n) (Fin n) ℚ} {xs : List ℚ}
    (h : correct n M xs) : xs.length = n * n := h.1

theorem correct_entry {n : ℕ} {M : Matrix (Fin n) (Fin n) ℚ} {xs : List ℚ}
    (h : correct n M xs) (i j : Fin n) : entry n xs i j = M i j := h.2 i j

theorem correct_unique {n : ℕ} {M N : Matrix (Fin n) (Fin n) ℚ} {xs : List ℚ}
    (hM : correct n M xs) (hN : correct n N xs) : M = N := by
  have h1 : toMatrix n xs = M := (correct_iff.mp hM).2
  have h2 : toMatrix n xs = N := (correct_iff.mp hN).2
  rw [← h1, ← h2]

theorem correct_vec_ext {n : ℕ} {v : Fin n → ℚ} {xs : List ℚ} (h : correctVec n v xs) :
    ∀ i : Fin n, xs.getD i 0 = v i := h.2

/-! ## 5. Correctness of the operations -/

theorem entry_add (n : ℕ) (xs ys : List ℚ) {i j : ℕ} (hi : i < n) (hj : j < n) :
    entry n (add n xs ys) i j = entry n xs i j + entry n ys i j := entry_mk n _ hi hj

theorem add_length (n : ℕ) (xs ys : List ℚ) : (add n xs ys).length = n * n := mk_length n _

theorem entry_smul (c : ℚ) (n : ℕ) (xs : List ℚ) {i j : ℕ} (hi : i < n) (hj : j < n) :
    entry n (smul c n xs) i j = c * entry n xs i j := entry_mk n _ hi hj

theorem smul_length (c : ℚ) (n : ℕ) (xs : List ℚ) : (smul c n xs).length = n * n :=
  mk_length n _

theorem entry_neg (n : ℕ) (xs : List ℚ) {i j : ℕ} (hi : i < n) (hj : j < n) :
    entry n (neg n xs) i j = -entry n xs i j := by
  rw [neg, entry_smul _ _ _ hi hj]; ring

theorem entry_transpose (n : ℕ) (xs : List ℚ) {i j : ℕ} (hi : i < n) (hj : j < n) :
    entry n (transpose n xs) i j = entry n xs j i := entry_mk n _ hi hj

theorem transpose_length (n : ℕ) (xs : List ℚ) : (transpose n xs).length = n * n :=
  mk_length n _

theorem entry_mul (n : ℕ) (xs ys : List ℚ) {i j : ℕ} (hi : i < n) (hj : j < n) :
    entry n (mul n xs ys) i j =
      ((List.range n).map (fun k => entry n xs i k * entry n ys k j)).sum :=
  entry_mk n _ hi hj

theorem mul_length (n : ℕ) (xs ys : List ℚ) : (mul n xs ys).length = n * n := mk_length n _

theorem entry_diagOfVec (n : ℕ) (ys : List ℚ) {i j : ℕ} (hi : i < n) (hj : j < n) :
    entry n (diagOfVec n ys) i j = if i = j then ys.getD i 0 else 0 := entry_mk n _ hi hj

theorem diagOfVec_length (n : ℕ) (ys : List ℚ) : (diagOfVec n ys).length = n * n :=
  mk_length n _

theorem ident_length (n : ℕ) : (ident n).length = n * n := mk_length n _

theorem entry_ident (n : ℕ) {i j : ℕ} (hi : i < n) (hj : j < n) :
    entry n (ident n) i j = if i = j then 1 else 0 := entry_mk n _ hi hj

theorem mulVec_length (n : ℕ) (xs ys : List ℚ) : (mulVec n xs ys).length = n := by
  simp [mulVec]

theorem vecMul_length (n : ℕ) (ys xs : List ℚ) : (vecMul n ys xs).length = n := by
  simp [vecMul]

theorem mulVec_getD (n : ℕ) (xs ys : List ℚ) {i : ℕ} (hi : i < n) :
    (mulVec n xs ys).getD i 0 =
      ((List.range n).map (fun k => entry n xs i k * ys.getD k 0)).sum := by
  rw [mulVec, getD_map_range n _ 0 hi]

theorem vecMul_getD (n : ℕ) (ys xs : List ℚ) {j : ℕ} (hj : j < n) :
    (vecMul n ys xs).getD j 0 =
      ((List.range n).map (fun k => ys.getD k 0 * entry n xs k j)).sum := by
  rw [vecMul, getD_map_range n _ 0 hj]

/-- `List.range` sums are `Fin`-sums. -/
theorem list_sum_range (g : ℕ → ℚ) : ∀ n : ℕ, ((List.range n).map g).sum = ∑ i : Fin n, g i
  | 0 => by simp
  | n + 1 => by
    rw [List.range_succ, List.map_append, List.sum_append, list_sum_range g n,
      Fin.sum_univ_castSucc]
    simp

/-- Summing a `flatMap` over `List.range` is summing the blocks. -/
theorem sum_flatMap_range (h : ℕ → List ℚ) :
    ∀ n : ℕ, ((List.range n).flatMap h).sum = ∑ i : Fin n, (h i).sum
  | 0 => by simp
  | n + 1 => by
    have hlast : (List.flatMap h [n]).sum = (h n).sum := by simp
    rw [List.range_succ, List.flatMap_append, List.sum_append,
      sum_flatMap_range h n, Fin.sum_univ_castSucc, hlast]
    rfl

theorem trace_eq (n : ℕ) (xs : List ℚ) {M : Matrix (Fin n) (Fin n) ℚ}
    (h : correct n M xs) : trace n xs = M.trace := by
  rw [trace, Matrix.trace, list_sum_range (fun i => entry n xs i i)]
  exact Finset.sum_congr rfl fun i _ => h.2 i i

theorem sum_eq (n : ℕ) (xs : List ℚ) {M : Matrix (Fin n) (Fin n) ℚ}
    (h : correct n M xs) : sum n xs = ∑ i : Fin n, ∑ j : Fin n, M i j := by
  rw [sum, sum_flatMap_range]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [list_sum_range]
  exact Finset.sum_congr rfl fun j _ => h.2 i j


/-! ## 6. `ofMatrix`: every matrix has a code -/

/-- The row-major code of `M`. -/
def ofMatrix (n : ℕ) (M : Matrix (Fin n) (Fin n) ℚ) : List ℚ :=
  mk n (fun i j => if h : i < n ∧ j < n then M ⟨i, h.1⟩ ⟨j, h.2⟩ else 0)

theorem ofMatrix_length (n : ℕ) (M : Matrix (Fin n) (Fin n) ℚ) :
    (ofMatrix n M).length = n * n := mk_length n _

theorem entry_ofMatrix (n : ℕ) (M : Matrix (Fin n) (Fin n) ℚ) (i j : Fin n) :
    entry n (ofMatrix n M) i j = M i j := by
  rw [ofMatrix, entry_mk n _ i.isLt j.isLt,
    dif_pos (show (i : ℕ) < n ∧ (j : ℕ) < n from ⟨i.isLt, j.isLt⟩)]

theorem correct_ofMatrix (n : ℕ) (M : Matrix (Fin n) (Fin n) ℚ) : correct n M (ofMatrix n M) :=
  ⟨ofMatrix_length n M, fun i j => entry_ofMatrix n M i j⟩

theorem correct_iff_toMatrix {n : ℕ} {M : Matrix (Fin n) (Fin n) ℚ} {xs : List ℚ} :
    correct n M xs ↔ xs.length = n * n ∧ toMatrix n xs = M := correct_iff

/-! ## 7. Correctness of the operations -/

theorem correct_zero (n : ℕ) : correct n (0 : Matrix (Fin n) (Fin n) ℚ) (zero n) := by
  refine ⟨mk_length n _, fun i j => ?_⟩
  rw [zero, entry_mk n _ i.isLt j.isLt]
  rfl

theorem correct_ident (n : ℕ) : correct n (1 : Matrix (Fin n) (Fin n) ℚ) (ident n) := by
  refine ⟨ident_length n, fun i j => ?_⟩
  rw [entry_ident n i.isLt j.isLt, Matrix.one_apply]
  by_cases h : i = j
  · simp [h]
  · have h' : ¬((i : ℕ) = (j : ℕ)) := fun hh => h (Fin.ext hh)
    simp [h, h']

theorem correct_add {n : ℕ} {M N : Matrix (Fin n) (Fin n) ℚ} {xs ys : List ℚ}
    (hx : correct n M xs) (hy : correct n N ys) : correct n (M + N) (add n xs ys) := by
  refine ⟨add_length n xs ys, fun i j => ?_⟩
  rw [entry_add n xs ys i.isLt j.isLt, hx.2 i j, hy.2 i j]
  rfl

theorem correct_smul (c : ℚ) {n : ℕ} {M : Matrix (Fin n) (Fin n) ℚ} {xs : List ℚ}
    (hx : correct n M xs) : correct n (c • M) (smul c n xs) := by
  refine ⟨smul_length c n xs, fun i j => ?_⟩
  rw [entry_smul c n xs i.isLt j.isLt, hx.2 i j]
  rfl

theorem correct_neg {n : ℕ} {M : Matrix (Fin n) (Fin n) ℚ} {xs : List ℚ}
    (hx : correct n M xs) : correct n (-M) (neg n xs) := by
  have h := correct_smul (-1 : ℚ) hx
  have heq : (-1 : ℚ) • M = -M := neg_one_smul ℚ M
  rwa [heq] at h

theorem correct_sub {n : ℕ} {M N : Matrix (Fin n) (Fin n) ℚ} {xs ys : List ℚ}
    (hx : correct n M xs) (hy : correct n N ys) : correct n (M - N) (sub n xs ys) := by
  have h := correct_add hx (correct_neg hy)
  rw [sub, sub_eq_add_neg]
  exact h

theorem entry_sub (n : ℕ) (xs ys : List ℚ) {i j : ℕ} (hi : i < n) (hj : j < n) :
    entry n (sub n xs ys) i j = entry n xs i j - entry n ys i j := by
  rw [sub, entry_add n xs (neg n ys) hi hj, entry_neg n ys hi hj]
  ring

theorem correct_transpose {n : ℕ} {M : Matrix (Fin n) (Fin n) ℚ} {xs : List ℚ}
    (hx : correct n M xs) : correct n (Matrix.transpose M) (transpose n xs) := by
  refine ⟨transpose_length n xs, fun i j => ?_⟩
  rw [entry_transpose n xs i.isLt j.isLt, hx.2 j i]
  rfl

theorem correct_mul {n : ℕ} {M N : Matrix (Fin n) (Fin n) ℚ} {xs ys : List ℚ}
    (hx : correct n M xs) (hy : correct n N ys) : correct n (M * N) (mul n xs ys) := by
  refine ⟨mul_length n xs ys, fun i j => ?_⟩
  rw [entry_mul n xs ys i.isLt j.isLt, list_sum_range, Matrix.mul_apply]
  exact Finset.sum_congr rfl fun k _ => by rw [hx.2 i k, hy.2 k j]

theorem correct_diagOfVec {n : ℕ} {v : Fin n → ℚ} {ys : List ℚ} (hy : correctVec n v ys) :
    correct n (Matrix.diagonal v) (diagOfVec n ys) := by
  refine ⟨diagOfVec_length n ys, fun i j => ?_⟩
  rw [entry_diagOfVec n ys i.isLt j.isLt, hy.2 i]
  show (if (i : ℕ) = (j : ℕ) then v i else 0) = Matrix.diagonal v i j
  rw [Matrix.diagonal, Matrix.of_apply]
  by_cases h : i = j
  · subst h; simp
  · have h' : ¬((i : ℕ) = (j : ℕ)) := fun hh => h (Fin.ext hh)
    simp [h, h']

theorem correctVec_entry {n : ℕ} {v : Fin n → ℚ} {ys : List ℚ} (hy : correctVec n v ys)
    (i : Fin n) : entry n (diagOfVec n ys) i i = v i := by
  rw [entry_diagOfVec n ys i.isLt i.isLt, if_pos rfl, hy.2 i]

theorem correct_mulVec {n : ℕ} {M : Matrix (Fin n) (Fin n) ℚ} {v : Fin n → ℚ}
    {xs ys : List ℚ} (hx : correct n M xs) (hy : correctVec n v ys) :
    correctVec n (Matrix.mulVec M v) (mulVec n xs ys) := by
  refine ⟨mulVec_length n xs ys, fun i => ?_⟩
  rw [mulVec_getD n xs ys i.isLt, list_sum_range]
  simp only [Matrix.mulVec, dotProduct]
  exact Finset.sum_congr rfl fun k _ => by rw [hx.2 i k, hy.2 k]

theorem correct_vecMul {n : ℕ} {M : Matrix (Fin n) (Fin n) ℚ} {v : Fin n → ℚ}
    {xs ys : List ℚ} (hx : correct n M xs) (hy : correctVec n v ys) :
    correctVec n (Matrix.vecMul v M) (vecMul n ys xs) := by
  refine ⟨vecMul_length n ys xs, fun j => ?_⟩
  rw [vecMul_getD n ys xs j.isLt, list_sum_range]
  simp only [Matrix.vecMul, dotProduct]
  exact Finset.sum_congr rfl fun k _ => by rw [hy.2 k, hx.2 k j]

theorem dot_eq {n : ℕ} {v w : Fin n → ℚ} {ys zs : List ℚ}
    (hy : correctVec n v ys) (hz : correctVec n w zs) : dot n ys zs = dotProduct v w := by
  rw [dot, list_sum_range]
  simp only [dotProduct]
  exact Finset.sum_congr rfl fun k _ => by rw [hy.2 k, hz.2 k]

theorem qform_eq {n : ℕ} {M : Matrix (Fin n) (Fin n) ℚ} {v : Fin n → ℚ}
    {xs ys : List ℚ} (hx : correct n M xs) (hy : correctVec n v ys) :
    qform n xs ys = dotProduct v (Matrix.mulVec M v) := by
  simp only [qform, Matrix.mulVec, dotProduct]
  rw [list_sum_range]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [list_sum_range, hy.2 i]
  congr 1
  exact Finset.sum_congr rfl fun k _ => by rw [hx.2 i k, hy.2 k]

theorem trace_mul_eq {n : ℕ} {M N : Matrix (Fin n) (Fin n) ℚ} {xs ys : List ℚ}
    (hx : correct n M xs) (hy : correct n N ys) : trace n (mul n xs ys) = (M * N).trace :=
  trace_eq n _ (correct_mul hx hy)

theorem trace_diagOfVec {n : ℕ} {v : Fin n → ℚ} {ys : List ℚ} (hy : correctVec n v ys) :
    trace n (diagOfVec n ys) = ∑ i, v i := by
  rw [trace, list_sum_range]
  exact Finset.sum_congr rfl fun i _ => correctVec_entry hy i

/-- The sum of all entries of a positive-semidefinite-diagonal-type matrix: the `V` of the leaf. -/
theorem sum_eq_sum (n : ℕ) (xs : List ℚ) {M : Matrix (Fin n) (Fin n) ℚ}
    (h : correct n M xs) : sum n xs = ∑ i, ∑ j, M i j := sum_eq n xs h

/-- `tr (A X)` as a double loop over the two row-major codes. -/
def trProd (n : ℕ) (xs ys : List ℚ) : ℚ :=
  ((List.range n).flatMap (fun i => (List.range n).map
    (fun j => entry n xs i j * entry n ys j i))).sum

theorem trProd_eq {n : ℕ} {M N : Matrix (Fin n) (Fin n) ℚ} {xs ys : List ℚ}
    (hx : correct n M xs) (hy : correct n N ys) : trProd n xs ys = (M * N).trace := by
  rw [trProd, sum_flatMap_range, Matrix.trace]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [list_sum_range, Matrix.diag_apply, Matrix.mul_apply]
  exact Finset.sum_congr rfl fun j _ => by rw [hx.2 i j, hy.2 j i]

theorem trProd_symm (n : ℕ) (xs ys : List ℚ) {M N : Matrix (Fin n) (Fin n) ℚ}
    (hx : correct n M xs) (hy : correct n N ys) : trProd n xs ys = trProd n ys xs := by
  rw [trProd_eq hx hy, trProd_eq hy hx, Matrix.trace_mul_comm]

/-! ## 8. Runtime layer: `PolyProgram`s for the storage operations

The platform library supplies machines for rational arithmetic and for the list
combinators; we compose them explicitly. `fun_prop`-driven synthesis of `Poly`
does *not* work for list-mapped functions in this library (the `list_map` /
`list_flatMap` rules fail to instantiate), so every program below is an explicit
`PolyProgram.comp` chain.
-/

namespace Runtime

open OAI.MetricKMedian.Binary
open OAI.MetricKMedian.Binary.PolyProgram
open OAI.MetricKMedian.Binary.Automatic

/-- Retarget a composed program along a pointwise equality of functions. -/
def prog_congr {α β : Type} {ea : α → List Bool} {eb : β → List Bool}
    {f g : α → β} (h : ∀ a, f a = g a) (P : PolyProgram ea eb f) : PolyProgram ea eb g :=
  P.congr g h

/-! ### Projections out of a nested pair -/

noncomputable def pfst {α β γ : Type} (ea : α → List Bool) (eb : β → List Bool)
    (ec : γ → List Bool) : PolyProgram (encodePair (encodePair ea eb) ec) ea (fun x => x.1.1) :=
  ((fst (encodePair ea eb) ec).comp (fst ea eb)).congr _ (fun _ => rfl)

noncomputable def pn {α β γ : Type} (ea : α → List Bool) (eb : β → List Bool)
    (ec : γ → List Bool) : PolyProgram (encodePair (encodePair ea eb) ec) eb (fun x => x.1.2) :=
  ((fst (encodePair ea eb) ec).comp (snd ea eb)).congr _ (fun _ => rfl)

noncomputable def pij {α β γ : Type} (ea : α → List Bool) (eb : β → List Bool)
    (ec : γ → List Bool) : PolyProgram (encodePair (encodePair ea eb) ec) ec (fun x => x.2) :=
  ((snd (encodePair ea eb) ec)).congr _ (fun _ => rfl)


/-! ### `entry`: look up `i*n + j` -/

/-- State of the entry program: `(xs, n, i, j)`. -/
abbrev ESt : Type := (List ℚ × ℕ) × ℕ × ℕ

noncomputable def e_xs : PolyProgram (encodePair (encodePair (encodeList Ratio.encode) Nat.bits)
    (encodePair Nat.bits Nat.bits)) (encodeList Ratio.encode) (fun p : ESt => p.1.1) :=
  pfst (encodeList Ratio.encode) Nat.bits (encodePair Nat.bits Nat.bits)

noncomputable def e_n : PolyProgram (encodePair (encodePair (encodeList Ratio.encode) Nat.bits)
    (encodePair Nat.bits Nat.bits)) Nat.bits (fun p : ESt => p.1.2) :=
  pn (encodeList Ratio.encode) Nat.bits (encodePair Nat.bits Nat.bits)

noncomputable def e_ij : PolyProgram (encodePair (encodePair (encodeList Ratio.encode) Nat.bits)
    (encodePair Nat.bits Nat.bits)) (encodePair Nat.bits Nat.bits) (fun p : ESt => p.2) :=
  pij (encodeList Ratio.encode) Nat.bits (encodePair Nat.bits Nat.bits)

noncomputable def e_i : PolyProgram (encodePair (encodePair (encodeList Ratio.encode) Nat.bits)
    (encodePair Nat.bits Nat.bits)) Nat.bits (fun p : ESt => p.2.1) :=
  (e_ij.comp (fst Nat.bits Nat.bits)).congr _ (fun _ => rfl)

noncomputable def e_j : PolyProgram (encodePair (encodePair (encodeList Ratio.encode) Nat.bits)
    (encodePair Nat.bits Nat.bits)) Nat.bits (fun p : ESt => p.2.2) :=
  (e_ij.comp (snd Nat.bits Nat.bits)).congr _ (fun _ => rfl)

noncomputable def e_in : PolyProgram (encodePair (encodePair (encodeList Ratio.encode) Nat.bits)
    (encodePair Nat.bits Nat.bits)) Nat.bits (fun p : ESt => p.2.1 * p.1.2) :=
  ((e_i.fanout e_n).comp natMul).congr _ (fun _ => rfl)

noncomputable def e_idx : PolyProgram (encodePair (encodePair (encodeList Ratio.encode) Nat.bits)
    (encodePair Nat.bits Nat.bits)) Nat.bits (fun p : ESt => p.2.1 * p.1.2 + p.2.2) :=
  ((e_in.fanout e_j).comp natAdd).congr _ (fun _ => rfl)

/-- The lookup machine: `xs[i*n+j]?` with default `0`. -/
noncomputable def entryProgram : PolyProgram (encodePair (encodePair (encodeList Ratio.encode) Nat.bits)
    (encodePair Nat.bits Nat.bits)) Ratio.encode
    (fun p : ESt => p.1.1[p.2.1 * p.1.2 + p.2.2]?.getD 0) :=
  ((e_xs.fanout e_idx).comp (listGetD (Ratio.encode) (0 : ℚ))).congr _ (fun _ => rfl)

/-- The lookup machine computes `MatQ.entry`. -/
theorem entryProgram_spec (n : ℕ) (xs : List ℚ) (i j : ℕ) :
    (fun p : ESt => p.1.1[p.2.1 * p.1.2 + p.2.2]?.getD 0) ((xs, n), i, j) = entry n xs i j := by
  simp only [entry, List.getD_eq_getElem?_getD]

/-! ### `dot`: the rational inner product of two lists -/

noncomputable def dotProgram : PolyProgram
    (encodePair (encodeList Ratio.encode) (encodeList Ratio.encode)) Ratio.encode
    (fun p : List ℚ × List ℚ => ((p.1.zip p.2).map (fun q : ℚ × ℚ => q.1 * q.2)).sum) :=
  ((listZipWith (ea := Ratio.encode) (eb := Ratio.encode) (ec := Ratio.encode)
    (a0 := (0 : ℚ)) (b0 := (0 : ℚ)) (f := fun q : ℚ × ℚ => q.1 * q.2) ratMul).comp ratSum).congr _
    (fun _ => rfl)


/-! ### The state `(n, xs)` and its index list -/

/-- State of the unary matrix programs: `(n, xs)`. -/
abbrev MSt : Type := ℕ × List ℚ

noncomputable def m_id : PolyProgram (enc (α := MSt)) (enc (α := MSt)) (fun p : MSt => p) :=
  identity (enc (α := MSt))

noncomputable def m_n : PolyProgram (enc (α := MSt)) Nat.bits (fun p : MSt => p.1) :=
  fst Nat.bits (encodeList Ratio.encode)

noncomputable def m_xs : PolyProgram (enc (α := MSt)) (encodeList Ratio.encode) (fun p : MSt => p.2) :=
  snd Nat.bits (encodeList Ratio.encode)

noncomputable def m_take : PolyProgram (enc (α := MSt)) (encodeList Ratio.encode)
    (fun p : MSt => p.2.take p.1) :=
  ((m_xs.fanout m_n).comp (listTake (Ratio.encode) (0 : ℚ))).congr _ (fun _ => rfl)

/-- The row index list `List.range n`, computed from `(n, xs)` as `List.range (xs.take n).length`. -/
noncomputable def m_idx : PolyProgram (enc (α := MSt)) (encodeList Nat.bits)
    (fun p : MSt => List.range (p.2.take p.1).length) :=
  ((m_take).comp (listIndices (Ratio.encode) (0 : ℚ))).congr _ (fun _ => rfl)

theorem m_idx_spec (n : ℕ) (xs : List ℚ) (h : xs.length = n * n) :
    List.range ((xs.take n).length) = List.range n := by
  have hmin : min n xs.length = n := by
    rcases Nat.eq_zero_or_pos n with h0 | h0
    · subst h0; simp
    · rw [h]; exact Nat.min_eq_left (Nat.le_mul_of_pos_left n h0)
  rw [List.length_take, hmin]

/-! ### `trace` -/

noncomputable def t_n : PolyProgram (encodePair (enc (α := MSt)) Nat.bits) Nat.bits (fun x : MSt × ℕ => x.1.1) :=
  pfst Nat.bits (encodeList Ratio.encode) Nat.bits

noncomputable def t_xs : PolyProgram (encodePair (enc (α := MSt)) Nat.bits) (encodeList Ratio.encode)
    (fun x : MSt × ℕ => x.1.2) :=
  pn Nat.bits (encodeList Ratio.encode) Nat.bits

noncomputable def t_i : PolyProgram (encodePair (enc (α := MSt)) Nat.bits) Nat.bits (fun x : MSt × ℕ => x.2) :=
  pij Nat.bits (encodeList Ratio.encode) Nat.bits

noncomputable def t_in : PolyProgram (encodePair (enc (α := MSt)) Nat.bits) Nat.bits
    (fun x : MSt × ℕ => x.2 * x.1.1) :=
  ((t_i.fanout t_n).comp natMul).congr _ (fun _ => rfl)

noncomputable def t_ii : PolyProgram (encodePair (enc (α := MSt)) Nat.bits) Nat.bits
    (fun x : MSt × ℕ => x.2 * x.1.1 + x.2) :=
  ((t_in.fanout t_i).comp natAdd).congr _ (fun _ => rfl)

noncomputable def t_elem : PolyProgram (encodePair (enc (α := MSt)) Nat.bits) Ratio.encode
    (fun x : MSt × ℕ => x.1.2[x.2 * x.1.1 + x.2]?.getD 0) :=
  ((t_xs.fanout t_ii).comp (listGetD (Ratio.encode) (0 : ℚ))).congr _ (fun _ => rfl)

/-- The trace machine. -/
noncomputable def traceProgram : PolyProgram (enc (α := MSt)) Ratio.encode
    (fun p : MSt => ((List.range (p.2.take p.1).length).map
      (fun i => p.2[i * p.1 + i]?.getD 0)).sum) :=
  (((m_id.fanout m_idx).comp (listMapWith (ea := Nat.bits) (ec := enc (α := MSt))
    (f := fun y : MSt × ℕ => y.1.2[y.2 * y.1.1 + y.2]?.getD 0) t_elem (a0 := 0) (b0 := (0 : ℚ)))).comp
    ratSum).congr _ (fun _ => rfl)

theorem traceProgram_spec (n : ℕ) (xs : List ℚ) (h : xs.length = n * n) :
    (fun p : MSt => ((List.range (p.2.take p.1).length).map
      (fun i => p.2[i * p.1 + i]?.getD 0)).sum) (n, xs) = trace n xs := by
  simp only [trace, m_idx_spec n xs h, entry, List.getD_eq_getElem?_getD]

/-! ### The two-matrix state `(n, xs, ys)` -/

abbrev VSt : Type := ℕ × (List ℚ × List ℚ)

noncomputable def v_id : PolyProgram (enc (α := VSt)) (enc (α := VSt)) (fun p : VSt => p) :=
  identity (enc (α := VSt))

noncomputable def v_n : PolyProgram (enc (α := VSt)) Nat.bits (fun p : VSt => p.1) :=
  fst Nat.bits (encodePair (encodeList Ratio.encode) (encodeList Ratio.encode))

noncomputable def v_2 : PolyProgram (enc (α := VSt)) (encodePair (encodeList Ratio.encode) (encodeList Ratio.encode))
    (fun p : VSt => p.2) :=
  snd Nat.bits (encodePair (encodeList Ratio.encode) (encodeList Ratio.encode))

noncomputable def v_xs : PolyProgram (enc (α := VSt)) (encodeList Ratio.encode) (fun p : VSt => p.2.1) :=
  (v_2.comp (fst (encodeList Ratio.encode) (encodeList Ratio.encode))).congr _ (fun _ => rfl)

noncomputable def v_ys : PolyProgram (enc (α := VSt)) (encodeList Ratio.encode) (fun p : VSt => p.2.2) :=
  (v_2.comp (snd (encodeList Ratio.encode) (encodeList Ratio.encode))).congr _ (fun _ => rfl)

noncomputable def v_ytake : PolyProgram (enc (α := VSt)) (encodeList Ratio.encode)
    (fun p : VSt => p.2.2.take p.1) :=
  ((v_ys.fanout v_n).comp (listTake (Ratio.encode) (0 : ℚ))).congr _ (fun _ => rfl)

noncomputable def v_xtake : PolyProgram (enc (α := VSt)) (encodeList Ratio.encode)
    (fun p : VSt => p.2.1.take p.1) :=
  ((v_xs.fanout v_n).comp (listTake (Ratio.encode) (0 : ℚ))).congr _ (fun _ => rfl)

noncomputable def v_yidx : PolyProgram (enc (α := VSt)) (encodeList Nat.bits)
    (fun p : VSt => List.range (p.2.2.take p.1).length) :=
  (v_ytake.comp (listIndices (Ratio.encode) (0 : ℚ))).congr _ (fun _ => rfl)

noncomputable def v_xidx : PolyProgram (enc (α := VSt)) (encodeList Nat.bits)
    (fun p : VSt => List.range (p.2.1.take p.1).length) :=
  (v_xtake.comp (listIndices (Ratio.encode) (0 : ℚ))).congr _ (fun _ => rfl)

/-! ### `sum`: the double loop `∑ᵢ ∑ⱼ xs[i*n+j]` -/

noncomputable def s_V : PolyProgram (encodePair (encodePair (enc (α := VSt)) Nat.bits) Nat.bits) (enc (α := VSt))
    (fun z : (VSt × ℕ) × ℕ => z.1.1) :=
  pfst (enc (α := VSt)) Nat.bits Nat.bits

noncomputable def s_i : PolyProgram (encodePair (encodePair (enc (α := VSt)) Nat.bits) Nat.bits) Nat.bits
    (fun z : (VSt × ℕ) × ℕ => z.1.2) :=
  pn (enc (α := VSt)) Nat.bits Nat.bits

noncomputable def s_j : PolyProgram (encodePair (encodePair (enc (α := VSt)) Nat.bits) Nat.bits) Nat.bits
    (fun z : (VSt × ℕ) × ℕ => z.2) :=
  pij (enc (α := VSt)) Nat.bits Nat.bits

noncomputable def s_n : PolyProgram (encodePair (encodePair (enc (α := VSt)) Nat.bits) Nat.bits) Nat.bits
    (fun z : (VSt × ℕ) × ℕ => z.1.1.1) :=
  (s_V.comp v_n).congr _ (fun _ => rfl)

noncomputable def s_xs : PolyProgram (encodePair (encodePair (enc (α := VSt)) Nat.bits) Nat.bits)
    (encodeList Ratio.encode) (fun z : (VSt × ℕ) × ℕ => z.1.1.2.1) :=
  (s_V.comp v_xs).congr _ (fun _ => rfl)

noncomputable def s_in : PolyProgram (encodePair (encodePair (enc (α := VSt)) Nat.bits) Nat.bits) Nat.bits
    (fun z : (VSt × ℕ) × ℕ => z.1.2 * z.1.1.1) :=
  ((s_i.fanout s_n).comp natMul).congr _ (fun _ => rfl)

noncomputable def s_idx : PolyProgram (encodePair (encodePair (enc (α := VSt)) Nat.bits) Nat.bits) Nat.bits
    (fun z : (VSt × ℕ) × ℕ => z.1.2 * z.1.1.1 + z.2) :=
  ((s_in.fanout s_j).comp natAdd).congr _ (fun _ => rfl)

noncomputable def s_elem : PolyProgram (encodePair (encodePair (enc (α := VSt)) Nat.bits) Nat.bits) Ratio.encode
    (fun z : (VSt × ℕ) × ℕ => z.1.1.2.1[z.1.2 * z.1.1.1 + z.2]?.getD 0) :=
  ((s_xs.fanout s_idx).comp (listGetD (Ratio.encode) (0 : ℚ))).congr _ (fun _ => rfl)

/-- One row of the sum: `List.range n |>.map (fun j => xs[i*n+j])`. -/
noncomputable def s_row : PolyProgram (encodePair (enc (α := VSt)) Nat.bits) (encodeList Ratio.encode)
    (fun y : VSt × ℕ => (List.range (y.1.2.2.take y.1.1).length).map
      (fun j => y.1.2.1[y.2 * y.1.1 + j]?.getD 0)) :=
  (((identity (encodePair (enc (α := VSt)) Nat.bits)).fanout
      ((fst (enc (α := VSt)) Nat.bits).comp v_yidx)).comp
    (listMapWith (ea := Nat.bits) (ec := encodePair (enc (α := VSt)) Nat.bits)
      (f := fun z : (VSt × ℕ) × ℕ => z.1.1.2.1[z.1.2 * z.1.1.1 + z.2]?.getD 0) s_elem
      (a0 := 0) (b0 := (0 : ℚ)))).congr _ (fun _ => rfl)

/-- The sum machine: `∑ᵢ ∑ⱼ xs[i*n+j]`. -/
noncomputable def sumProgram : PolyProgram (enc (α := VSt)) Ratio.encode
    (fun p : VSt => ((List.range (p.2.2.take p.1).length).flatMap
      (fun i => (List.range (p.2.2.take p.1).length).map
        (fun j => p.2.1[i * p.1 + j]?.getD 0))).sum) :=
  (((v_id.fanout v_yidx).comp
    (listFlatMapWith (ea := Nat.bits) (ec := enc (α := VSt))
      (f := fun y : VSt × ℕ => (List.range (y.1.2.2.take y.1.1).length).map
        (fun j => y.1.2.1[y.2 * y.1.1 + j]?.getD 0)) s_row
      (a0 := 0) (b0 := (0 : ℚ)))).comp ratSum).congr _ (fun _ => rfl)

theorem range_take (n : ℕ) (ys : List ℚ) (h : n ≤ ys.length) :
    List.range ((ys.take n).length) = List.range n := by
  rw [List.length_take, Nat.min_eq_left h]

theorem m_idx_spec' (n : ℕ) (xs : List ℚ) (h : xs.length = n * n) :
    List.range ((xs.take n).length) = List.range n := by
  refine range_take n xs ?_
  rw [h]
  rcases Nat.eq_zero_or_pos n with h0 | h0
  · subst h0; simp
  · exact Nat.le_mul_of_pos_left n h0

/-- The sum machine computes `MatQ.sum`. -/
theorem sumProgram_spec (n : ℕ) (xs ys : List ℚ) (_hx : xs.length = n * n)
    (h : ys.length = n * n) :
    (fun p : VSt => ((List.range (p.2.2.take p.1).length).flatMap
      (fun i => (List.range (p.2.2.take p.1).length).map
        (fun j => p.2.1[i * p.1 + j]?.getD 0))).sum) (n, xs, ys) = sum n xs := by
  simp only [sum, m_idx_spec' n ys h, entry, List.getD_eq_getElem?_getD]

/-! ### `trProd`: the double loop `∑ᵢ ∑ⱼ xs[i*n+j] * ys[j*n+i]` -/

noncomputable def s_ys : PolyProgram (encodePair (encodePair (enc (α := VSt)) Nat.bits) Nat.bits)
    (encodeList Ratio.encode) (fun z : (VSt × ℕ) × ℕ => z.1.1.2.2) :=
  (s_V.comp v_ys).congr _ (fun _ => rfl)

noncomputable def s_jn : PolyProgram (encodePair (encodePair (enc (α := VSt)) Nat.bits) Nat.bits) Nat.bits
    (fun z : (VSt × ℕ) × ℕ => z.2 * z.1.1.1) :=
  ((s_j.fanout s_n).comp natMul).congr _ (fun _ => rfl)

noncomputable def s_ji : PolyProgram (encodePair (encodePair (enc (α := VSt)) Nat.bits) Nat.bits) Nat.bits
    (fun z : (VSt × ℕ) × ℕ => z.2 * z.1.1.1 + z.1.2) :=
  ((s_jn.fanout s_i).comp natAdd).congr _ (fun _ => rfl)

noncomputable def t_yval : PolyProgram (encodePair (encodePair (enc (α := VSt)) Nat.bits) Nat.bits) Ratio.encode
    (fun z : (VSt × ℕ) × ℕ => z.1.1.2.2[z.2 * z.1.1.1 + z.1.2]?.getD 0) :=
  ((s_ys.fanout s_ji).comp (listGetD (Ratio.encode) (0 : ℚ))).congr _ (fun _ => rfl)

noncomputable def tp_elem : PolyProgram (encodePair (encodePair (enc (α := VSt)) Nat.bits) Nat.bits) Ratio.encode
    (fun z : (VSt × ℕ) × ℕ =>
      z.1.1.2.1[z.1.2 * z.1.1.1 + z.2]?.getD 0 * z.1.1.2.2[z.2 * z.1.1.1 + z.1.2]?.getD 0) :=
  ((s_elem.fanout t_yval).comp ratMul).congr _ (fun _ => rfl)

noncomputable def t_row : PolyProgram (encodePair (enc (α := VSt)) Nat.bits) (encodeList Ratio.encode)
    (fun y : VSt × ℕ => (List.range (y.1.2.2.take y.1.1).length).map
      (fun j => y.1.2.1[y.2 * y.1.1 + j]?.getD 0 * y.1.2.2[j * y.1.1 + y.2]?.getD 0)) :=
  (((identity (encodePair (enc (α := VSt)) Nat.bits)).fanout
      ((fst (enc (α := VSt)) Nat.bits).comp v_yidx)).comp
    (listMapWith (ea := Nat.bits) (ec := encodePair (enc (α := VSt)) Nat.bits)
      (f := fun z : (VSt × ℕ) × ℕ =>
        z.1.1.2.1[z.1.2 * z.1.1.1 + z.2]?.getD 0 * z.1.1.2.2[z.2 * z.1.1.1 + z.1.2]?.getD 0) tp_elem
      (a0 := 0) (b0 := (0 : ℚ)))).congr _ (fun _ => rfl)

noncomputable def trProdProgram : PolyProgram (enc (α := VSt)) Ratio.encode
    (fun p : VSt => ((List.range (p.2.2.take p.1).length).flatMap
      (fun i => (List.range (p.2.2.take p.1).length).map
        (fun j => p.2.1[i * p.1 + j]?.getD 0 * p.2.2[j * p.1 + i]?.getD 0))).sum) :=
  (((v_id.fanout v_yidx).comp
    (listFlatMapWith (ea := Nat.bits) (ec := enc (α := VSt))
      (f := fun y : VSt × ℕ => (List.range (y.1.2.2.take y.1.1).length).map
        (fun j => y.1.2.1[y.2 * y.1.1 + j]?.getD 0 * y.1.2.2[j * y.1.1 + y.2]?.getD 0)) t_row
      (a0 := 0) (b0 := (0 : ℚ)))).comp ratSum).congr _ (fun _ => rfl)

theorem trProdProgram_spec (n : ℕ) (xs ys : List ℚ) (_hx : xs.length = n * n)
    (h : ys.length = n * n) :
    (fun p : VSt => ((List.range (p.2.2.take p.1).length).flatMap
      (fun i => (List.range (p.2.2.take p.1).length).map
        (fun j => p.2.1[i * p.1 + j]?.getD 0 * p.2.2[j * p.1 + i]?.getD 0))).sum) (n, xs, ys)
      = trProd n xs ys := by
  simp only [trProd, m_idx_spec' n ys h, entry, List.getD_eq_getElem?_getD]

/-! ### `mulVec`: one inner product per row -/

noncomputable def m_yvalK : PolyProgram (encodePair (encodePair (enc (α := VSt)) Nat.bits) Nat.bits) Ratio.encode
    (fun z : (VSt × ℕ) × ℕ => z.1.1.2.2[z.2]?.getD 0) :=
  ((s_ys.fanout s_j).comp (listGetD (Ratio.encode) (0 : ℚ))).congr _ (fun _ => rfl)

noncomputable def mv_elem : PolyProgram (encodePair (encodePair (enc (α := VSt)) Nat.bits) Nat.bits) Ratio.encode
    (fun z : (VSt × ℕ) × ℕ => z.1.1.2.1[z.1.2 * z.1.1.1 + z.2]?.getD 0 * z.1.1.2.2[z.2]?.getD 0) :=
  ((s_elem.fanout m_yvalK).comp ratMul).congr _ (fun _ => rfl)

/-- One row-inner-product: `∑ₖ A[i*n+k] * v[k]`. -/
noncomputable def mv_row : PolyProgram (encodePair (enc (α := VSt)) Nat.bits) Ratio.encode
    (fun y : VSt × ℕ => List.sum ((List.range (y.1.2.2.take y.1.1).length).map
      (fun k => y.1.2.1[y.2 * y.1.1 + k]?.getD 0 * y.1.2.2[k]?.getD 0))) :=
  ((((identity (encodePair (enc (α := VSt)) Nat.bits)).fanout
      ((fst (enc (α := VSt)) Nat.bits).comp v_yidx)).comp
    (listMapWith (ea := Nat.bits) (ec := encodePair (enc (α := VSt)) Nat.bits)
      (f := fun z : (VSt × ℕ) × ℕ =>
        z.1.1.2.1[z.1.2 * z.1.1.1 + z.2]?.getD 0 * z.1.1.2.2[z.2]?.getD 0) mv_elem
      (a0 := 0) (b0 := (0 : ℚ)))).comp ratSum).congr _ (fun _ => rfl)

/-- The raw `mulVec` computation on the packed state. -/
def mulVecRaw (p : VSt) : List ℚ :=
  (List.range (p.2.2.take p.1).length).map
    (fun i => List.sum ((List.range (p.2.2.take p.1).length).map
      (fun k => p.2.1[i * p.1 + k]?.getD 0 * p.2.2[k]?.getD 0)))

noncomputable def mv_lmw : PolyProgram (encodePair (enc (α := VSt)) (encodeList Nat.bits))
    (encodeList Ratio.encode)
    (fun x : VSt × List ℕ => x.2.map (fun a => List.sum ((List.range (x.1.2.2.take x.1.1).length).map
      (fun k => x.1.2.1[a * x.1.1 + k]?.getD 0 * x.1.2.2[k]?.getD 0)))) :=
  listMapWith (ea := Nat.bits) (ec := enc (α := VSt))
    (f := fun y : VSt × ℕ => List.sum ((List.range (y.1.2.2.take y.1.1).length).map
      (fun k => y.1.2.1[y.2 * y.1.1 + k]?.getD 0 * y.1.2.2[k]?.getD 0))) mv_row
    (a0 := 0) (b0 := (0 : ℚ))

noncomputable def mulVecProgram : PolyProgram (enc (α := VSt)) (encodeList Ratio.encode) mulVecRaw :=
  ((v_id.fanout v_yidx).comp mv_lmw).congr _ (fun _ => rfl)

theorem mulVecProgram_spec (n : ℕ) (xs ys : List ℚ) (h : ys.length = n) :
    mulVecRaw (n, xs, ys) = mulVec n xs ys := by
  simp only [mulVecRaw, mulVec, range_take n ys (le_of_eq h.symm), entry,
    List.getD_eq_getElem?_getD]

/-! ### `add` and `transpose` (matrix-valued) and the leaf quantity `V - tr(AX)` -/

/-- Raw entrywise sum. -/
def addRaw (p : VSt) : List ℚ :=
  (List.range (p.2.2.take p.1).length).flatMap
    (fun i => (List.range (p.2.2.take p.1).length).map
      (fun j => p.2.1[i * p.1 + j]?.getD 0 + p.2.2[i * p.1 + j]?.getD 0))

noncomputable def a_yval : PolyProgram (encodePair (encodePair (enc (α := VSt)) Nat.bits) Nat.bits) Ratio.encode
    (fun z : (VSt × ℕ) × ℕ => z.1.1.2.2[z.1.2 * z.1.1.1 + z.2]?.getD 0) :=
  ((s_ys.fanout s_idx).comp (listGetD (Ratio.encode) (0 : ℚ))).congr _ (fun _ => rfl)

noncomputable def a_elem : PolyProgram (encodePair (encodePair (enc (α := VSt)) Nat.bits) Nat.bits) Ratio.encode
    (fun z : (VSt × ℕ) × ℕ => z.1.1.2.1[z.1.2 * z.1.1.1 + z.2]?.getD 0
      + z.1.1.2.2[z.1.2 * z.1.1.1 + z.2]?.getD 0) :=
  ((s_elem.fanout a_yval).comp ratAdd).congr _ (fun _ => rfl)

noncomputable def a_row : PolyProgram (encodePair (enc (α := VSt)) Nat.bits) (encodeList Ratio.encode)
    (fun y : VSt × ℕ => (List.range (y.1.2.2.take y.1.1).length).map
      (fun j => y.1.2.1[y.2 * y.1.1 + j]?.getD 0 + y.1.2.2[y.2 * y.1.1 + j]?.getD 0)) :=
  (((identity (encodePair (enc (α := VSt)) Nat.bits)).fanout
      ((fst (enc (α := VSt)) Nat.bits).comp v_yidx)).comp
    (listMapWith (ea := Nat.bits) (ec := encodePair (enc (α := VSt)) Nat.bits)
      (f := fun z : (VSt × ℕ) × ℕ => z.1.1.2.1[z.1.2 * z.1.1.1 + z.2]?.getD 0
        + z.1.1.2.2[z.1.2 * z.1.1.1 + z.2]?.getD 0) a_elem
      (a0 := 0) (b0 := (0 : ℚ)))).congr _ (fun _ => rfl)

noncomputable def addProgram : PolyProgram (enc (α := VSt)) (encodeList Ratio.encode) addRaw :=
  ((v_id.fanout v_yidx).comp
    (listFlatMapWith (ea := Nat.bits) (ec := enc (α := VSt))
      (f := fun y : VSt × ℕ => (List.range (y.1.2.2.take y.1.1).length).map
        (fun j => y.1.2.1[y.2 * y.1.1 + j]?.getD 0 + y.1.2.2[y.2 * y.1.1 + j]?.getD 0)) a_row
      (a0 := 0) (b0 := (0 : ℚ)))).congr _ (fun _ => rfl)

theorem addProgram_spec (n : ℕ) (xs ys : List ℚ) (_hx : xs.length = n * n)
    (hy : ys.length = n * n) : addRaw (n, xs, ys) = add n xs ys := by
  simp only [addRaw, add, mk, m_idx_spec' n ys hy, entry, List.getD_eq_getElem?_getD]

/-- Raw transpose. -/
def transposeRaw (p : VSt) : List ℚ :=
  (List.range (p.2.2.take p.1).length).flatMap
    (fun i => (List.range (p.2.2.take p.1).length).map
      (fun j => p.2.1[j * p.1 + i]?.getD 0))

noncomputable def tr_elem : PolyProgram (encodePair (encodePair (enc (α := VSt)) Nat.bits) Nat.bits) Ratio.encode
    (fun z : (VSt × ℕ) × ℕ => z.1.1.2.1[z.2 * z.1.1.1 + z.1.2]?.getD 0) :=
  ((s_xs.fanout s_ji).comp (listGetD (Ratio.encode) (0 : ℚ))).congr _ (fun _ => rfl)

noncomputable def tr_row : PolyProgram (encodePair (enc (α := VSt)) Nat.bits) (encodeList Ratio.encode)
    (fun y : VSt × ℕ => (List.range (y.1.2.2.take y.1.1).length).map
      (fun j => y.1.2.1[j * y.1.1 + y.2]?.getD 0)) :=
  (((identity (encodePair (enc (α := VSt)) Nat.bits)).fanout
      ((fst (enc (α := VSt)) Nat.bits).comp v_yidx)).comp
    (listMapWith (ea := Nat.bits) (ec := encodePair (enc (α := VSt)) Nat.bits)
      (f := fun z : (VSt × ℕ) × ℕ => z.1.1.2.1[z.2 * z.1.1.1 + z.1.2]?.getD 0) tr_elem
      (a0 := 0) (b0 := (0 : ℚ)))).congr _ (fun _ => rfl)

noncomputable def transposeProgram : PolyProgram (enc (α := VSt)) (encodeList Ratio.encode) transposeRaw :=
  ((v_id.fanout v_yidx).comp
    (listFlatMapWith (ea := Nat.bits) (ec := enc (α := VSt))
      (f := fun y : VSt × ℕ => (List.range (y.1.2.2.take y.1.1).length).map
        (fun j => y.1.2.1[j * y.1.1 + y.2]?.getD 0)) tr_row
      (a0 := 0) (b0 := (0 : ℚ)))).congr _ (fun _ => rfl)

theorem transposeProgram_spec (n : ℕ) (xs ys : List ℚ) (_hx : xs.length = n * n)
    (hy : ys.length = n * n) : transposeRaw (n, xs, ys) = transpose n xs := by
  simp only [transposeRaw, transpose, mk, m_idx_spec' n ys hy, entry,
    List.getD_eq_getElem?_getD]

/-- The leaf quantity `V - tr(A X)` on the packed state, raw form. -/
def gapRaw (p : VSt) : ℚ :=
  ((List.range (p.2.2.take p.1).length).flatMap
      (fun i => (List.range (p.2.2.take p.1).length).map (fun j => p.2.1[i * p.1 + j]?.getD 0))).sum
    - ((List.range (p.2.2.take p.1).length).flatMap
      (fun i => (List.range (p.2.2.take p.1).length).map
        (fun j => p.2.1[i * p.1 + j]?.getD 0 * p.2.2[j * p.1 + i]?.getD 0))).sum

/-- The leaf quantity `V - tr(A X)`, as one machine. -/
noncomputable def gapProgram : PolyProgram (enc (α := VSt)) Ratio.encode gapRaw :=
  ((sumProgram.fanout trProdProgram).comp ratSub).congr _ (fun _ => rfl)

theorem gapProgram_spec (n : ℕ) (xs ys : List ℚ) (_hx : xs.length = n * n)
    (hy : ys.length = n * n) :
    gapRaw (n, xs, ys) = sum n xs - trProd n xs ys := by
  simp only [gapRaw, sum, trProd, m_idx_spec' n ys hy, entry, List.getD_eq_getElem?_getD]

/-! ## 9. Runtime size bounds (whatever the framework gives) -/

theorem traceProgram_length_bound (p : MSt) :
    (Ratio.encode ((fun p : MSt => ((List.range (p.2.take p.1).length).map
      (fun i => p.2[i * p.1 + i]?.getD 0)).sum) p)).length ≤
      traceProgram.sizeBound.eval (enc (α := MSt) p).length :=
  traceProgram.length_bound p

theorem dotProgram_length_bound (p : List ℚ × List ℚ) :
    (Ratio.encode ((fun p : List ℚ × List ℚ =>
      ((p.1.zip p.2).map (fun q : ℚ × ℚ => q.1 * q.2)).sum) p)).length ≤
      dotProgram.sizeBound.eval (enc (α := List ℚ × List ℚ) p).length :=
  dotProgram.length_bound p

theorem mulVecProgram_length_bound (p : VSt) :
    (encodeList Ratio.encode (mulVecRaw p)).length ≤
      mulVecProgram.sizeBound.eval (enc (α := VSt) p).length :=
  mulVecProgram.length_bound p

end Runtime

/-! ## 10. Axiom audit -/

#print axioms MatQ.entry_mk
#print axioms MatQ.mk_getD
#print axioms MatQ.correct_mul
#print axioms MatQ.correct_mulVec
#print axioms MatQ.qform_eq
#print axioms MatQ.trProd_eq
#print axioms MatQ.sum_eq
#print axioms MatQ.trace_eq
#print axioms MatQ.Runtime.entryProgram
#print axioms MatQ.Runtime.dotProgram
#print axioms MatQ.Runtime.traceProgram
#print axioms MatQ.Runtime.sumProgram
#print axioms MatQ.Runtime.trProdProgram
#print axioms MatQ.Runtime.mulVecProgram
#print axioms MatQ.Runtime.traceProgram_length_bound
#print axioms MatQ.Runtime.addProgram
#print axioms MatQ.Runtime.transposeProgram
#print axioms MatQ.Runtime.gapProgram
#print axioms MatQ.Runtime.addProgram_spec
#print axioms MatQ.Runtime.gapProgram_spec

end MatQ


