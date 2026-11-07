-- Prove2me | Definitions.Def_BoolCSPDel_dictOracle
-- name    : BoolCSPDel_dictOracle
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T15:57:20.507381+00:00
-- url     : https://prove2.me/theorems/9efd3bfd-3f17-41c9-bda2-0387df042f54
-- title:
--   Sparse row dictionaries, row oracle and weighted output lists
-- statement:
--   A **sparse row dictionary** is an integer matrix $B\in\mathbb Z^{m\times D}$ with at most $s_0$ nonzero entries and squared norm at most $b_0$ in each row. The row oracle answers an index $i$ with a word listing the nonzero entries of row $i$. A stream over $[m]$ is coded as sign bits and indices in $\lceil\log_2 m\rceil$ bits. An output list has entries $(i,a,e)$, row $i$ with the dyadic weight $a/2^e$.
--
--   **Formalization Note** The oracle models "the time needed to obtain a row" at unit cost, while its answer occupies tape. Dyadic weights suffice, as the algorithm's weights are squares of multiples of a power of two, doubled.
-- source:
--   Bandekar, Sharma, Velusamy, A New Characterization of Streaming Decidability of Boolean CSPs Under Deletions, STOC 2027 submission (manuscript sha256 15f83519…), Corollary 5.4, pp.31–32; §5.1, p.32; §A.1, p.47

import Mathlib
import Definitions.Def_BoolCSPDel_inputWord
import Definitions.Def_BoolCSPDel_Mono

namespace BoolCSPDel

/-- **Sparse row dictionaries as oracles.** Bandekar, Sharma, Velusamy, STOC 2027 submission
(manuscript sha256 15f83519…), Corollary 5.4, p.31, §5.1, p.32: each row has at most `s₀` nonzero
entries and squared norm at most `b₀`. -/
def SparseRows {m D : ℕ} (s₀ b₀ : ℕ) (B : Matrix (Fin m) (Fin D) ℤ) : Prop :=
  ∀ i, (Finset.univ.filter fun j => B i j ≠ 0).card ≤ s₀ ∧ ∑ j, (B i j) ^ 2 ≤ (b₀ : ℤ)

/-- One signed coefficient: sign bit (`true` for `≥ 0`), then its absolute value. -/
def coeffWord (v : ℤ) : List Bool := decide (0 ≤ v) :: encNat v.natAbs

/-- A row as a word: for each nonzero entry in column order, `true`, the column, the coefficient;
then `false`. -/
def rowWord {D : ℕ} (b : Fin D → ℤ) : List Bool :=
  ((List.finRange D).filter fun j => b j ≠ 0).flatMap (fun j : Fin D => true :: encNat j.val ++ coeffWord (b j))
    ++ [false]

/-- The row oracle: on `i < m`, the word of row `i`. -/
def dictOracle {m D : ℕ} (B : Matrix (Fin m) (Fin D) ℤ) : ℕ → List Bool :=
  fun i => if h : i < m then rowWord (B ⟨i, h⟩) else []

/-- The updates of a stream over `[m]`: sign bit, then the index in `⌈log₂ m⌉` bits. -/
def updateBits {m : ℕ} (s : List (Fin m × Bool)) : List Bool :=
  s.flatMap fun u => u.2 :: fixedBits (Nat.clog 2 m) u.1

/-- An output list of weighted rows: `(i, a, e)` is row `i` with the dyadic weight `a / 2^e`. -/
abbrev WeightedList (m : ℕ) : Type := List (Fin m × ℕ × ℕ)

/-- The output word: for each entry, `true`, the index, `a`, `e`; then `false`. -/
def weightedWord {m : ℕ} (l : WeightedList m) : List Bool :=
  (l.flatMap fun e => true :: fixedBits (Nat.clog 2 m) e.1 ++ encNat e.2.1 ++ encNat e.2.2) ++ [false]

/-- `W = Σ w_i b_i b_iᵀ` for an output list. -/
noncomputable def listSum {m D : ℕ} (B : Matrix (Fin m) (Fin D) ℤ) (l : WeightedList m) :
    Matrix (Fin D) (Fin D) ℝ :=
  (l.map fun e => ((e.2.1 : ℝ) / 2 ^ e.2.2) • Matrix.vecMulVec (rowR B e.1) (rowR B e.1)).sum

/-- A list of distinct active rows with positive weights: the shape every output must have on success. -/
def ActiveList {m : ℕ} (f : Fin m → ℤ) (l : WeightedList m) : Prop :=
  (l.map Prod.fst).Nodup ∧ ∀ e ∈ l, 0 < f e.1 ∧ 0 < e.2.1

/-- A monomial coordinate as a word: the size, then the variables in increasing order. -/
def monoWord {n d : ℕ} (T : Mono n d) : List Bool :=
  encNat T.1.card ++ (T.1.sort (· ≤ ·)).flatMap fun v => encNat v

/-- A row of the polynomial representation as a word: for each listed coordinate, `true`, the
coordinate, the coefficient; then `false`. -/
def monoRowWord {n d : ℕ} (L : List (Mono n d × ℤ)) : List Bool :=
  (L.flatMap fun e => true :: monoWord e.1 ++ coeffWord e.2) ++ [false]

end BoolCSPDel


