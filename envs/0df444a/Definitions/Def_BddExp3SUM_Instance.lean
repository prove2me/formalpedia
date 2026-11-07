-- Prove2me | Definitions.Def_BddExp3SUM_Instance
-- name    : BddExp3SUM_Instance
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T10:57:12.413821+00:00
-- url     : https://prove2.me/theorems/b0c24f13-25db-4251-be41-6e29805128fc
-- title:
--   Three-list 3SUM over $\prod_j \mathbb Z_{m_j}$ with $m_j\mid M$, witnesses, and $\delta_M=\eta\gamma/2$
-- statement:
--   An instance over a fixed integer $M$ consists of moduli $m_1,\dots,m_r$ with each $m_j\mid M$, and three lists $L_1,L_2,L_3$ of residue vectors: each element $a$ has $0\le a_j<m_j$. The group is $G_0=\prod_{j=1}^r\mathbb Z_{m_j}$, of order $\prod_j m_j$.
--
--   A **witness** is a triple of indices, in range of the three lists, whose entries satisfy
--
--   $$a^{(1)}_j+a^{(2)}_j+a^{(3)}_j\equiv 0\pmod{m_j}\qquad\text{for every } j.$$
--
--   The module also fixes the constants of Theorem 1:
--
--   $$C=\lceil\log_2 M\rceil,\quad \eta=\min\{1/18,\,1/(8C)\},\quad \gamma=63/1000,\quad \delta_M=\eta\gamma/2.$$
--
--   These objects are all the goal theorem speaks about.
--
--   **Formalization Note** The memory of a run holds $n$ in cell $0$, then $r$, the moduli, the three lengths and the three lists row by row. Output is three indices in the cells right after the input, read as signed words. Moduli $m_j=1$, empty lists and repetitions are allowed.
-- source:
--   Zeng, Wang, Cao, Dai, Wang, Truly Subquadratic 3SUM over Every Bounded-Exponent Abelian Group, STOC 2027 submission (manuscript sha256 19546c9a…), §1 and Theorem 1, p.1

import Mathlib
import Definitions.Def_BddExp3SUM_CoinRAM

namespace BddExp3SUM

/-!
# Instances of three-list 3SUM over a product of `Z_{m_j}`, witnesses and the saving `δ_M`

Zeng, Wang, Cao, Dai, Wang, STOC 2027 submission (manuscript sha256 19546c9a…), §1 and Theorem 1,
p.1: "The input group is given as G0 = ∏_{j=1}^r Z_{m_j}, with each m_j | M, and list elements are
residue vectors."; "Three-list 3SUM asks whether x1 + x2 + x3 = 0 for some xi in three given lists."

**Formalization Note.**
* Moduli `m_j = 1` are allowed ("each m_j | M"), so `r` is not bounded by the group's order.
* A list element is a vector of natural numbers with `a j < m j`. Lists may be empty, may have
  different lengths and may contain repetitions (the paper deduplicates them in §2).
* The zero-sum test is coordinatewise: `(a₁ j + a₂ j + a₃ j) % m j = 0`.
* The word layout is `r, m_0, …, m_{r-1}, |L₁|, |L₂|, |L₃|`, then the three lists row by row. A run
  has `n` in cell `0` and this input from cell `1`, as in `EndStatement.Problem.SolvedBy`. The output
  is three indices in the three cells right after the input, read as signed words.
-/

/-- An instance over a product of `Z_{m_j}`, `m_j ∣ M`: the moduli and three lists of residue vectors. -/
structure Instance (M : ℕ) where
  /-- the number of factors -/
  r : ℕ
  /-- the moduli -/
  m : Fin r → ℕ
  m_dvd : ∀ j, m j ∣ M
  /-- the first list -/
  L₁ : List (Fin r → ℕ)
  /-- the second list -/
  L₂ : List (Fin r → ℕ)
  /-- the third list -/
  L₃ : List (Fin r → ℕ)
  residue₁ : ∀ a ∈ L₁, ∀ j, a j < m j
  residue₂ : ∀ a ∈ L₂, ∀ j, a j < m j
  residue₃ : ∀ a ∈ L₃, ∀ j, a j < m j

namespace Instance

variable {M : ℕ} (x : Instance M)

/-- The order `|G₀| = ∏_j m_j` of the group, as a real number. -/
def order : ℝ := ∏ j, (x.m j : ℝ)

/-- A list of vectors, row by row. -/
def rowWords (l : List (Fin x.r → ℕ)) : List ℤ :=
  l.flatMap fun a => List.ofFn fun j => (a j : ℤ)

/-- The input words: `r`, the moduli, the three lengths, the three lists row by row. -/
def input : List ℤ :=
  (x.r : ℤ) :: (List.ofFn fun j => (x.m j : ℤ)) ++
    [(x.L₁.length : ℤ), (x.L₂.length : ℤ), (x.L₃.length : ℤ)] ++
    x.rowWords x.L₁ ++ x.rowWords x.L₂ ++ x.rowWords x.L₃

/-- Three residue vectors sum to zero in `∏_j Z_{m_j}`. -/
def ZeroSum (a₁ a₂ a₃ : Fin x.r → ℕ) : Prop :=
  ∀ j, (a₁ j + a₂ j + a₃ j) % x.m j = 0

/-- `(i₁, i₂, i₃)` are (0-based) indices in range of the three lists, and the entries there sum to
zero. Indices are integers because they are read from signed words. -/
def IsWitness (i₁ i₂ i₃ : ℤ) : Prop :=
  0 ≤ i₁ ∧ 0 ≤ i₂ ∧ 0 ≤ i₃ ∧ ∃ a₁ a₂ a₃ : Fin x.r → ℕ,
    x.L₁[i₁.toNat]? = some a₁ ∧ x.L₂[i₂.toNat]? = some a₂ ∧ x.L₃[i₃.toNat]? = some a₃ ∧
      x.ZeroSum a₁ a₂ a₃

/-- The input is positive: some zero-sum triple exists. -/
def HasWitness : Prop := ∃ i₁ i₂ i₃ : ℤ, x.IsWitness i₁ i₂ i₃

/-- The memory at the start of a run with size parameter `n` in cell `0`, this instance from cell
`1`, and the coin tape in the negative cells. -/
def memory (W n : ℕ) (tape : ℕ → Bool) : ℤ → BitVec W :=
  coinMemory W ((n : ℤ) :: x.input) tape

/-- The output word number `a` in a final memory: cell `1 + |input| + a`, read as signed. -/
def out {W : ℕ} (mem : ℤ → BitVec W) (a : ℕ) : ℤ :=
  (mem ((1 + x.input.length + a : ℕ) : ℤ)).toInt

/-- `P` accepts on this coin tape. -/
def Accepts (P : List EndStatement.Instr) (W n : ℕ) (tape : ℕ → Bool) : Prop :=
  ∃ (t : ℕ) (mem : ℤ → BitVec W), EndStatement.exec P t 0 (x.memory W n tape) = some (true, mem)

end Instance

/-- `C = ⌈log₂ M⌉`. -/
def C (M : ℕ) : ℕ := Nat.clog 2 M

/-- `η = min{1/18, 1/(8C)}`. -/
noncomputable def η (M : ℕ) : ℝ := min (1 / 18) (1 / (8 * (C M : ℝ)))

/-- `γ = 63/1000`. -/
noncomputable def γ : ℝ := 63 / 1000

/-- The saving `δ_M = ηγ/2`. -/
noncomputable def δ (M : ℕ) : ℝ := η M * γ / 2

end BddExp3SUM


