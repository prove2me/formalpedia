-- Prove2me | Definitions.Def_MovementSorting_Exponent_Beta
-- name    : MovementSorting_Exponent_Beta
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-09T21:00:45.105957+00:00
-- url     : https://prove2.me/theorems/111bd542-db05-490e-9fa8-6c84940b45ac
-- title:
--   The movement exponent β^{(d)}_r and the scale schedule
-- statement:
--   $\beta^{(d)}_r = 1 + D^{r-1}/(D^r - (D-1)^r)$ with $D = 2d$ for finite $r \ge 1$ (a real number), and $\beta^{(d)}_\infty = 1 + 1/(2d)$ (`betaInf`). With $q = (D-1)/D$, the exponents of Lemma 2.5 are $a_j = (q^{j+1}-q^r)/(1-q^r)$ (`schedExp d r j`). `IsScheduleSolution d r β a` states Equations (2.1)–(2.3): $\beta = 2 - a_0$, $\beta = 1 + (1-a_{j-1})/D + a_{j-1} - a_j$ for $1 \le j \le r-2$, and $\beta = 1 + a_{r-2} + (1-a_{r-2})/D$. The real schedule is $b_j = n^{a_j}$ (`realScale`), and the dyadic schedule of Section 4 takes for $b_j$ the largest power of two not exceeding $n^{a_j}$ (`dyadicScale`).
-- source:
--   Wang (2026), The Movement Complexity of Sorting, arXiv:2611.01157 (held copy SHA-256 90e3d9df…), Theorem 1.1, p. 2; Equations (2.1)–(2.3), Lemma 2.5 and the schedule, pp. 8–9; Section 4 schedule, p. 12

import Mathlib

set_option autoImplicit false

namespace MovementSorting.Exponent

/-! # The movement exponent and the scale schedule (Wang 2026, Theorem 1.1 p. 2; §2.2 pp. 8–9) -/

/-- `β^{(d)}_r = 1 + D^{r-1} / (D^r - (D-1)^r)` with `D = 2d`, for finite `r ≥ 1` (a real number;
the value at `r = 0` is not used). -/
noncomputable def beta (d r : ℕ) : ℝ :=
  1 + (2 * d : ℝ) ^ (r - 1) / ((2 * d : ℝ) ^ r - (2 * d - 1 : ℝ) ^ r)

/-- `β^{(d)}_∞ = 1 + 1/(2d)`. -/
noncomputable def betaInf (d : ℕ) : ℝ := 1 + 1 / (2 * d : ℝ)

/-- `q = (D - 1)/D` with `D = 2d`. -/
noncomputable def qRatio (d : ℕ) : ℝ := (2 * d - 1 : ℝ) / (2 * d : ℝ)

/-- The exponents of Lemma 2.5: `a_j = (q^{j+1} - q^r)/(1 - q^r)` (used for `0 ≤ j ≤ r - 2`). -/
noncomputable def schedExp (d r j : ℕ) : ℝ :=
  (qRatio d ^ (j + 1) - qRatio d ^ r) / (1 - qRatio d ^ r)

/-- `(β, a_0, …, a_{r-2})` solves Equations (2.1)–(2.3) (with `D = 2d`):
splitter `β = 2 - a_0`; refinement `β = 1 + (1 - a_{j-1})/D + a_{j-1} - a_j` for
`1 ≤ j ≤ r - 2`; cleanup `β = 1 + a_{r-2} + (1 - a_{r-2})/D`. Values `a j` for `j > r - 2` are not
constrained. -/
def IsScheduleSolution (d r : ℕ) (β : ℝ) (a : ℕ → ℝ) : Prop :=
  β = 2 - a 0 ∧
  (∀ j : ℕ, 1 ≤ j → j ≤ r - 2 → β = 1 + (1 - a (j - 1)) / (2 * d : ℝ) + a (j - 1) - a j) ∧
  β = 1 + a (r - 2) + (1 - a (r - 2)) / (2 * d : ℝ)

/-- The real schedule `b_j = n^{a_j}`, `n = m^d` (used by the algorithms). -/
noncomputable def realScale (d r m j : ℕ) : ℝ := ((m ^ d : ℕ) : ℝ) ^ schedExp d r j

/-- The dyadic schedule of Section 4: `b_j` is the largest power of two not exceeding `n^{a_j}`. -/
noncomputable def dyadicScale (d r m j : ℕ) : ℕ := 2 ^ Nat.log 2 ⌊realScale d r m j⌋₊

end MovementSorting.Exponent


