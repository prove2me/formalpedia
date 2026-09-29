-- Prove2me | Definitions.Def_SmaleNinth_FourierMotzkin
-- name    : SmaleNinth_FourierMotzkin
-- status  : Definition
-- author  : @Zexuan Liu
-- created : 2026-09-08T02:41:52.42606+00:00
-- url     : https://prove2.me/theorems/eb9ca5b5-c121-4ee2-ad1d-5708fe1e99a6
-- title:
--   The Fourier-Motzkin elimination procedure
-- statement:
--   Fourier–Motzkin elimination decides whether a finite system of linear inequalities over the reals has a solution. This file defines the procedure.
--
--   One elimination step removes the last variable. Writing $\beta_i$ for the last coefficient of row $i$, the new system is indexed by the rows together with the ordered pairs of rows: a row with $\beta_i = 0$ is kept unchanged; a pair $(i,j)$ with $\beta_i > 0 > \beta_j$ contributes the combination $(-\beta_j)\cdot(\text{row } i) + \beta_i \cdot (\text{row } j)$, in which the last variable cancels; and every other row or pair contributes the vacuous inequality $0 \ge 0$. Keeping the vacuous rows rather than discarding them is what makes the index type of the new system a fixed function, $\iota \oplus \iota \times \iota$, of the old one, so that the construction iterates without any bookkeeping of which rows survive.
--
--   `elimStep` performs that step on an arbitrary functional on the rows, so that applying it to each column of the matrix (`elimMatrix`) and to the right-hand side gives the eliminated system. `ElimFeas n A c` iterates the step $n$ times and asserts that the constant system which remains — one real number per index, with no variables left — has all its right-hand sides at most $0$.
--
--   After $n$ steps the number of indices is at most $(m+1)^{2^n}$ when the original system has $m$ rows, since one step takes a count $N$ to $N + N^2$. The procedure is therefore of polynomial size for each fixed number of variables and doubly exponential in the number of variables, which is the classical behaviour of the method.
-- source:
--   J. B. J. Fourier (1826); T. Motzkin, Beitraege zur Theorie der linearen Ungleichungen, Dissertation, Basel 1936. See A. Schrijver, Theory of Linear and Integer Programming, Wiley 1986, Section 12.2, for the elimination step and its iteration.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fin.Basic

/-!
The Fourier-Motzkin decision procedure for feasibility of a system of linear
inequalities over the reals: eliminate the variables one after another, then
read off the answer from the constant system that remains.

Source: J. B. J. Fourier (1826) and T. Motzkin (1936); see A. Schrijver,
*Theory of Linear and Integer Programming*, Wiley 1986, Section 12.2.
-/

namespace SmaleNinth

open Classical in
/-- One elimination step applied to a functional `f` on the rows.  A row whose
last coefficient vanishes is kept; a pair of rows whose last coefficients have
opposite signs contributes the combination in which the last variable cancels;
every other row or pair contributes the vacuous value `0`. -/
noncomputable def elimStep {ι : Type} {n : ℕ} (A : ι → Fin (n + 1) → ℝ) (f : ι → ℝ) :
    (ι ⊕ ι × ι) → ℝ
  | Sum.inl i => if A i (Fin.last n) = 0 then f i else 0
  | Sum.inr (i, j) =>
      if 0 < A i (Fin.last n) ∧ A j (Fin.last n) < 0 then
        A i (Fin.last n) * f j - A j (Fin.last n) * f i
      else 0

/-- The system obtained from `A` by eliminating the last variable. -/
noncomputable def elimMatrix {ι : Type} {n : ℕ} (A : ι → Fin (n + 1) → ℝ) :
    (ι ⊕ ι × ι) → Fin n → ℝ :=
  fun i' k => elimStep A (fun i => A i k.castSucc) i'

/-- **The Fourier-Motzkin procedure.**  `ElimFeas n A c` eliminates the `n`
variables of the system `A x ≥ c` one after another and asserts that every row
of the resulting constant system is satisfiable. -/
noncomputable def ElimFeas :
    (n : ℕ) → {ι : Type} → [Fintype ι] → (ι → Fin n → ℝ) → (ι → ℝ) → Prop
  | 0, _, _, _, c => ∀ i, c i ≤ 0
  | (n + 1), _, _, A, c => ElimFeas n (elimMatrix A) (elimStep A c)

end SmaleNinth


