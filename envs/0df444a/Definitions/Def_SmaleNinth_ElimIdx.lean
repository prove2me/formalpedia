-- Prove2me | Definitions.Def_SmaleNinth_ElimIdx
-- name    : SmaleNinth_ElimIdx
-- status  : Definition
-- author  : @Zexuan Liu
-- created : 2026-09-08T02:46:56.13097+00:00
-- url     : https://prove2.me/theorems/2dbf2fc9-0d4b-4312-9098-6f98f6cbf72c
-- title:
--   Index type and right-hand side of the eliminated system
-- statement:
--   Fourier–Motzkin elimination replaces the rows of a system by the rows together with the ordered pairs of rows, so after $n$ steps the rows are indexed by the type obtained from the original index type $\iota$ by applying $\iota \mapsto \iota \oplus \iota \times \iota$ exactly $n$ times. This file names that type, `ElimIdx n ι`, records that it is finite, and defines `elimRhs n A c`, the right-hand side of the system reached after $n$ eliminations.
--
--   They make the size of the procedure visible. If the original system has $m$ rows, then one step produces at most $m + m^2$ rows, so after $n$ steps the count is at most $(m+1)^{2^n}$: the procedure `SmaleNinth.ElimFeas` is a conjunction of at most that many sign conditions, each an explicit polynomial expression in the entries of the system. This is polynomial in the number of constraints for every fixed number of variables and doubly exponential in the number of variables.
-- source:
--   J. B. J. Fourier (1826); T. Motzkin, Beitraege zur Theorie der linearen Ungleichungen, Dissertation, Basel 1936. See A. Schrijver, Theory of Linear and Integer Programming, Wiley 1986, Section 12.2, for the growth of the number of inequalities under elimination.

import Definitions.Def_SmaleNinth_FourierMotzkin
import Mathlib.Data.Fintype.Card

/-!
The index type of the system produced by `n` steps of Fourier-Motzkin
elimination, and the right-hand side of that system.  Together they exhibit
`SmaleNinth.ElimFeas` as a conjunction of explicitly many sign conditions.

Source: J. B. J. Fourier (1826) and T. Motzkin (1936); see A. Schrijver,
*Theory of Linear and Integer Programming*, Wiley 1986, Section 12.2.
-/

namespace SmaleNinth

/-- The index type of the system after `n` eliminations: each step replaces the
rows by the rows together with the ordered pairs of rows. -/
def ElimIdx : ℕ → Type → Type
  | 0, ι => ι
  | (n + 1), ι => ElimIdx n (ι ⊕ ι × ι)

/-- Finiteness of the iterated index type. -/
def elimIdxFintypeAux : (n : ℕ) → (ι : Type) → Fintype ι → Fintype (ElimIdx n ι)
  | 0, _, h => h
  | (n + 1), ι, h =>
      elimIdxFintypeAux n (ι ⊕ ι × ι) (@instFintypeSum _ _ h (@instFintypeProd _ _ h h))

instance elimIdxFintype {n : ℕ} {ι : Type} [h : Fintype ι] : Fintype (ElimIdx n ι) :=
  elimIdxFintypeAux n ι h

/-- The right-hand side of the system after `n` eliminations. -/
noncomputable def elimRhs :
    (n : ℕ) → {ι : Type} → (ι → Fin n → ℝ) → (ι → ℝ) → (ElimIdx n ι → ℝ)
  | 0, _, _, c => c
  | (n + 1), _, A, c => elimRhs n (elimMatrix A) (elimStep A c)

end SmaleNinth


