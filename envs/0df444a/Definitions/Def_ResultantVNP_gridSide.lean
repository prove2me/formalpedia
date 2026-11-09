-- Prove2me | Definitions.Def_ResultantVNP_gridSide
-- name    : ResultantVNP_gridSide
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T22:24:56.844375+00:00
-- url     : https://prove2.me/theorems/b942ffca-63b1-4be8-90d2-adf3c2478c06
-- title:
--   Grid side $m(n)$: the smallest $3^r+1>n$ with $r\ge1$
-- statement:
--   For an $n\times n$ matrix the grid has side $m(n)$, the smallest number of the form $3^r+1$ with $r\ge1$ that exceeds $n$. For example $m(1)=m(3)=4$ and $m(4)=10$.
--
--   The form $3^r+1$ is what Lemma 3.6 needs ($3^r\equiv-1\pmod m$).
-- source:
--   Bhargav–Curticapean–Jindal–Shukla, Multivariate Resultants: Complexity and Applications to Real Feasibility, STOC 2027 submission (manuscript sha256 8827709b…7f8271), Lemma 3.3, p.15; Appendix A.1, p.37

import Mathlib

namespace ResultantVNP

theorem gridSide_exists (n : ℕ) : ∃ r : ℕ, 1 ≤ r ∧ n < 3 ^ r + 1 :=
  ⟨n + 1, by omega, by
    have h := Nat.lt_pow_self (by norm_num : 1 < 3) (n := n + 1)
    omega⟩

/-- The **side of the grid** used for `n × n` matrices: the smallest `m = 3^r + 1 > n` with `r ≥ 1`.

Bhargav–Curticapean–Jindal–Shukla, *Multivariate Resultants: Complexity and Applications to Real Feasibility*, STOC 2027 submission manuscript (sha256 8827709b…7f8271), Lemma 3.3, p.15 ("side m = m(n) = 3^r + 1 = O(n), with r ≥ 1") and Appendix A.1, p.37 ("choose
the smallest m = m(n) = 3^r + 1 > n with r ≥ 1").

**Formalization Note** `r` is the least `r ≥ 1` with `n < 3^r + 1` (`Nat.find`); e.g. `gridSide 1 = 4`,
`gridSide 4 = 10`. -/
def gridSide (n : ℕ) : ℕ :=
  3 ^ Nat.find (gridSide_exists n) + 1

instance (n : ℕ) : NeZero (gridSide n) := ⟨by simp [gridSide]⟩

end ResultantVNP


