-- Prove2me | Definitions.Def_ResultantVNP_gridTableCode
-- name    : ResultantVNP_gridTableCode
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T22:31:52.599204+00:00
-- url     : https://prove2.me/theorems/e12719bb-fb28-4aa6-84cb-a203ef64a464
-- title:
--   Entry table of $A_m(Z)$ as a bit string
-- statement:
--   The output of the construction of Lemma 3.3: the table of all entries of $A_m(Z)$ for the generic $n\times n$ matrix, as a bit string. The $5m^2$ indices are numbered (position $(\lfloor k/5\rfloor\ \mathrm{div}\ m,\ \lfloor k/5\rfloor \bmod m)$, state $k\bmod 5$), and for all index numbers $a,b,c<5m^2$ in lexicographic order the entry at the unordered triple $\{a,b,c\}$ is written as `00` (for $0$), `01` (for $1$) or $1\,1^i\,0\,1^j\,0$ (for $z_{ij}$).
--
--   Lemma 3.3 asserts that $n\mapsto$ this table is computable in polynomial time.
-- source:
--   Bhargav–Curticapean–Jindal–Shukla, Multivariate Resultants: Complexity and Applications to Real Feasibility, STOC 2027 submission (manuscript sha256 8827709b…7f8271), Lemma 3.3, p.15; Appendix A.1, p.37

import Mathlib
import Definitions.Def_ResultantVNP_gridTensor

namespace ResultantVNP

/-- The state numbered `k` (`0, 1, 2, 3` are `(0,0,0), (0,0,1), (0,1,0), (0,1,1)`; every other `k` is
`(1,0,0)`). -/
def gridStateOfNat : ℕ → GridState
  | 0 => ⟨(0, 0, 0), Or.inl rfl⟩
  | 1 => ⟨(0, 0, 1), Or.inl rfl⟩
  | 2 => ⟨(0, 1, 0), Or.inl rfl⟩
  | 3 => ⟨(0, 1, 1), Or.inl rfl⟩
  | _ => ⟨(1, 0, 0), Or.inr rfl⟩

/-- The grid index numbered `k < 5m²`: position `(⌊k/5⌋ / m, ⌊k/5⌋ mod m)` and state `k mod 5`. -/
def gridIdxOfNat (m k : ℕ) : GridIdx m :=
  ((((k / 5 / m : ℕ) : ZMod m), ((k / 5 % m : ℕ) : ZMod m)), gridStateOfNat (k % 5))

/-- The binary code of an entry `0`, `1` or `z_{ij}`: `00`, `01`, and `1 1^i 0 1^j 0`; any other polynomial
gets the empty code. -/
noncomputable def entryCode {n : ℕ} (e : MvPolynomial (Fin n × Fin n) ℤ) : List Bool := by
  classical
  exact if e = 0 then [false, false] else if e = 1 then [false, true]
    else if h : ∃ ij : Fin n × Fin n, e = MvPolynomial.X ij then
      true :: (List.replicate (h.choose.1 : ℕ) true ++ false ::
        List.replicate (h.choose.2 : ℕ) true ++ [false])
    else []

/-- The **entry table** of `A_m(Z) = gridTensor n` as a bit string: for all index numbers
`a, b, c < 5m²` in lexicographic order, the code (`entryCode`) of the entry at the unordered triple
`{a, b, c}`. This is the output of the construction of Lemma 3.3 ("one can construct in polynomial time a
symmetric tensor A_m(Z)").

Bhargav–Curticapean–Jindal–Shukla, *Multivariate Resultants: Complexity and Applications to Real Feasibility*, STOC 2027 submission manuscript (sha256 8827709b…7f8271), Lemma 3.3, p.15; Appendix A.1, p.37.

**Formalization Note** The construction takes the size `n` of the symbolic matrix and outputs the
symbolic table (entries `0`, `1` or a variable `z_{ij}`); a concrete matrix is then substituted entry by
entry. -/
noncomputable def gridTableCode (n : ℕ) : List Bool :=
  (List.range (5 * gridSide n ^ 2)).flatMap fun a =>
    (List.range (5 * gridSide n ^ 2)).flatMap fun b =>
      (List.range (5 * gridSide n ^ 2)).flatMap fun c =>
        entryCode (gridTensor n (gridIdxOfNat (gridSide n) a ::ₛ gridIdxOfNat (gridSide n) b ::ₛ
          gridIdxOfNat (gridSide n) c ::ₛ Sym.nil))

end ResultantVNP


