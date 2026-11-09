-- Prove2me | Definitions.Def_ResultantVNP_gridTensor
-- name    : ResultantVNP_gridTensor
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T22:29:07.014533+00:00
-- url     : https://prove2.me/theorems/386f275b-c38d-4372-b4e3-01b0a76a69b8
-- title:
--   The grid encoding $A_m(Z)$ of the permanent (Appendix A.1)
-- statement:
--   Let $Z=(z_{ij})$ be the generic $n\times n$ matrix, $m=m(n)$ and $Z'=\mathrm{diag}(Z,I_{m-n})$. At each grid position use the five **states**
--
--   $$
--   S=\{(0,p,q):p,q\in\{0,1\}\}\cup\{(1,0,0)\},
--   $$
--
--   a separate copy for each position; the tensor indices are the pairs (position, state), five per position. For a state $a=(x,p,q)$, $x$ selects the matrix entry, $p$ records the number of selections earlier in the column, $q$ the number earlier in the row. For the triangle anchored at $(i,j)$ with states $a,b,c$ at $(i,j),(i^+,j),(i,j^+)$, the entry is $z'^{\,x(a)}_{ij}$ (with $z'^{\,0}=1$) if
--
--   - $i=1\Rightarrow p(a)=0$, $j=1\Rightarrow q(a)=0$,
--   - $i<m\Rightarrow p(b)=p(a)+x(a)$, $j<m\Rightarrow q(c)=q(a)+x(a)$,
--   - $i=m\Rightarrow p(a)+x(a)=1$, $j=m\Rightarrow q(a)+x(a)=1$,
--
--   and $0$ otherwise; all other entries are $0$. This defines a symmetric tensor $A_m(Z)$ with entries in $\{0,1\}\cup\{z_{ij}\}$; its index classes are the five indices at each position.
--
--   **Formalization Note** Positions $1,\dots,m$ of the paper are $0,\dots,m-1$ in $\mathbb Z_m$. Entries are polynomials in the variables $z_{ij}$; a concrete matrix is substituted by evaluation. The entry of an unordered triple is computed as a sum over all (anchor, states) whose triangle triple it is; for $m\ge3$ at most one summand is nonzero, as the paper notes.
-- source:
--   Bhargav–Curticapean–Jindal–Shukla, Multivariate Resultants: Complexity and Applications to Real Feasibility, STOC 2027 submission (manuscript sha256 8827709b…7f8271), Lemma 3.3, p.15; Appendix A.1, p.37

import Mathlib
import Definitions.Def_ResultantVNP_gridSum
import Definitions.Def_ResultantVNP_gridSide

namespace ResultantVNP

/-- The five **states** `S = {(0, p, q) : p, q ∈ {0,1}} ∪ {(1, 0, 0)}` of a grid position; a state is
`a = (x, p, q)`. -/
abbrev GridState : Type := {a : Fin 2 × Fin 2 × Fin 2 // a.1 = 0 ∨ a = (1, 0, 0)}

/-- The tensor indices of the grid encoding on side `m`: a position of `ℤ_m²` together with one of the
five states (a separate copy of `S` for each position). -/
abbrev GridIdx (m : ℕ) : Type := (ZMod m × ZMod m) × GridState

/-- The entry `z'_{ij}` of `Z' = diag(Z, I_{m−n})` for the generic `n × n` matrix `Z = (z_{ij})`, at grid
position `(i, j)` (0-based). -/
noncomputable def paddedEntry (n m : ℕ) (p : ZMod m × ZMod m) : MvPolynomial (Fin n × Fin n) ℤ :=
  if h : p.1.val < n ∧ p.2.val < n then MvPolynomial.X (⟨p.1.val, h.1⟩, ⟨p.2.val, h.2⟩)
  else if p.1 = p.2 then 1 else 0

/-- The six tests of Appendix A.1 for the factor anchored at `p = (i, j)` with states `a, b, c` at
`(i, j), (i⁺, j), (i, j⁺)` (positions `1, …, m` of the paper are `0, …, m − 1` here):
`i = 1 ⇒ p(a) = 0`, `j = 1 ⇒ q(a) = 0`, `i < m ⇒ p(b) = p(a) + x(a)`, `j < m ⇒ q(c) = q(a) + x(a)`,
`i = m ⇒ p(a) + x(a) = 1`, `j = m ⇒ q(a) + x(a) = 1`. -/
def gridTest (m : ℕ) (p : ZMod m × ZMod m) (a b c : GridState) : Prop :=
  (p.1.val = 0 → a.1.2.1.val = 0) ∧ (p.2.val = 0 → a.1.2.2.val = 0) ∧
    (p.1.val < m - 1 → b.1.2.1.val = a.1.2.1.val + a.1.1.val) ∧
    (p.2.val < m - 1 → c.1.2.2.val = a.1.2.2.val + a.1.1.val) ∧
    (p.1.val = m - 1 → a.1.2.1.val + a.1.1.val = 1) ∧
    (p.2.val = m - 1 → a.1.2.2.val + a.1.1.val = 1)

/-- The **grid encoding** of the generic `n × n` matrix on an `m × m` toroidal grid (Appendix A.1): the
symmetric tensor whose entry at the unordered triple `{(p, a), (p + (1,0), b), (p + (0,1), c)}` is
`z'_p^{x(a)}` (with `z'^0 = 1`) if the six tests hold and `0` otherwise, and whose other entries are
`0`; `Z' = diag(Z, I_{m−n})`.

Bhargav–Curticapean–Jindal–Shukla, *Multivariate Resultants: Complexity and Applications to Real Feasibility*, STOC 2027 submission manuscript (sha256 8827709b…7f8271), Appendix A.1, p.37.

**Formalization Note** For `m ≥ 3` the three positions of a triangle determine its anchor, so at most one
summand below is nonzero and the sum is the tensor entry ("the three grid positions uniquely determine
the factor and its anchor, so this symmetric tensor is well defined"). -/
noncomputable def gridEncoding (n m : ℕ) [NeZero m] (T : Sym (GridIdx m) 3) :
    MvPolynomial (Fin n × Fin n) ℤ := by
  classical
  exact ∑ p : ZMod m × ZMod m, ∑ a : GridState, ∑ b : GridState, ∑ c : GridState,
    if T = (p, a) ::ₛ (gridRight p, b) ::ₛ (gridDown p, c) ::ₛ Sym.nil ∧ gridTest m p a b c then
      (if a.1.1 = 1 then paddedEntry n m p else 1)
    else 0

/-- The tensor `A_m(Z)` of Lemma 3.3 for the generic `n × n` matrix `Z = (z_{ij})`: the grid encoding of
`Z' = diag(Z, I_{m−n})` on the grid of side `m = gridSide n`, the smallest `3^r + 1 > n` with `r ≥ 1`.
Its index classes are the five indices `(p, a)` at each position `p` (class map `Prod.fst`).

Bhargav–Curticapean–Jindal–Shukla, *Multivariate Resultants: Complexity and Applications to Real Feasibility*, STOC 2027 submission manuscript (sha256 8827709b…7f8271), Lemma 3.3, p.15 and its proof, Appendix A.1, p.37.

**Formalization Note** Entries are polynomials in the matrix entries `z_{ij}` (variables `Fin n × Fin n`,
0-based); a concrete matrix is substituted by evaluation. -/
noncomputable def gridTensor (n : ℕ) : Sym (GridIdx (gridSide n)) 3 → MvPolynomial (Fin n × Fin n) ℤ :=
  gridEncoding n (gridSide n)

end ResultantVNP


