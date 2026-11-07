-- Prove2me | Definitions.Def_IntQuotHNP_MIHNPLattice
-- name    : IntQuotHNP_MIHNPLattice
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T10:53:10.693002+00:00
-- url     : https://prove2.me/theorems/4885680b-9402-43f6-86e1-eef9adbd258d
-- title:
--   Eq. (6) — the monomials, $a_{ij}$, the basis matrix of the MIHNP lattice, $v_{\mathrm{tar}}$, and the constant $K$ of (2)
-- statement:
--   The monomial index set consists of the $x_ix_j$ with $i<j$ and the $x_1,\dots,x_N$, $N(N+1)/2$ monomials in all. For $i<j$, $a_{ij}\in(-p/2,p/2]\cap\mathbb Z$ represents $(t_i-t_j)^{-1}$ modulo $p$, and
--   $$
--   P_{ij}(x)=(v_i+x_i)(v_j+x_j)+a_{ij}(v_i+x_i-v_j-x_j).
--   $$
--   The basis matrix of the lattice $\Lambda$ has one row for each $P_{ij}$ and one for each $px_h$:
--   $$
--   \begin{pmatrix} X^2 I & XJ\\ 0 & pX I_N\end{pmatrix},\qquad J_{(i,j),i}=v_j+a_{ij},\quad J_{(i,j),j}=v_i-a_{ij},\quad J_{(i,j),h}=0\ (h\notin\{i,j\}).
--   $$
--   The **target vector** $v_{\mathrm{tar}}$ has entry $pX$ at the monomial $x_1$ and zero elsewhere. The constant of (2) for this lattice is $K=1+12\sqrt d\,4^m$ with $m=d=N(N+1)/2$.
--
--   **Formalization Note** Rows and columns are both indexed by the type `Mon N`. The paper's algorithm lists the rows as $P_{ij}$, then $px_2,\dots,px_N,px_1$, and its own display (6) already reorders them; a row order affects neither the lattice nor $v_{\mathrm{tar}}$.
-- source:
--   Kang, Lee, Provable Recovery from Integer Quotients: Improved Bounds for Nonlinear Hidden Number Problems, STOC 2027 submission (manuscript sha256 605f9dd3…), §4.1, pp.22–23 (PDF pp.23–24), eq. (6); eq. (2), p.20 (PDF p.21)

import Mathlib
import Definitions.Def_IntQuotHNP_MIHNPInput

namespace IntQuotHNP

/-- **The monomials recorded by `Φ` for MIHNP**: `x_i x_j` (`i < j`) and `x_1, …, x_N`.
Kang, Lee, *Provable Recovery from Integer Quotients*, STOC 2027 submission (manuscript sha256
605f9dd3…), §4.1, p.23 (PDF p.24): "In the monomial order (x_i x_j)_{i<j}, x₁, . . . , x_N".

`Mon N` has `N(N − 1)/2 + N = N(N + 1)/2` elements. It indexes both the rows (the polynomials
`P_ij`, `p x_h`) and the columns (the monomials) of the basis matrix (6).

**Formalization Note.** `Sum.inl ⟨(i, j), _⟩` is the quadratic monomial `x_i x_j` (and the row of
`P_ij`), `Sum.inr h` the linear monomial `x_h` (and the row of `p x_h`); indices are 0-based. -/
abbrev Mon (N : ℕ) : Type := {q : Fin N × Fin N // q.1 < q.2} ⊕ Fin N

/-- **The centred representative `a_ij` of `(t_i − t_j)⁻¹ mod p`** (§4.1).
Kang, Lee, STOC 2027 submission (manuscript sha256 605f9dd3…), §4.1, p.22 (PDF p.23): "For each
i < j, let a_ij ∈ (−p/2, p/2] ∩ ℤ represent (t_i − t_j)⁻¹ modulo p."

With `r = [(t_i − t_j)⁻¹]_p`, `a_ij = r` if `2r ≤ p` and `a_ij = r − p` otherwise.

**Formalization Note.** The inverse is taken in `ZMod p`; for distinct shifts it is a genuine
inverse. -/
def aij (p ti tj : ℕ) : ℤ :=
  let r := (((ti : ZMod p) - (tj : ZMod p))⁻¹).val
  if 2 * r ≤ p then (r : ℤ) else (r : ℤ) - p

/-- **The rows of the basis matrix (6) of the MIHNP lattice.**
Kang, Lee, STOC 2027 submission (manuscript sha256 605f9dd3…), §4.1, pp.22–23 (PDF pp.23–24):
"P_ij(x) = (v_i + x_i)(v_j + x_j) + a_ij(v_i + x_i − v_j − x_j) (i < j). Take the P_ij, followed by
px₂, . . . , px_N, px₁, as the entries of P. … J_(i,j),i = v_j + a_ij, J_(i,j),j = v_i − a_ij,
J_(i,j),h = 0 (h ∉ {i, j}). In the monomial order (x_ix_j)_{i<j}, x₁, . . . , x_N, a basis matrix
of Λ is ( X²I  XJ ; 0  pXI_N ). (6)"

The row of `P_ij` has `X²` at `x_i x_j`, `X(v_j + a_ij)` at `x_i`, `X(v_i − a_ij)` at `x_j` and
`0` elsewhere: it is the scaled coefficient vector `Φ(P_ij)` of Definition 2.3. The row of `p x_h`
has `pX` at `x_h` and `0` elsewhere: it is `Φ(p x_h)`.

**Formalization Note.** Rows are indexed by `Mon N` rather than listed in the algorithm's order
(`P_ij`, then `px₂, …, px_N, px₁`); a reordering of the rows changes neither the lattice nor `v_tar`.
The paper's own matrix (6) also reorders them. -/
noncomputable def latticeBasis (I : MIHNPInput) : Mon I.N → EuclideanSpace ℝ (Mon I.N) :=
  fun r => WithLp.toLp 2 fun c =>
    match r, c with
    | Sum.inl q, Sum.inl q' => if q = q' then (I.X : ℝ) ^ 2 else 0
    | Sum.inl q, Sum.inr h =>
        if h = q.1.1 then (I.X : ℝ) * ((I.v q.1.2 : ℝ) + (aij I.p (I.t q.1.1) (I.t q.1.2) : ℝ))
        else if h = q.1.2 then
          (I.X : ℝ) * ((I.v q.1.1 : ℝ) - (aij I.p (I.t q.1.1) (I.t q.1.2) : ℝ))
        else 0
    | Sum.inr _, Sum.inl _ => 0
    | Sum.inr h, Sum.inr h' => if h = h' then (I.p : ℝ) * I.X else 0

/-- **The target vector `v_tar = Φ(p x₁)`** (§3.3, §4.1).
Kang, Lee, STOC 2027 submission (manuscript sha256 605f9dd3…), §4.1, p.23 (PDF p.24): "The vector
v_tar representing px₁ has entry pX in the x₁ coordinate and zero elsewhere."

**Formalization Note.** The paper's `x₁` is the 0-based coordinate `Sum.inr h` with `h = 0`. -/
noncomputable def vtar (I : MIHNPInput) : EuclideanSpace ℝ (Mon I.N) :=
  WithLp.toLp 2 fun c =>
    match c with
    | Sum.inl _ => 0
    | Sum.inr h => if (h : ℕ) = 0 then (I.p : ℝ) * I.X else 0

/-- **The constant `K = 1 + 12√d·4^m` of (2)** for the MIHNP lattice, `m = d = N(N + 1)/2`.
Kang, Lee, STOC 2027 submission (manuscript sha256 605f9dd3…), eq. (2), p.20 (PDF p.21): "where
K = 1 + 12√d 4^m depends only on m, d"; §4.1, p.22: "m = d = N(N + 1)/2".

**Formalization Note.** `N(N + 1)/2` is exact natural-number division (the product is even). -/
noncomputable def Kc (N : ℕ) : ℝ :=
  1 + 12 * Real.sqrt ((N * (N + 1) / 2 : ℕ) : ℝ) * 4 ^ (N * (N + 1) / 2)

end IntQuotHNP


