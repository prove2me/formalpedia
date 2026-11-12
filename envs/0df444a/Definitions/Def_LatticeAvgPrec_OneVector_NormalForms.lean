-- Prove2me | Definitions.Def_LatticeAvgPrec_OneVector_NormalForms
-- name    : LatticeAvgPrec_OneVector_NormalForms
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T06:44:50.233538+00:00
-- url     : https://prove2.me/theorems/772dc4f7-af06-4f77-850f-184da165c69d
-- title:
--   Upper column Hermite normal form (Def. 2.1) and Smith massagers (Def. 2.3)
-- statement:
--   **Definition 2.1** (p.9). For nonsingular $B\in\mathbb Z^{n\times n}$, its upper column Hermite normal form is an integer matrix $H$ with $\Lambda(H)=\Lambda(B)$ that is upper triangular and satisfies $H_{ii}>0$ and $0\le H_{ij}<H_{ii}$ for $i<j$. "$H$ is in HNF" means that $H$ has this shape.
--
--   **Smith invariant factors.** For nonsingular $H$, the invariant factors are the diagonal $d_1\mid d_2\mid\cdots\mid d_n$, $d_i>0$, of a Smith form $UHV=\operatorname{diag}(d_1,\dots,d_n)$ with unimodular $U,V$. A list $s_1,\dots,s_m$ lists the invariant factors exceeding one if, as a multiset, it equals $\{d_i: d_i>1\}$.
--
--   **Definition 2.3** (p.9). Let $S=\operatorname{diag}(s_1,\dots,s_m)$ list the Smith invariant factors of $H$ that exceed one. A Smith massager for $H$ is a pair $(S,F)$, $F\in\mathbb Z^{n\times m}$, with
--   $$F^TH\in S\mathbb Z^{m\times n},\qquad F^TW-I_m\in S\mathbb Z^{m\times m}$$
--   for some $W\in\mathbb Z^{n\times m}$; it is reduced if $0\le F_{ij}<s_j$. For unimodular $H$ the pair is empty ($m=0$).
--
--   These are the integer-matrix tools of Labahn and Storjohann that the one-vector algorithm starts from.
--
--   **Formalization Note** $S\mathbb Z^{m\times p}$ is the set of integer matrices whose row $j$ is divisible by $s_j$. The order of the $s_j$ is left free (multiset equality), as the page fixes none.
-- source:
--   yang zhou, Mingsheng Wang, Zhedong Wang, Lattice Reduction at Average Precision, STOC 2027 submission #1574 (October 2026), Definition 2.1 and Definition 2.3, p.9

import Definitions.Def_LatticeAvgPrec_OneVector_Lattice
open Matrix

namespace LatticeAvgPrec.OneVector

/-- `H` is in upper column Hermite normal form (shape part of Definition 2.1, p.9): upper triangular,
`H_ii > 0`, and `0 ≤ H_ij < H_ii` for `i < j`. -/
def IsHNF {n : ℕ} (H : Matrix (Fin n) (Fin n) ℤ) : Prop :=
  (∀ i j, j < i → H i j = 0) ∧ (∀ i, 0 < H i i) ∧ ∀ i j, i < j → 0 ≤ H i j ∧ H i j < H i i

/-- Definition 2.1 (p.9): `H` is the upper column HNF of `B`: `Λ(H) = Λ(B)` and `H` has the HNF
shape. -/
def IsUpperColHNF {n : ℕ} (B H : Matrix (Fin n) (Fin n) ℤ) : Prop :=
  lat H = lat B ∧ IsHNF H

/-- `s_1, …, s_m` (in some order) are exactly the Smith invariant factors of the nonsingular `H`
that exceed one: there are unimodular `U, V` with `U H V = diag(d_1, …, d_n)`, `d_i > 0`,
`d_i ∣ d_j` for `i ≤ j`, and the multiset of the `s_j` equals the multiset of the `d_i > 1`. -/
def IsSmithFactorList {n m : ℕ} (H : Matrix (Fin n) (Fin n) ℤ) (s : Fin m → ℕ) : Prop :=
  ∃ (d : Fin n → ℕ) (U V : Matrix (Fin n) (Fin n) ℤ), IsUnit U.det ∧ IsUnit V.det ∧
    U * H * V = Matrix.diagonal (fun i => (d i : ℤ)) ∧ (∀ i, 0 < d i) ∧
    (∀ i j, i ≤ j → d i ∣ d j) ∧
    Finset.univ.val.map s = (Finset.univ.val.map d).filter (fun x => 1 < x)

/-- Definition 2.3 (p.9): `(S, F)` with `S = diag(s_1, …, s_m)` is a Smith massager for `H`:
the `s_j` are the Smith invariant factors of `H` exceeding one, `FᵀH ∈ S ℤ^{m×n}` (row `j` of
`FᵀH` divisible by `s_j`), and `FᵀW − I_m ∈ S ℤ^{m×m}` for some `W ∈ ℤ^{n×m}`. For unimodular `H`
the pair is empty (`m = 0`). -/
def IsSmithMassager {n m : ℕ} (H : Matrix (Fin n) (Fin n) ℤ) (s : Fin m → ℕ)
    (F : Matrix (Fin n) (Fin m) ℤ) : Prop :=
  IsSmithFactorList H s ∧ (∀ j i, (s j : ℤ) ∣ (Fᵀ * H) j i) ∧
    ∃ W : Matrix (Fin n) (Fin m) ℤ, ∀ j j', (s j : ℤ) ∣ (Fᵀ * W - 1 : Matrix (Fin m) (Fin m) ℤ) j j'

/-- A reduced Smith massager (Definition 2.3): additionally `0 ≤ F_ij < s_j`. -/
def IsReducedSmithMassager {n m : ℕ} (H : Matrix (Fin n) (Fin n) ℤ) (s : Fin m → ℕ)
    (F : Matrix (Fin n) (Fin m) ℤ) : Prop :=
  IsSmithMassager H s F ∧ ∀ i j, 0 ≤ F i j ∧ F i j < (s j : ℤ)

end LatticeAvgPrec.OneVector


