-- Prove2me | Definitions.Def_DetParamSVP_RSConstruction
-- name    : DetParamSVP_RSConstruction
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T10:49:46.506494+00:00
-- url     : https://prove2.me/theorems/bee14e47-39a6-4cda-a5d2-f42393c92c8b
-- title:
--   The Reed–Solomon lattice and the data of the construction in Theorem 3.4 (Eqs. (5), (7)–(10))
-- statement:
--   Let $q$ be prime, $k\ge2$ and $L=k-1$; coordinates are the elements of $\mathbb F_q$, and $e_z$ is the unit vector at $z$.
--
--   1. The **Reed–Solomon lattice** (Eq. (5)) is $\mathcal L_{q,k}=\{v\in\mathbb Z^{\mathbb F_q}:\sum_{z\in\mathbb F_q}v_z z^j\equiv0\pmod q,\ 0\le j<k\}$, with $z^0=1$ for every $z$; its parity-check matrix is $H=(z^j)_{0\le j<k,\ z\in\mathbb F_q}$.
--   2. The bound of Eq. (7) is $T=1+\max\{2k,\ D,\ m+L,\ 9(L!)^5,\ 9L!\,(1+(L+h)m+Lh+\binom L2)\}$.
--   3. For distinct $y_1,\dots,y_L,x_1,\dots,x_m\in\mathbb F_q$, the shift is $s=-\sum_{\ell=1}^L e_{y_\ell}$ and $S=(x_1,\dots,x_m)$.
--   4. For $u\in\mathbb Z^m$ with support $I$ and $z_1,\dots,z_L,\tau\in\mathbb F_q$, the vector of Eq. (8) is
--   $$w=\sum_{\ell=1}^L e_{z_\ell}+\sum_{i\in I}u_i\,(e_{x_i}-e_{x_i+\tau}).$$
--   5. In $\mathbb F_q[Z_1,\dots,Z_L,Y]$, the left sides of Eq. (9) are $\sum_{\ell=1}^L(Z_\ell^j-y_\ell^j)-\sum_{i\in I}u_i\big((x_i+Y)^j-x_i^j\big)$ for $1\le j\le L$, and with $E=\{x_b-x_i:i\in I,\ b\in[m]\}$ the polynomial of Eq. (10) is
--   $$g=Y\prod_{e\in E\setminus\{0\}}(Y-e)\prod_{\ell=1}^{L}\prod_{b=1}^{m}(Z_\ell-x_b)\cdot\prod_{1\le\ell<\ell'\le L}(Z_\ell-Z_{\ell'})\prod_{\ell=1}^{L}\prod_{i\in I}(Z_\ell-x_i-Y).$$
--
--   These objects are the data of the deterministic construction of a locally dense lattice in the proof of Theorem 3.4.
--
--   **Formalization Note** The coefficients $u_i$ are cast to $\mathbb F_q$ in the polynomials and stay integers in $w$. The variables are indexed by $\{0,\dots,L\}$, with $Y$ the last one. $L=k-1$ is natural-number subtraction, used only with $k\ge2$. The parameter $d$ of Theorem 3.4 does not occur in Eq. (7) and is not an argument of $T$.
-- source:
--   Hirahara–Lin–Liu–Ogitsuka, Deterministic Parameterized Inapproximability of the Shortest Vector and Minimum Distance Problems, STOC 2027 submission (manuscript sha256 4584f5e2…), Lemma 3.3 and Eq. (5), p.19; proof of Theorem 3.4, Eqs. (7) p.19, (8) p.20, (9) and (10) p.21

import Mathlib

set_option autoImplicit false

namespace DetParamSVP

open MvPolynomial

/-- The **Reed–Solomon lattice** `L_{q,k} = {v ∈ ℤ^{F_q} : ∑_{z ∈ F_q} v_z z^j ≡ 0 (mod q),
0 ≤ j < k}` (Eq. (5)); for `j = 0` the equation uses `z^0 = 1` for every `z`.

Hirahara–Lin–Liu–Ogitsuka, *Deterministic Parameterized Inapproximability of the Shortest Vector
and Minimum Distance Problems*, STOC 2027 submission (manuscript sha256 4584f5e2…), Lemma 3.3 and
Eq. (5), p.19.

**Formalization Note.** Coordinates are the elements of `ZMod q`; the integer entries are cast to
`ZMod q` inside the congruences. Lean's `0 ^ 0 = 1` matches the paper's convention. -/
def rsLattice (q k : ℕ) [NeZero q] : Set (ZMod q → ℤ) :=
  {v | ∀ j < k, ∑ z : ZMod q, ((v z : ℤ) : ZMod q) * z ^ j = 0}

/-- The parity-check matrix `H = (z^j)_{0 ≤ j < k, z ∈ F_q}` of the Reed–Solomon lattice
(proof of Theorem 3.4, p.19: "define H = (zj)0≤j<k, z∈Fq, with z0 = 1 for every z"). -/
def vandermondeH (q k : ℕ) : Matrix (Fin k) (ZMod q) (ZMod q) :=
  fun j z => z ^ (j : ℕ)

/-- The bound `T` of Eq. (7), with `L = k − 1`:
`T = 1 + max{2k, D, m + L, 9(L!)^5, 9 L! (1 + (L + h)m + Lh + C(L, 2))}`.

Proof of Theorem 3.4, Eq. (7), p.19.

**Formalization Note.** The parameter `d` of Theorem 3.4 does not occur in Eq. (7), so it is not an
argument. `L = k − 1` is natural-number subtraction; it is used only with `k ≥ 2`. -/
def Tbound (m D h k : ℕ) : ℕ :=
  let L := k - 1
  1 + max (2 * k) (max D (max (m + L) (max (9 * L.factorial ^ 5)
    (9 * L.factorial * (1 + (L + h) * m + L * h + L.choose 2)))))

/-- The shift `s = −∑_{ℓ=1}^{L} e_{y_ℓ} ∈ ℤ^{F_q}` (proof of Theorem 3.4, p.19). -/
def rsCenter {q L : ℕ} (y : Fin L → ZMod q) : ZMod q → ℤ :=
  -∑ l, Pi.single (y l) (1 : ℤ)

/-- The support `I = {i ∈ [m] : u_i ≠ 0}` of `u ∈ ℤ^m` (proof of Theorem 3.4, p.20). -/
def supp {m : ℕ} (u : Fin m → ℤ) : Finset (Fin m) :=
  Finset.univ.filter fun i => u i ≠ 0

/-- The vector of Eq. (8): `w = ∑_{ℓ=1}^{L} e_{z_ℓ} + ∑_{i ∈ I} u_i (e_{x_i} − e_{x_i + τ})
∈ ℤ^{F_q}`, with `I` the support of `u`. The additions in the coordinate indices are in `F_q`, the
coefficients are integers (proof of Theorem 3.4, Eq. (8), p.20). -/
def eq8Vec {q L m : ℕ} (u : Fin m → ℤ) (x : Fin m → ZMod q) (z : Fin L → ZMod q) (τ : ZMod q) :
    ZMod q → ℤ :=
  ∑ l, Pi.single (z l) (1 : ℤ) +
    ∑ i ∈ supp u, u i • (Pi.single (x i) (1 : ℤ) - Pi.single (x i + τ) (1 : ℤ))

/-- The left side of Eq. (9) for the index `j`:
`∑_{ℓ=1}^{L} (Z_ℓ^j − y_ℓ^j) − ∑_{i ∈ I} u_i ((x_i + Y)^j − x_i^j) ∈ F_q[Z_1, …, Z_L, Y]`, with the
coefficients `u_i` interpreted in `F_q` (proof of Theorem 3.4, Eq. (9), p.21).

**Formalization Note.** The variables are `Fin (L + 1)`: `Z_ℓ` is `X ℓ.castSucc` and `Y` is
`X (Fin.last L)`. -/
noncomputable def eq9Poly {q L m : ℕ} (y : Fin L → ZMod q) (u : Fin m → ℤ) (x : Fin m → ZMod q)
    (j : ℕ) : MvPolynomial (Fin (L + 1)) (ZMod q) :=
  ∑ l : Fin L, (X l.castSucc ^ j - C (y l ^ j)) -
    ∑ i ∈ supp u, C ((u i : ℤ) : ZMod q) * ((C (x i) + X (Fin.last L)) ^ j - C (x i ^ j))

/-- The set `E = {x_b − x_i : i ∈ I, b ∈ [m]} ⊆ F_q` (proof of Theorem 3.4, p.21). -/
def eSet {q m : ℕ} (u : Fin m → ℤ) (x : Fin m → ZMod q) : Finset (ZMod q) :=
  (supp u ×ˢ Finset.univ).image fun ib => x ib.2 - x ib.1

/-- The polynomial `g` of Eq. (10):
`g = Y ∏_{e ∈ E∖{0}} (Y − e) ∏_{ℓ=1}^{L} ∏_{b=1}^{m} (Z_ℓ − x_b) · ∏_{1≤ℓ<ℓ′≤L} (Z_ℓ − Z_ℓ′)
∏_{ℓ=1}^{L} ∏_{i∈I} (Z_ℓ − x_i − Y)`; empty products are `1` (proof of Theorem 3.4, Eq. (10),
p.21).

**Formalization Note.** Variables as in `eq9Poly`; `E ∖ {0}` is `(eSet u x).erase 0`. -/
noncomputable def gPoly {q m : ℕ} (L : ℕ) (u : Fin m → ℤ) (x : Fin m → ZMod q) :
    MvPolynomial (Fin (L + 1)) (ZMod q) :=
  X (Fin.last L) *
    (∏ e ∈ (eSet u x).erase 0, (X (Fin.last L) - C e)) *
    (∏ l : Fin L, ∏ b : Fin m, (X l.castSucc - C (x b))) *
    (∏ l : Fin L, ∏ l' ∈ Finset.univ.filter (fun l' : Fin L => l < l'),
      (X l.castSucc - X l'.castSucc)) *
    (∏ l : Fin L, ∏ i ∈ supp u, (X l.castSucc - C (x i) - X (Fin.last L)))

end DetParamSVP


