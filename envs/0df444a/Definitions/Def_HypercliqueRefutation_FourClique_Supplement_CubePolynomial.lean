-- Prove2me | Definitions.Def_HypercliqueRefutation_FourClique_Supplement_CubePolynomial
-- name    : HypercliqueRefutation_FourClique_Supplement_CubePolynomial
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T09:26:16.111324+00:00
-- url     : https://prove2.me/theorems/d285b0ac-cfcb-454e-b3fe-a7466fdd7072
-- title:
--   Binary cube, full counting polynomial and Walsh transforms
-- statement:
--   Indices form the binary cube $\{0,1\}^n$, represented by $\mathrm{Fin}(n)\to\mathbb Z/2\mathbb Z$. Coordinate addition is xor, support is the set of nonzero coordinates, and $\ell(e,\xi)$ counts the coordinates where both bits are zero. The unnormalized Walsh transform is $\widehat f(\xi)=\sum_c(-1)^{\xi\cdot c}f(c)$; the sign is cast into the coefficient ring, which is distinct from the binary index group.
--
--   For four independent arrays $X,Y,Z,W$, the polynomial is
--
--   $$
--   \Phi(z)=\sum_{a,b,c,d,t:\,\operatorname{supp}(t)\subseteq\operatorname{supp}(c\oplus d)}
--   z^{n-|c\oplus d|}(z-1)^{|t|}X_{abc}Y_{abd}Z_{ac,d\oplus t}W_{b,c\oplus t,d}.
--   $$
--
--   The two transforms are
--
--   $$
--   U_{abe}(\xi)=\sum_c(-1)^{\xi\cdot c}X_{abc}Z_{ac,c\oplus e},\qquad
--   V_{abe}(\xi)=\sum_c(-1)^{\xi\cdot c}Y_{ab,c\oplus e}W_{bc,c\oplus e}.
--   $$
--
--   The spectral expression is the full polynomial $2^{-n}\sum_{a,b,e,\xi}(2z-1)^{\ell(e,\xi)}U_{abe}(\xi)V_{abe}(\xi)$. These definitions do not assert their equality or any algorithmic complexity. The original contraction $Q$ is reused through binary labels of the published four-array contraction. The polynomial and transforms include $n=0$. The source's finite-dimensional identities are interpreted over characteristic-zero fields by the theorem; the polynomial constructors themselves require only the displayed algebraic operations.
-- source:
--   Timothy M. Chan, Reina Itakura, Zhiyuan Ma, Yuancheng Yu, The 3-Uniform Hyperclique Hypothesis is False, STOC 2027 submission #1431 (October 2026); Section 3, Eq.(4), printed/PDF p.7; Lemma 3.1 and Eq.(5), p.8; Walsh interpretation §3.2, pp.9–10.

import Mathlib
import Definitions.Def_HypercliqueRefutation_FourClique_Contractions

set_option autoImplicit false
noncomputable section

namespace HypercliqueRefutation.FourClique.Supplement

/- Chan--Itakura--Ma--Yu, STOC 2027 submission #1431 (October 2026),
   Section 3, Eq.(4), p.7, and Lemma 3.1, Eq.(5), p.8.
   The index group is the binary cube; the coefficient field is separate. -/
abbrev Cube (n : ℕ) := Fin n → ZMod 2
abbrev CubeArray (K : Type*) (n : ℕ) := Cube n → Cube n → Cube n → K

def support {n : ℕ} (a : Cube n) : Finset (Fin n) :=
  Finset.univ.filter (fun j => a j ≠ 0)

def zeroZero {n : ℕ} (e ξ : Cube n) : ℕ :=
  (Finset.univ.filter (fun j => e j = 0 ∧ ξ j = 0)).card

def walshSign {K : Type*} [Ring K] {n : ℕ} (ξ c : Cube n) : K :=
  (-1 : K) ^ (∑ j, (ξ j).val * (c j).val)

def walsh {K : Type*} [CommRing K] {n : ℕ} (f : Cube n → K) (ξ : Cube n) : K :=
  ∑ c, walshSign ξ c * f c

def transformU {K : Type*} [CommRing K] {n : ℕ}
    (X Z : CubeArray K n) (a b e ξ : Cube n) : K :=
  walsh (fun c => X a b c * Z a c (c + e)) ξ

def transformV {K : Type*} [CommRing K] {n : ℕ}
    (Y W : CubeArray K n) (a b e ξ : Cube n) : K :=
  walsh (fun c => Y a b (c + e) * W b c (c + e)) ξ

/-- The binary label of a source array index, used only for the scalar Q.
    It is not an assumption that the hypergraph size is a power of two. -/
def cubeLabel {n : ℕ} (a : Fin (2 ^ n)) : Cube n :=
  fun j => ((a.val / 2 ^ j.val : ℕ) : ZMod 2)

def cubeQ {K : Type*} [CommSemiring K] {n : ℕ}
    (X Y Z W : CubeArray K n) : K :=
  fourArrayContraction
    (fun a b c => X (cubeLabel a) (cubeLabel b) (cubeLabel c))
    (fun a b c => Y (cubeLabel a) (cubeLabel b) (cubeLabel c))
    (fun a b c => Z (cubeLabel a) (cubeLabel b) (cubeLabel c))
    (fun a b c => W (cubeLabel a) (cubeLabel b) (cubeLabel c))

/-- Eq.(4), including every coefficient and every support-restricted t. -/
def phi {K : Type*} [CommRing K] {n : ℕ}
    (X Y Z W : CubeArray K n) : Polynomial K :=
  ∑ a, ∑ b, ∑ c, ∑ d, ∑ t : Cube n,
    if support t ⊆ support (c + d) then
      Polynomial.X ^ (n - (support (c + d)).card) *
        (Polynomial.X - 1) ^ (support t).card *
        Polynomial.C (X a b c * Y a b d * Z a c (d + t) * W b (c + t) d)
    else 0

/-- Eq.(5), with U and V embedded as constant polynomials. -/
def spectralPhi {K : Type*} [Field K] {n : ℕ}
    (X Y Z W : CubeArray K n) : Polynomial K :=
  Polynomial.C (((2 : K) ^ n)⁻¹) *
    ∑ a, ∑ b, ∑ e, ∑ ξ : Cube n,
      (2 * Polynomial.X - 1) ^ (zeroZero e ξ) *
        Polynomial.C (transformU X Z a b e ξ * transformV Y W a b e ξ)

end HypercliqueRefutation.FourClique.Supplement


