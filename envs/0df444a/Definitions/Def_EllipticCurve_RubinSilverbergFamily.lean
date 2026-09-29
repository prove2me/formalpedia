-- Prove2me | Definitions.Def_EllipticCurve_RubinSilverbergFamily
-- name    : EllipticCurve_RubinSilverbergFamily
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:26.503845+00:00
-- url     : https://prove2.me/theorems/2d1d2576-f6f0-5f05-b3bd-c77b67ff9ce3
-- title:
--   Klein forms, icosahedral symmetry and Rubin–Silverberg families
-- statement:
--   Over an arbitrary commutative ring the module defines Klein's icosahedral invariants in one variable, `kleinV` $V(u)=u(u^{10}+11u^5-1)$, `kleinH` $H(u)=u^{20}-228u^{15}+494u^{10}+228u^5+1$, `kleinT` $T(u)=u^{30}+522u^{25}-10005u^{20}-10005u^{10}-522u^5+1$, together with their homogenisations `kleinVHom`, `kleinHHom`, `kleinTHom` as binary forms of degrees $12$, $20$, $30$ in $(n,d)$. Over a field, `kleinCurve u` is the Weierstrass curve $y^2=x^3-\frac{H(u)}{48}x+\frac{T(u)}{864}$ (Mathlib coefficients $a_1=a_2=a_3=0$, $a_4=-H(u)/48$, $a_6=T(u)/864$), and `kleinX u`, `kleinY u` are two explicit rational functions of $u$ (quotients by $12$ and by $2$ of the displayed polynomials of degrees $10$ and $13$), intended as the coordinates of a $5$-torsion section. The helper `pt W x y` is total: it returns `WeierstrassCurve.Affine.Point.some x y h` when $(x,y)$ is nonsingular on $W$ and $0$ otherwise, with `pt_eq_some`, `pt_eq_zero` recording the two cases. Next, `rsBeta`, `rsGamma` are the explicit rational functions $\beta(u),\gamma(u)$ written in the source; `rsNum u₀ l t` $=(\beta(u_0)+\lambda u_0)t+u_0$, `rsDen u₀ l t` $=(\gamma(u_0)+\lambda)t+1$; and `rsMember a b u₀ l t` is the Weierstrass curve with $a_4=a\,H_{\hom}(\nu,\delta)/H(u_0)$ (`rsFamilyA`) and $a_6=b\,T_{\hom}(\nu,\delta)/T(u_0)$ (`rsFamilyB`). The predicate `IsKleinDatum a b u₀` is exactly the conjunction $H(u_0)^3(4a^3+27b^2)+6912\,a^3V(u_0)^5=0$ and $V(u_0)\neq0$. Finally `moeb`, `moebNum`, `moebDen` give the Möbius action $u\mapsto (g_{00}u+g_{01})/(g_{10}u+g_{11})$ and its denominator; `sqrtFive ζ` $=\zeta+\zeta^4-\zeta^2-\zeta^3$; `icoS`, `icoT`, `icoU` are the three displayed $2\times2$ matrices; and `IsIcoSymmetry g` asserts $\det g=1$, invariance of the three homogeneous Klein forms under the substitution $(n,d)\mapsto(g_{00}n+g_{01}d,\;g_{10}n+g_{11}d)$, and, for all $u$ with $V(u)\neq0$ and `moebDen g u` $\neq0$, the two equivariance identities $\mathrm{den}\cdot\beta(g\cdot u)=g_{00}\beta(u)+g_{01}\gamma(u)$ and $\mathrm{den}\cdot\gamma(g\cdot u)=g_{10}\beta(u)+g_{11}\gamma(u)$. All definitions are total, taking junk values where denominators vanish (in particular in characteristics $2$ and $3$); the substantive hypotheses appear only in the theorems using this vocabulary.
--
--   **Relation to Mathlib.** The curves are Mathlib `WeierstrassCurve` data and points are taken in `W.toAffine.Point` with Mathlib's `Nonsingular` predicate; Klein's forms, the Rubin–Silverberg family, `IsKleinDatum`, the Möbius action and `IsIcoSymmetry` have no Mathlib counterpart and are the project's own definitions.
--
--   **Where it is used.** This vocabulary supports the construction of auxiliary elliptic curves with prescribed mod $5$ behaviour: the family `rsMember a b u₀ l t` is designed so that its members have mod $5$ torsion tied to that of $y^2=x^3+ax+b$, which is what the $3$–$5$ switch in the modularity argument requires. It is imported by a large number of downstream modules in the tree.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_EllipticCurve_RubinSilverbergFamily.lean

import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

namespace RubinSilverberg

section KleinForms

variable {R : Type*} [CommRing R]

def kleinV (u : R) : R := u * (u ^ 10 + 11 * u ^ 5 - 1)

def kleinH (u : R) : R := u ^ 20 - 228 * u ^ 15 + 494 * u ^ 10 + 228 * u ^ 5 + 1

def kleinT (u : R) : R :=
  u ^ 30 + 522 * u ^ 25 - 10005 * u ^ 20 - 10005 * u ^ 10 - 522 * u ^ 5 + 1

def kleinVHom (n d : R) : R := n * d * (n ^ 10 + 11 * n ^ 5 * d ^ 5 - d ^ 10)

def kleinHHom (n d : R) : R :=
  n ^ 20 - 228 * n ^ 15 * d ^ 5 + 494 * n ^ 10 * d ^ 10 + 228 * n ^ 5 * d ^ 15 + d ^ 20

def kleinTHom (n d : R) : R :=
  n ^ 30 + 522 * n ^ 25 * d ^ 5 - 10005 * n ^ 20 * d ^ 10 - 10005 * n ^ 10 * d ^ 20
    - 522 * n ^ 5 * d ^ 25 + d ^ 30

end KleinForms

section KleinCurve

variable {K : Type*} [Field K]

def kleinCurve (u : K) : WeierstrassCurve K :=
  ⟨0, 0, 0, -kleinH u / 48, kleinT u / 864⟩

def kleinX (u : K) : K :=
  (u ^ 10 + 12 * u ^ 8 - 12 * u ^ 7 + 24 * u ^ 6 + 30 * u ^ 5 + 60 * u ^ 4 + 36 * u ^ 3
    + 24 * u ^ 2 + 12 * u + 1) / 12

def kleinY (u : K) : K :=
  (u ^ 13 + u ^ 12 + 4 * u ^ 11 + 5 * u ^ 9 + 6 * u ^ 8 + 21 * u ^ 7 + 29 * u ^ 6 + 25 * u ^ 5
    + 15 * u ^ 4 + 9 * u ^ 3 + 4 * u ^ 2 + u) / 2

noncomputable def pt (W : WeierstrassCurve K) (x y : K) : W.toAffine.Point :=
  open scoped Classical in
  if h : W.toAffine.Nonsingular x y then WeierstrassCurve.Affine.Point.some x y h else 0

theorem pt_eq_some {W : WeierstrassCurve K} {x y : K} (h : W.toAffine.Nonsingular x y) :
    pt W x y = WeierstrassCurve.Affine.Point.some x y h := by
  unfold pt
  exact dif_pos h

theorem pt_eq_zero {W : WeierstrassCurve K} {x y : K} (h : ¬ W.toAffine.Nonsingular x y) :
    pt W x y = 0 := by
  unfold pt
  exact dif_neg h

end KleinCurve

section Datum

variable {K : Type*} [Field K]

def rsBeta (u : K) : K :=
  kleinT u * (57 * u ^ 15 - 247 * u ^ 10 - 171 * u ^ 5 - 1)
    / (144 * u ^ 4 * (u ^ 10 + 11 * u ^ 5 - 1) ^ 4)

def rsGamma (u : K) : K :=
  kleinT u * (u ^ 15 - 171 * u ^ 10 + 247 * u ^ 5 + 57) / (144 * (u ^ 10 + 11 * u ^ 5 - 1) ^ 4)

def rsNum (u₀ l t : K) : K := (rsBeta u₀ + l * u₀) * t + u₀

def rsDen (u₀ l t : K) : K := (rsGamma u₀ + l) * t + 1

def rsFamilyA (a u₀ l t : K) : K :=
  a * kleinHHom (rsNum u₀ l t) (rsDen u₀ l t) / kleinH u₀

def rsFamilyB (b u₀ l t : K) : K :=
  b * kleinTHom (rsNum u₀ l t) (rsDen u₀ l t) / kleinT u₀

def rsMember (a b u₀ l t : K) : WeierstrassCurve K :=
  ⟨0, 0, 0, rsFamilyA a u₀ l t, rsFamilyB b u₀ l t⟩

def IsKleinDatum (a b u₀ : K) : Prop :=
  kleinH u₀ ^ 3 * (4 * a ^ 3 + 27 * b ^ 2) + 6912 * a ^ 3 * kleinV u₀ ^ 5 = 0 ∧ kleinV u₀ ≠ 0

end Datum

section Icosahedral

variable {K : Type*} [Field K]

def moeb (g : Matrix (Fin 2) (Fin 2) K) (u : K) : K := (g 0 0 * u + g 0 1) / (g 1 0 * u + g 1 1)

def moebDen (g : Matrix (Fin 2) (Fin 2) K) (u : K) : K := g 1 0 * u + g 1 1

def moebNum (g : Matrix (Fin 2) (Fin 2) K) (u : K) : K := g 0 0 * u + g 0 1

theorem moeb_eq_div (g : Matrix (Fin 2) (Fin 2) K) (u : K) : moeb g u = moebNum g u / moebDen g u := rfl

def sqrtFive (ζ : K) : K := ζ + ζ ^ 4 - ζ ^ 2 - ζ ^ 3

def icoS (ζ : K) : Matrix (Fin 2) (Fin 2) K := !![ζ ^ 3, 0; 0, ζ ^ 2]

def icoT : Matrix (Fin 2) (Fin 2) K := !![0, 1; -1, 0]

def icoU (ζ : K) : Matrix (Fin 2) (Fin 2) K :=
  (sqrtFive ζ)⁻¹ • !![-(ζ - ζ ^ 4), ζ ^ 2 - ζ ^ 3; ζ ^ 2 - ζ ^ 3, ζ - ζ ^ 4]

def IsIcoSymmetry (g : Matrix (Fin 2) (Fin 2) K) : Prop :=
  g.det = 1 ∧
  (∀ n d : K, kleinVHom (g 0 0 * n + g 0 1 * d) (g 1 0 * n + g 1 1 * d) = kleinVHom n d) ∧
  (∀ n d : K, kleinHHom (g 0 0 * n + g 0 1 * d) (g 1 0 * n + g 1 1 * d) = kleinHHom n d) ∧
  (∀ n d : K, kleinTHom (g 0 0 * n + g 0 1 * d) (g 1 0 * n + g 1 1 * d) = kleinTHom n d) ∧
  (∀ u : K, kleinV u ≠ 0 → moebDen g u ≠ 0 →
    moebDen g u * rsBeta (moeb g u) = g 0 0 * rsBeta u + g 0 1 * rsGamma u ∧
    moebDen g u * rsGamma (moeb g u) = g 1 0 * rsBeta u + g 1 1 * rsGamma u)

end Icosahedral

end RubinSilverberg


