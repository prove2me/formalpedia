-- Prove2me | Definitions.Def_AlgebraicCurve_WeilDatum
-- name    : AlgebraicCurve_WeilDatum
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:24.773853+00:00
-- url     : https://prove2.me/theorems/04677cd8-0a61-5bca-bb6c-fa3be67d4c59
-- title:
--   Weil pairing data on a curve: divisors, functions, pairing value
-- statement:
--   Over a field extension $F/K$, the structure [`AlgebraicCurve.WeilDatum K F n`](../def/AlgebraicCurve_WeilDatum.html#L14), for a natural number $n$, packages an explicit presentation of a pair of $n$-torsion divisor classes together with the functions witnessing the torsion. Its fields are two divisors $D_1, D_2 : \mathrm{Place}\,K\,F \to_{f} \mathbb{Z}$ (finitely supported functions on the places of $F/K$, a place being a valuation subring of $F$ containing the image of $K$, proper in $F$, whose ideals are principal), two elements $f_1, f_2 \in F$ together with proofs that they are nonzero, and four properties carried as fields: $\operatorname{ord}_v(f_1) = n\,D_1(v)$ and $\operatorname{ord}_v(f_2) = n\,D_2(v)$ for every place $v$, where $\operatorname{ord}_v$ is minus the logarithm of the adic valuation attached to $v$; a disjointness condition, namely $D_1(v) = 0$ or $D_2(v) = 0$ for every $v$; and a rationality condition, namely that whenever $D_1(v) \neq 0$ or $D_2(v) \neq 0$ the place $v$ is rational, i.e. $K \to \kappa(v)$ is surjective.
--
--   For such a datum $d$, `WeilDatum.pairing` is the element of $K$ given by
--   $$\frac{f_1(D_2)}{f_2(D_1)}, \qquad f(D) = \prod_{v \in \operatorname{supp} D} \big(\mathrm{ev}_v(f)\big)^{D(v)},$$
--   where $\mathrm{ev}_v(f)$ is the element of $K$ mapping to the residue of $f$ at $v$ when $f$ lies in the valuation subring of $v$, and $0$ otherwise; the quotient is formed in the field $K$, with no nonvanishing asserted. Two operations on data are defined: `WeilDatum.symm` exchanges the two components, producing the datum $(D_2, D_1, f_2, f_1)$, and `WeilDatum.addLeft`, given a second datum $d'$ of the same order with $d.D_2 = d'.D_2$ and $d.f_2 = d'.f_2$, produces the datum $(D_1 + D_1', D_2, f_1 f_1', f_2)$.
--
--   **Relation to Mathlib.** Mathlib has no notion of Weil pairing datum in this divisor-theoretic form; the ambient notions of place, divisor and order function are the project's own, built on Mathlib's valuation subrings and adic valuations.
--
--   **Where it is used.** These data are the explicit representatives on which the Weil pairing $e_n$ on $n$-torsion divisor classes is computed: the properties of the pairing (its $n$-th power being trivial given Weil reciprocity, antisymmetry, additivity in each argument) are formulated over this module, `symm` and `addLeft` supplying the shapes in which antisymmetry and additivity are stated.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AlgebraicCurve_WeilDatum.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_PlaceEvaluation

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

namespace AlgebraicCurve

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

variable (K F) in

structure WeilDatum (n : ℕ) where

  D₁ : Divisor K F

  D₂ : Divisor K F

  f₁ : F

  f₂ : F
  f₁_ne_zero : f₁ ≠ 0
  f₂_ne_zero : f₂ ≠ 0

  ord_f₁ : ∀ v : Place K F, v.ord f₁ = n * D₁ v

  ord_f₂ : ∀ v : Place K F, v.ord f₂ = n * D₂ v

  disjoint : ∀ v : Place K F, D₁ v = 0 ∨ D₂ v = 0

  rational : ∀ v : Place K F, D₁ v ≠ 0 ∨ D₂ v ≠ 0 → v.IsRational

namespace WeilDatum

variable {n : ℕ} (d : WeilDatum K F n)

def pairing : K :=
  Divisor.evalFun d.f₁ d.D₂ / Divisor.evalFun d.f₂ d.D₁

def symm : WeilDatum K F n where
  D₁ := d.D₂
  D₂ := d.D₁
  f₁ := d.f₂
  f₂ := d.f₁
  f₁_ne_zero := d.f₂_ne_zero
  f₂_ne_zero := d.f₁_ne_zero
  ord_f₁ := d.ord_f₂
  ord_f₂ := d.ord_f₁
  disjoint := fun v => (d.disjoint v).symm
  rational := fun v hv => d.rational v hv.symm

def addLeft (d' : WeilDatum K F n) (hD : d.D₂ = d'.D₂) (_hf : d.f₂ = d'.f₂) :
    WeilDatum K F n where
  D₁ := d.D₁ + d'.D₁
  D₂ := d.D₂
  f₁ := d.f₁ * d'.f₁
  f₂ := d.f₂
  f₁_ne_zero := mul_ne_zero d.f₁_ne_zero d'.f₁_ne_zero
  f₂_ne_zero := d.f₂_ne_zero
  ord_f₁ := fun v => by
    rw [v.ord_mul d.f₁_ne_zero d'.f₁_ne_zero, d.ord_f₁ v, d'.ord_f₁ v, Finsupp.add_apply,
      mul_add]
  ord_f₂ := d.ord_f₂
  disjoint := fun v => by
    rcases eq_or_ne (d.D₂ v) 0 with h2 | h2
    · exact Or.inr h2
    · refine Or.inl ?_
      rw [Finsupp.add_apply, (d.disjoint v).resolve_right h2,
        (d'.disjoint v).resolve_right (hD ▸ h2), add_zero]
  rational := fun v hv => by
    rcases hv with h1 | h2
    · rw [Finsupp.add_apply] at h1
      rcases eq_or_ne (d.D₁ v) 0 with hd | hd
      · exact d'.rational v (Or.inl fun hd' => h1 (by rw [hd, hd', add_zero]))
      · exact d.rational v (Or.inl hd)
    · exact d.rational v (Or.inr h2)

end WeilDatum

end AlgebraicCurve


