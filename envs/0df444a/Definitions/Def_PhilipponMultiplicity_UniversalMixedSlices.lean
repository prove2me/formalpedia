-- Prove2me | Definitions.Def_PhilipponMultiplicity_UniversalMixedSlices
-- name    : PhilipponMultiplicity_UniversalMixedSlices
-- status  : Definition
-- author  : @tomasz
-- created : 2026-10-07T16:27:32.779459+00:00
-- url     : https://prove2.me/theorems/550730ac-420e-4dd7-b235-9895de07453c
-- title:
--   Universal affine mixed-section coefficient algebras
-- statement:
--   For a multiprojective space $M$ over a field $K$, write $A=K[X_{i,t}]$ for its homogeneous coordinate polynomial ring. An ordered list $l$ of coordinate blocks determines a coefficient ring $C=K[T_{j,w}]$, with one parameter for every row $j$ and every original coordinate $w$.
--
--   Given $W\subseteq M$, pivot indices $b_i$, and $H\in A$, this module defines the polynomial ring $A[z][T_{j,w}]$ and the quotient
--   $$
--   B_{b,H}=A[z][T_{j,w}]\Big/\Big(I(W),\ \big(\sum_t T_{j,(l_j,t)}X_{l_j,t}\big)_j,\ (X_{i,b_i}-1)_i,\ Hz-1\Big).
--   $$
--   The map from $A$ is the composite inclusion of constant polynomials. The universal row equations use only the block selected by $l_j$; coefficient parameters outside that block remain present and unused in that row. Pivot equations fix one affine representative in each projective factor, while $Hz=1$ restricts to the principal open where $H$ is invertible. The quotient is by the displayed original equations, without taking radicals. The module contains only ring abbreviations, their inherited commutative-ring structures, and these defining expressions; specialization and quasi-finiteness are proved separately.
-- source:
--   Auxiliary affine incidence-family presentation for P. Philippon, Lemmes de zeros dans les groupes algebriques commutatifs, Bull. SMF 114 (1986), Lemma 3.1 and mixed linear sections, pp. 363–364, https://numdam.org/articles/10.24033/bsmf.2060/ . The displayed polynomial presentation is a formalization construction, not a verbatim definition in the paper. It extends the published PhilipponMultiplicity_MixedFlagParameters definitions with universal coefficient variables, affine pivot normalization, and one inverse equation.

import Definitions.Def_PhilipponMultiplicity_MixedFlagParameters
import Mathlib

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators
noncomputable section

namespace PhilipponMultiplicity.MixedFamily
variable {K : Type*} [Field K] (M : MultiProjectiveSpace K)

abbrev ParameterRing (l : List M.FactorIndex) :=
  MvPolynomial (Fin l.length × M.Variable) K

/-- The affine coordinates of a normalized slice and one inverse variable. -/
abbrev SlicePolynomial := Polynomial M.CoordinateRing

instance : CommRing (SlicePolynomial M) := inferInstanceAs (CommRing (Polynomial M.CoordinateRing))

/-- Coefficient variables over the affine coordinate polynomial ring. -/
abbrev TotalPolynomial (l : List M.FactorIndex) :=
  MvPolynomial (Fin l.length × M.Variable) (SlicePolynomial M)

instance (l : List M.FactorIndex) : CommRing (TotalPolynomial M l) :=
  inferInstanceAs (CommRing (MvPolynomial (Fin l.length × M.Variable) (SlicePolynomial M)))

def fixed (l : List M.FactorIndex) : M.CoordinateRing →+* TotalPolynomial M l :=
  MvPolynomial.C.comp Polynomial.C

def row (l : List M.FactorIndex) (j : Fin l.length) : TotalPolynomial M l :=
  ∑ t : Fin (M.ambientDimension l[j] + 1),
    MvPolynomial.X (j, (⟨l[j],t⟩ : M.Variable)) *
      fixed M l (MvPolynomial.X (⟨l[j],t⟩ : M.Variable))

/-- The original equations of the universal mixed slice, including pivot
normalizations and the inverse equation. No radical is taken. -/
def ideal (W : Set M.Point) (l : List M.FactorIndex)
    (b : ∀ i : M.FactorIndex, Fin (M.ambientDimension i + 1))
    (H : M.CoordinateRing) : Ideal (TotalPolynomial M l) :=
  (((M.vanishingIdeal W).map (fixed M l) ⊔
    ⨆ (j : Fin l.length) (_ : j.val < l.length), Ideal.span {row M l j}) ⊔
    (Ideal.span (Set.range (fun i : M.FactorIndex =>
      (MvPolynomial.X (⟨i,b i⟩ : M.Variable) : M.CoordinateRing) - 1))).map (fixed M l)) ⊔
    Ideal.span {MvPolynomial.C (Polynomial.C H * Polynomial.X - 1)}

abbrev CoordinateRing (W : Set M.Point) (l : List M.FactorIndex)
    (b : ∀ i : M.FactorIndex, Fin (M.ambientDimension i + 1))
    (H : M.CoordinateRing) := TotalPolynomial M l ⧸ ideal M W l b H

end PhilipponMultiplicity.MixedFamily


