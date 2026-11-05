-- Prove2me | Definitions.Def_DiamondCertificate
-- name    : DiamondCertificate
-- status  : Definition
-- author  : @benediamond
-- created : 2026-11-04T20:09:44.689144+00:00
-- url     : https://prove2.me/theorems/adbd0c9a-ff4d-4c6e-918f-2df60d3f073d
-- title:
--   Diamond certificates
-- statement:
--   For arbitrary $n,d,q\in\mathbb N$, work in $\mathbb C[z_0,\ldots,z_n]$. Require a nonzero homogeneous $F$ of degree $d$ and a homogeneous $A$ of integer degree $d\cdot(q+1)-(n+1)$. A certificate consists of a nonzero homogeneous denominator $D$ relatively prime to $F$ and polynomial numerators $N_i$ of integer degree $\deg(D)+d\cdot q-n$ satisfying the key equation for $v_i=N_i/D$:
--
--   $$F^{q+1}\mid A-q\cdot dF(v)+F\cdot\operatorname{div}(v).$$
--
--   Divisibility is in the localization whose denominators are relatively prime to $F$. There is no bound on $\deg(D)$. A polynomial of negative prescribed degree must be zero. This formalism is based on [Diamond's reduction](https://arxiv.org/abs/2603.29157).
-- source:
--   https://arxiv.org/abs/2603.29157; https://github.com/hodge-computer/sextics/pull/211

import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Analysis.Complex.Basic
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.Polynomial.UniqueFactorization

set_option autoImplicit false
noncomputable section
namespace HodgeComputer
open MvPolynomial
open scoped BigOperators

abbrev AmbientPoly (n : ℕ) := MvPolynomial (Fin (n + 1)) ℂ

def directional {n : ℕ} (P : AmbientPoly n) (N : Fin (n + 1) → AmbientPoly n) : AmbientPoly n :=
  ∑ i, pderiv i P * N i

def divergence {n : ℕ} (N : Fin (n + 1) → AmbientPoly n) : AmbientPoly n :=
  ∑ i, pderiv i (N i)

def divergenceNumerator {n : ℕ} (D : AmbientPoly n) (N : Fin (n + 1) → AmbientPoly n) : AmbientPoly n :=
  D * divergence N - directional D N

/-- Exact cleared defect, with the pole parameter retained. -/
def defect {n : ℕ} (F A D : AmbientPoly n) (q : ℕ)
    (N : Fin (n + 1) → AmbientPoly n) : AmbientPoly n :=
  A * D^2 - (q : AmbientPoly n) * D * directional F N +
    F * divergenceNumerator D N

/-- Homogeneity with an integer degree. Negative degrees permit only zero. -/
def Homogeneous {σ : Type*} (P : MvPolynomial σ ℂ) (k : ℤ) : Prop :=
  ∀ ⦃m : σ →₀ ℕ⦄, coeff m P ≠ 0 → (m.degree : ℤ) = k

/-- A rational-vector-field certificate in projective dimension `n`, for a
nonzero degree-`d` hypersurface and pole parameter `q`. All subtractions in
homogeneity degrees are in the integers. The denominator degree is unrestricted. -/
structure Verify {n : ℕ} (F A : AmbientPoly n) (d q : ℕ) (D : AmbientPoly n)
    (N : Fin (n + 1) → AmbientPoly n) (Q : AmbientPoly n) : Prop where
  hypersurface_ne_zero : F ≠ 0
  hypersurface_homogeneous : F.IsHomogeneous d
  source_homogeneous : Homogeneous A ((d : ℤ) * (q + 1) - (n + 1))
  denominator_ne_zero : D ≠ 0
  denominator_homogeneous : D.IsHomogeneous D.totalDegree
  numerator_homogeneous : ∀ i, Homogeneous (N i) ((D.totalDegree : ℤ) + d*q - n)
  denominator_legal : IsRelPrime F D
  identity : defect F A D q N = F^(q+1) * Q

def HasCertificate {n : ℕ} (F A : AmbientPoly n) (d q : ℕ) : Prop :=
  ∃ D N Q, Verify F A d q D N Q

end HodgeComputer


