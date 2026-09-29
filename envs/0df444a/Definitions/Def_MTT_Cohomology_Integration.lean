-- Prove2me | Definitions.Def_MTT_Cohomology_Integration
-- name    : MTT_Cohomology_Integration
-- status  : Definition
-- author  : @davidloeffler
-- created : 2026-09-06T16:39:39.512615+00:00
-- url     : https://prove2.me/theorems/77529eaa-679b-4f90-9a94-42d6876a42bd
-- title:
--   The cusp-to-cusp integration cocycle
-- statement:
--   Let $f$ be a cusp form of level $\Gamma_1(N)$ and integral weight $k$. For a rational cusp $r$, define the homogeneous period polynomial
--
--   $$
--   F_f(r;X,Y)=-2\pi i\int_r^{i\infty} f(z)(zX+Y)^{k-2}\,dz,
--   $$
--
--   and put $F_f(\infty;X,Y)=0$. Equivalently, the coefficient of $X^jY^{k-2-j}$ is
--
--   $$
--   \binom{k-2}{j}\,2\pi\int_0^\infty f(r+it)(r+it)^j\,dt.
--   $$
--
--   The raw cusp-to-cusp integration cochain is
--
--   $$
--   \Phi_f(x,y)=F_f(y)-F_f(x)=-2\pi i\int_y^x f(z)(zX+Y)^{k-2}\,dz.
--   $$
--
--   This definition isolates the explicit analytic formula. Its homogeneity, $\Gamma_1(N)$-equivariance, linearity, Hecke compatibility, and injectivity are stated separately as theorems.
-- source:
--   Shimura, Introduction to the Arithmetic Theory of Automorphic Functions (1971), Chapter 8; Ash–Stevens, Modular forms in characteristic l and special values of their L-functions (1986), §2, especially Theorem 2.3, p. 853, and §4, pp. 863–864, https://math.bu.edu/people/ghs/papers/Mod_fms_char_ell.pdf.

import Definitions.Def_MTT_Cohomology

set_option autoImplicit false
noncomputable section
open scoped BigOperators TensorProduct
namespace MTT.Cohomology

/-- The exponent vector of the binary monomial X^j Y^(n-j). -/
def binaryExponent (n j : ℕ) : Fin 2 →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun i : Fin 2 => if i = 0 then j else n - j)

/-- The homogeneous period polynomial based at the cusp at infinity. Its coefficient
of X^j Y^(k-2-j) is the normalized vertical modular integral. -/
def cuspPeriodPolynomial {N k : ℕ}
    (f : CuspForm (MTT.GammaOne N) (k : ℤ)) (r : ℚ) : Binary ℂ :=
  ∑ j ∈ Finset.range (k - 1),
    MvPolynomial.monomial (binaryExponent (k - 2) j)
      (((k - 2).choose j : ℂ) * MTT.modularIntegral f (Polynomial.X ^ j) r)

/-- A primitive for cusp-to-cusp integration, normalized to vanish at infinity. -/
def cuspPrimitive {N k : ℕ}
    (f : CuspForm (MTT.GammaOne N) (k : ℤ)) (x : Cusp) : Binary ℂ :=
  match x with
  | none => 0
  | some r => cuspPeriodPolynomial f r

/-- The raw polynomial-valued modular-symbol cocycle attached to a cusp form.
It represents -2*pi*i times the integral from the second cusp to the first. -/
def integrationCochain {N k : ℕ}
    (f : CuspForm (MTT.GammaOne N) (k : ℤ)) :
    (Cusp × Cusp) → Binary ℂ :=
  fun D => cuspPrimitive f D.2 - cuspPrimitive f D.1

end MTT.Cohomology


