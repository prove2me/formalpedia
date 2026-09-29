-- Prove2me | Definitions.Def_MTT_PeriodPairing
-- name    : MTT_PeriodPairing
-- status  : Definition
-- author  : @davidloeffler
-- created : 2026-09-07T22:14:55.445329+00:00
-- url     : https://prove2.me/theorems/6b4f30ef-2b71-4ccb-bae8-0f42114ef260
-- title:
--   Mixed period primitives, determinant contraction and Petersson integrals
-- statement:
--   For the MTT binary-polynomial coefficient model, put $n=k-2$ and $L_z=zX+Y$. This module defines the reflection $z\mapsto-\bar z$, the pure powers $L_z^n$, and the determinant contraction
--   $$B_n(P,Q)=\sum_{j=0}^n\frac{(-1)^{n-j}P_jQ_{n-j}}{\binom nj}.$$
--   It specifies an equivariant primitive of the mixed differential
--   $$g(z)L_z^n\,dz-\overline{v(z)}L_{\bar z}^n\,d\bar z$$
--   by coefficientwise real Fréchet derivatives, homogeneity, equivariance under $\Gamma_1(N)$, and at most polynomial coefficient growth in every integral cusp chart on each bounded horizontal strip. Values of its representing function outside the upper half-plane are unrestricted.
--
--   It also defines two explicit integrals:
--   $$\mathcal B_n(f,q)=\int y^2B_n(f(z)L_z^n,\overline{q(z)}L_{\bar z}^n)\,d\mu,\qquad
--   \langle f,q\rangle=\int f(z)\overline{q(z)}y^k\,d\mu,$$
--   where $d\mu=dx\,dy/y^2$. Each integral means the sum over $\mathrm{SL}_2(\mathbb Z)/\Gamma_1(N)$ of integrals on the standard closed modular fundamental region, evaluating the density at the inverse representative applied to $z$. The quotient is finite when $N>0$. This convention can count the geometric domain twice if $-I$ is absent; the convention is the same for both products. The sums and integrals are definitions only: convergence, invariance, the pure-power contraction identity, Stokes vanishing, and definiteness are separate theorem obligations.
-- source:
--   Columbia Spring 2021 modular-forms seminar notes, Week 4–5, §1.2, Theorem 1 and its injectivity proof, pp. 7–10, https://www.math.columbia.edu/~dmarcil/Seminars/2021_Spring/Notes/Week4-5.pdf. These four lemmas adapt the invariant-contraction/Stokes proof to the MTT mission’s binary-polynomial, reflected-summand and normalized cusp-primitive conventions; the coefficientwise derivative and finite-coset integral interfaces are explicit formalization choices.

import Definitions.Def_MTT_Cohomology_Integration
import Mathlib.Analysis.Complex.UpperHalfPlane.Measure
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.NumberTheory.Modular

set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate
open MeasureTheory
namespace MTT.Cohomology

/-- The antiholomorphic involution of the upper half-plane. -/
def periodReflect (z : UpperHalfPlane) : UpperHalfPlane :=
  ⟨-conj (z : ℂ), by simpa using z.im_pos⟩

/-- The pure power (zX+Y)^n. -/
def periodPower (n : ℕ) (z : ℂ) : Binary ℂ :=
  (MvPolynomial.C z * MvPolynomial.X 0 + MvPolynomial.X 1) ^ n

/-- Determinant contraction, normalized to B((zX+Y)^n,(wX+Y)^n)=(z-w)^n. -/
def periodContraction (n : ℕ) (P Q : Binary ℂ) : ℂ :=
  ∑ j ∈ Finset.range (n + 1),
    (-1 : ℂ) ^ (n - j) * MvPolynomial.coeff (binaryExponent n j) P *
      MvPolynomial.coeff (binaryExponent n (n - j)) Q / (n.choose j : ℂ)

/-- Complex-valued real-linear differential a dz + b d(conj z). -/
def periodDifferential (a b : ℂ) : ℂ →L[ℝ] ℂ :=
  a • (ContinuousLinearMap.id ℝ ℂ) + b • (Complex.conjCLE : ℂ →L[ℝ] ℂ)

/-- Coefficientwise C¹ primitive of g(z)(zX+Y)^n dz - conj(v(z))(conj(z)X+Y)^n d(conj z),
with equivariance and at most polynomial growth in every cusp chart.
The derivative is taken on the open upper half-plane, so values below it are immaterial. -/
def IsMixedPeriodPrimitive {N k : ℕ}
    (g v : CuspForm (MTT.GammaOne N) (k : ℤ)) (U : ℂ → Binary ℂ) : Prop :=
  (∀ z : UpperHalfPlane, U z ∈ Sym ℂ (k - 2)) ∧
  (∀ (γ : CongruenceSubgroup.Gamma1 N) (z : UpperHalfPlane),
    U (γ.val • z : UpperHalfPlane) = act γ.val.val (U z)) ∧
  (∀ (z : UpperHalfPlane) (e : Fin 2 →₀ ℕ),
    HasFDerivAt (fun w : ℂ => MvPolynomial.coeff e (U w))
      (periodDifferential
        (MvPolynomial.coeff e (g z • periodPower (k - 2) z))
        (-MvPolynomial.coeff e (conj (v z) • periodPower (k - 2) (conj (z : ℂ)))))
      (z : ℂ)) ∧
  (∀ (δ : Matrix.SpecialLinearGroup (Fin 2) ℤ) (e : Fin 2 →₀ ℕ)
      (W : ℝ), 0 < W → ∃ (C : ℝ) (A : ℕ), 0 ≤ C ∧
    ∀ z : UpperHalfPlane, 1 ≤ z.im → |z.re| ≤ W →
      ‖MvPolynomial.coeff e (act (δ⁻¹).val (U (δ • z : UpperHalfPlane)))‖ ≤
        C * (1 + z.im) ^ A)

/-- Integrate an invariant scalar density by summing over right-coset representatives
(inverted to obtain left-coset representatives), using hyperbolic measure.
For N>0 the indexing quotient is finite. The possible central multiplicity is harmless. -/
def periodDomainIntegral (N : ℕ) (F : UpperHalfPlane → ℂ) : ℂ :=
  ∑' q : Matrix.SpecialLinearGroup (Fin 2) ℤ ⧸ CongruenceSubgroup.Gamma1 N,
    ∫ z in ModularGroup.fd, F (q.out⁻¹ • z)

/-- Wedge contraction with the universal nonzero dz∧d(conj z) factor removed.
The factor y² converts the area density to hyperbolic measure. -/
def periodPairing (N n : ℕ) (f q : UpperHalfPlane → ℂ) : ℂ :=
  periodDomainIntegral N (fun z => (z.im : ℂ) ^ 2 *
    periodContraction n (f z • periodPower n z)
      (conj (q z) • periodPower n (conj (z : ℂ))))

/-- The Petersson product, linear in the first argument, with the same domain convention. -/
def periodPetersson (N k : ℕ) (f q : UpperHalfPlane → ℂ) : ℂ :=
  periodDomainIntegral N (fun z => f z * conj (q z) * (z.im : ℂ) ^ k)

end MTT.Cohomology


