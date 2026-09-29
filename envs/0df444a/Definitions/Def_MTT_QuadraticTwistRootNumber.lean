-- Prove2me | Definitions.Def_MTT_QuadraticTwistRootNumber
-- name    : MTT_QuadraticTwistRootNumber
-- status  : Definition
-- author  : @riccardo.brasca
-- created : 2026-09-26T20:01:24.861311+00:00
-- url     : https://prove2.me/theorems/0ddd7a4a-8340-4cf7-b1bf-6276ee4fc306
-- title:
--   Pointwise Fricke root numbers and real eigenform coefficients
-- statement:
--   For a function $F$ on the upper half-plane, a positive integer $L$, and an even weight $k$, the Fricke root-number identity with scalar $w$ is the concrete equality
--
--   $$F\!\left(\frac{i}{Lt}\right)=wL^{k/2}t^k\overline{F(it)}\qquad(t>0).$$
--
--   This is the normalization in which $w$ is the global root number of the completed $L$-function. The predicate concerns the actual function values; it includes no nonvanishing assertion.
--
--   For an algebraic eigenform with fixed complex embedding $\iota$, the real-coefficient predicate is
--
--   $$\overline{\iota(a_n(f))}=\iota(a_n(f))\qquad(n\ge0).$$
--
--   At minimal level this is the classical self-duality condition. Together these predicates give a concrete interface for applying prescribed-local-type quadratic nonvanishing to an admissible seed.
--
--   **Formalization Note.** The root-number predicate uses natural-number division for $k/2$; its analytic uses assume even weight and positive level. It supplies neither the Fricke equation nor the equivalence with automorphic self-duality as an axiom.
-- source:
--   The imaginary-axis form of the classical Fricke identity: Bettin et al., A conjectural extension of Hecke's converse theorem, equations (1.1)--(1.3), pp.1--2, and Lemma 4.10, p.15, https://arxiv.org/pdf/1704.02570. For primitive eigenforms and their conjugates see Atkin--Li, Twists of newforms and pseudo-eigenvalues of W-operators, Invent. Math. 48 (1978), 221--243, https://doi.org/10.1007/BF01390245; the coprime twisting formula is restated in Nicolas Mascot's thesis, Theorem A.2.2.34, printed p.82, https://warwick.ac.uk/fac/sci/maths/people/staff/mascot/these.pdf. The definition specializes the Fricke equation to z=it and uses the global scalar w=i^k times the usual Fricke pseudo-eigenvalue.

import Definitions.Def_MTT_HeckeEquivalence
import Definitions.Def_KN_HorizontalPadicL

set_option autoImplicit false

namespace MTT

/-- For even weight, the pointwise Fricke identity on the positive imaginary axis
with the normalization of the global root number. -/
def HasFrickeRootNumber (F : UpperHalfPlane → ℂ) (L k : ℕ) (w : ℂ) : Prop :=
  ∀ t : ℝ, 0 < t →
    F (UpperHalfPlane.ofComplex (Complex.I / ((L : ℂ) * (t : ℂ)))) =
      w * (L : ℂ) ^ (k / 2) * (t : ℂ) ^ k *
        star (F (UpperHalfPlane.ofComplex (Complex.I * (t : ℂ))))

/-- Reality of every embedded Fourier coefficient, the classical self-dual
condition for a primitive holomorphic eigenform. -/
def Eigenform.HasRealCoefficients {N k : ℕ} {ι : Qbar →+* ℂ}
    (f : Eigenform N k ι) : Prop :=
  ∀ n : ℕ, star (ι (f.coeff n)) = ι (f.coeff n)

end MTT


