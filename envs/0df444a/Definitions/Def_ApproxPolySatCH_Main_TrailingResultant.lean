-- Prove2me | Definitions.Def_ApproxPolySatCH_Main_TrailingResultant
-- name    : ApproxPolySatCH_Main_TrailingResultant
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-09T16:10:43.752688+00:00
-- url     : https://prove2.me/theorems/9572a06c-cd43-4912-aeea-1a0eb55770ee
-- title:
--   Homogenized perturbations, iterated trailing coefficients and substitution
-- statement:
--   For a polynomial in a variable $U$, its trailing coefficient is the coefficient at the least nonzero exponent; the trailing coefficient of zero is zero. Homogenization adds $X_0$ to reach the actual total degree. For the prescribed fiber, set $G_i=\operatorname{hom}(f_i-a_i\varepsilon)$ and $F=\operatorname{hom}(f_{n+1})$, of degrees $d_i$ and $d$.
--
--   The source's forms are
--   $$\widetilde G_i=G_i+TX_i^{d_i},\qquad L_{\mathrm{form}}=ZX_0^d+\sum_{i=1}^nW^iX_i^d-F,$$
--   $$R_0=\operatorname{Res}(\widetilde G_1,\ldots,\widetilde G_n,L_{\mathrm{form}}),\qquad R_2=\operatorname{TT}_W\operatorname{TT}_T R_0.$$
--   The last expression first takes the T-trailing coefficient, then the W-trailing coefficient. Auxiliary indices are T=0, W=1, epsilon=2, Z=3. Evaluation embeds the constants and epsilon into the valued closure while retaining Z as a polynomial variable. With $b=D_0+1$, the Kronecker substitution is $T=\varepsilon^{b^2}$ and $W=\varepsilon^b$.
--
--   These are the actual homogenized forms, including their projective behavior; no points at infinity are removed.
-- source:
--   Nikhil Balaji, Mahsa Shirmohammadi, Sébastien Tavenas, James Worrell, STOC 2027 submission #1125 (October 2026), §§2,4, pp.11–13,21–23, equations (20)–(23); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1125.pdf

import Definitions.Def_ApproxPolySatCH_Main_Algebra
import Definitions.Def_ApproxPolySatCH_Main_UniversalResultant

set_option autoImplicit false

namespace ApproxPolySatCH.Main

noncomputable def coefficientIn {A : Type} [CommRing A] {n : ℕ}
    (v : Fin n) (j : ℕ) (p : Poly A n) : Poly A n :=
  ∑ e ∈ p.support, if e v = j then MvPolynomial.monomial (e - Finsupp.single v j) (p.coeff e) else 0

open Classical in
noncomputable def trailing {A : Type} [CommRing A] {n : ℕ} (v : Fin n) (p : Poly A n) : Poly A n :=
  if h : p.support.Nonempty then
    coefficientIn v ((p.support.image (fun e => e v)).min' (h.image _)) p else 0

/-- The order is first T, then W; auxiliary indices are T=0,W=1,epsilon=2,Z=3. -/
noncomputable def twiceTrailing {A : Type} [CommRing A] (p : Poly A 4) : Poly A 4 :=
  trailing 1 (trailing 0 p)

noncomputable def homogenize {A : Type} [CommRing A] {n : ℕ} (d : ℕ) (p : Poly A n) : Poly A (n + 1) :=
  ∑ e ∈ p.support, MvPolynomial.monomial
    (Finsupp.single 0 (d - e.sum (fun _ j => j)) + e.mapDomain Fin.succ) (p.coeff e)

noncomputable def formCoefficients {k : Type} [Field k] : k →+* Poly (Constants k) 4 :=
  MvPolynomial.C.comp (algebraMap k (Constants k))

noncomputable def Gi {k : Type} [Field k] {n : ℕ}
    (f : Fin (n + 1) → Poly k n) (a : Fin n → Constants k) (i : Fin n) :
    Poly (Poly (Constants k) 4) (n + 1) :=
  homogenize (f i.castSucc).totalDegree
    (MvPolynomial.map (formCoefficients (k := k)) (f i.castSucc) -
      MvPolynomial.C (MvPolynomial.C (a i) * MvPolynomial.X 2))

noncomputable def finalForm {k : Type} [Field k] {n : ℕ}
    (f : Fin (n + 1) → Poly k n) : Poly (Poly (Constants k) 4) (n + 1) :=
  homogenize (f (Fin.last n)).totalDegree
    (MvPolynomial.map (formCoefficients (k := k)) (f (Fin.last n)))

noncomputable def perturbedGi {k : Type} [Field k] {n : ℕ}
    (f : Fin (n + 1) → Poly k n) (a : Fin n → Constants k) (i : Fin n) :
    Poly (Poly (Constants k) 4) (n + 1) :=
  Gi f a i + MvPolynomial.C (MvPolynomial.X 0) * MvPolynomial.X i.succ ^ (f i.castSucc).totalDegree

noncomputable def lastForm {k : Type} [Field k] {n : ℕ}
    (f : Fin (n + 1) → Poly k n) : Poly (Poly (Constants k) 4) (n + 1) :=
  let d := (f (Fin.last n)).totalDegree
  MvPolynomial.C (MvPolynomial.X 3) * MvPolynomial.X 0 ^ d +
    (∑ i : Fin n, MvPolynomial.C (MvPolynomial.X 1 ^ (i.val + 1)) * MvPolynomial.X i.succ ^ d) -
    finalForm f

noncomputable def R0 {k : Type} [Field k] {n : ℕ}
    (f : Fin (n + 1) → Poly k n) (a : Fin n → Constants k) : Poly (Constants k) 4 :=
  homogeneousResultant
    (Fin.lastCases (f (Fin.last n)).totalDegree (fun i : Fin n => (f i.castSucc).totalDegree))
    (Fin.lastCases (lastForm f) (perturbedGi f a))

/-- Evaluate epsilon in the valued closure; leave Z as a polynomial variable. -/
noncomputable def asZPolynomial {k : Type} [Field k] (p : Poly (Constants k) 4) :
    Polynomial (ValuedClosure k) :=
  MvPolynomial.eval₂ (Polynomial.C.comp (constantsMap k))
    ![0, 0, Polynomial.C (epsilon k), Polynomial.X] p

noncomputable def kroneckerSubstitution {A : Type} [CommRing A] (D : ℕ) (p : Poly A 4) : Poly A 4 :=
  let b := D + 1
  MvPolynomial.eval₂ MvPolynomial.C
    ![MvPolynomial.X 2 ^ (b ^ 2), MvPolynomial.X 2 ^ b, MvPolynomial.X 2, MvPolynomial.X 3] p
end ApproxPolySatCH.Main


