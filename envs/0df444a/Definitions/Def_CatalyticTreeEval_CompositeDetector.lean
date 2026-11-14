-- Prove2me | Definitions.Def_CatalyticTreeEval_CompositeDetector
-- name    : CatalyticTreeEval_CompositeDetector
-- status  : Definition
-- author  : @sragavan
-- created : 2026-11-14T01:55:58.6422+00:00
-- url     : https://prove2.me/theorems/394bf63d-9876-4576-84f7-bd727163f8e3
-- title:
--   CRT combination of prime-power weight detectors
-- statement:
--   For distinct primes $p_i$ and prime-coefficient polynomials $f_i$, form a polynomial modulo $m=\prod_i p_i$ by lifting every coefficient through the Chinese remainder map. The composite weight detector applies this construction to the explicit prime-power detectors. The support is contained in the union of their supports; its evaluation and degree properties are proved separately.
-- source:
--   Henzinger, Pyne and Ragavan, Catalytic Tree Evaluation from Matching Vectors, https://arxiv.org/html/2602.14320v3, Appendix B, Corollary B.6.

import Definitions.Def_CatalyticTreeEval_WeightDetector
import Definitions.Def_CatalyticTreeEval_CRT

set_option autoImplicit false

namespace CatalyticTreeEval.Main

/-- Lift a family of prime-coefficient polynomials coefficient by coefficient. -/
noncomputable def crtPolynomial {t H : ℕ} (p : Fin t → ℕ) (hp : PrimeData p)
    (f : (i : Fin t) → Poly (p i) H) : Poly (modulus p) H := by
  classical
  exact ∑ v ∈ Finset.univ.biUnion (fun i => (f i).support),
    MvPolynomial.monomial v (CRT.crtLift p hp (fun i => MvPolynomial.coeff v (f i)))

/-- Composite detector obtained by CRT from the explicit prime-power detectors. -/
noncomputable def compositeWeightDetector {t : ℕ} (p e : Fin t → ℕ)
    (hp : PrimeData p) (w H : ℕ) : Poly (modulus p) H :=
  crtPolynomial p hp (fun i => weightDetector (p i) (e i) w H)

end CatalyticTreeEval.Main


