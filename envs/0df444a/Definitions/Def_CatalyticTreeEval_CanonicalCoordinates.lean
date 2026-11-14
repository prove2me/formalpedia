-- Prove2me | Definitions.Def_CatalyticTreeEval_CanonicalCoordinates
-- name    : CatalyticTreeEval_CanonicalCoordinates
-- status  : Definition
-- author  : @sragavan
-- created : 2026-11-14T02:23:26.241345+00:00
-- url     : https://prove2.me/theorems/4f38528d-f76d-46ba-89f7-29e7688556d7
-- title:
--   Explicit subset and monomial indexing for canonical matching vectors
-- statement:
--   A canonical indexing supplies injective enumerations of the w-subsets and all square-free monomials below the degree cutoff. Coefficient vectors come from restricting the fixed CRT weight detector to an enumerated subset; evaluation vectors evaluate the same enumerated monomials at subset characteristic points. Matching, exact cardinalities and efficient native access are subsequent obligations.
-- source:
--   Henzinger, Pyne and Ragavan, Catalytic Tree Evaluation from Matching Vectors, https://arxiv.org/html/2602.14320v3, Appendix B, Lemma B.1.

import Definitions.Def_CatalyticTreeEval_CompositeDetector
import Definitions.Def_CatalyticTreeEval_SubsetPolynomials
import Definitions.Def_CatalyticTreeEval_MultilinearCoordinates

set_option autoImplicit false

namespace CatalyticTreeEval.Main

/-- The two explicit finite indexings needed by the canonical construction. -/
structure CanonicalIndexing (H w δ : ℕ) where
  subset : Fin (H.choose w) → Finset (Fin H)
  monomial : Fin (binomialDimension H δ) → Monomial H
  subset_card : ∀ i, (subset i).card = w
  subset_injective : Function.Injective subset
  monomial_injective : Function.Injective monomial
  monomial_cover : ∀ v : Monomial H, (∀ i, v i ≤ 1) →
    v.sum (fun _ e => e) < δ → ∃ j, monomial j = v

noncomputable def canonicalCoefficientVectors {t : ℕ} (p e : Fin t → ℕ)
    (hp : PrimeData p) (w H : ℕ) (I : CanonicalIndexing H w (delta p e)) :
    Fin (H.choose w) → Vec (modulus p) (binomialDimension H (delta p e)) :=
  fun i j => MvPolynomial.coeff (I.monomial j)
    (restrictPolynomial (I.subset i) (compositeWeightDetector p e hp w H))

noncomputable def canonicalEvaluationVectors {t : ℕ} (p e : Fin t → ℕ)
    (w H : ℕ) (I : CanonicalIndexing H w (delta p e)) :
    Fin (H.choose w) → Vec (modulus p) (binomialDimension H (delta p e)) :=
  fun i j => monomialValue (boolPoint (subsetPoint (I.subset i))) (I.monomial j)

end CatalyticTreeEval.Main


