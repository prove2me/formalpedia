-- Prove2me | Definitions.Def_N25_CuspPresentations
-- name    : N25_CuspPresentations
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:04:02.297507+00:00
-- url     : https://prove2.me/theorems/7804ce26-68a1-4c51-a583-8323bb7758b1
-- title:
--   Jacobian presentations for the canonical affine charts
-- statement:
--   For a pivot coordinate $i$, the file defines the finite relation family $$(Q,C,x_i-1)$$ cutting out the normalized affine chart. After choosing one omitted coordinate, it packages these three equations and the remaining three Jacobian columns as a pre-submersive presentation of relative dimension one. These presentations are the local inputs for the Jacobian-ideal smoothness argument at the primes $2$ and $3$.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Definitions.Def_N25_CanonicalAffineCharts
/-! Selected three-relation presentations for the standard canonical affine charts. -/
noncomputable section
namespace N25
open MvPolynomial

/-- The two canonical equations and the pivot equation in a finite relation family. -/
def canonicalChartRelations25 (k : Type*) [CommRing k] (pivot : Fin 4) :
    Fin 3 → CanonicalChartPolynomial25 k :=
  ![canonicalQuadric (X 0) (X 1) (X 2) (X 3),
    canonicalCubic (X 0) (X 1) (X 2) (X 3), X pivot - 1]

private theorem relationIdeal_eq (k : Type*) [CommRing k] (pivot : Fin 4) :
    Ideal.span (Set.range (canonicalChartRelations25 k pivot)) = canonicalChartIdeal25 k pivot := by
  unfold canonicalChartIdeal25
  congr 1
  ext f
  simp [canonicalChartRelations25]
  tauto

/-- Omit one variable from the three Jacobian columns. -/
def canonicalChartPresentation25 (k : Type*) [CommRing k] (pivot omitted : Fin 4) :
    Algebra.PreSubmersivePresentation k (CanonicalChartRing25 k pivot) (Fin 4) (Fin 3) :=
  (Algebra.PreSubmersivePresentation.naive (v := canonicalChartRelations25 k pivot)
    omitted.succAbove omitted.succAbove_right_injective).ofAlgEquiv
      (Ideal.quotientEquivAlgOfEq k (relationIdeal_eq k pivot))

end N25


