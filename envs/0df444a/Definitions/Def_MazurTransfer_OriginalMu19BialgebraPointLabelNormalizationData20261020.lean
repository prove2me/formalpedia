-- Prove2me | Definitions.Def_MazurTransfer_OriginalMu19BialgebraPointLabelNormalizationData20261020
-- name    : MazurTransfer_OriginalMu19BialgebraPointLabelNormalizationData20261020
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-22T01:28:55.354846+00:00
-- url     : https://prove2.me/theorems/fe230b71-a880-48c6-a13e-6c3d016c6f20
-- title:
--   Original arithmetic multiplicative root label for cyclic bialgebra normalization
-- statement:
--   Retain the original multiplicative form of the given arithmetic root label. Its complete original type and whole value, generated helper types, and original literal-root and cyclic-group contexts are independently checked. Named downstream consumer: normalize the given cyclic bialgebra equivalence over the same base so its literal field points equal the same given arithmetic root label.
-- source:
--   MazurTheorem Mu19BialgebraPointLabelNormalization by Vas and contributors; same given bialgebra equivalence and arithmetic root label over the same base, Apache-2.0.

import Definitions.Def_MazurTransfer_OriginalNineteenRootsCyclotomicPowerData20261020
import Definitions.Def_MazurTransfer_OriginalCyclicNineteenGroupAlgebraPointsData20261020
/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: normalize a GIVEN cyclic bialgebra equivalence so its
literal field points equal the GIVEN arithmetic root label, pointwise.
The adjustment is a bialgebra automorphism defined over the SAME base.
Named downstream consumer: exact selected-pi quotient restriction identity
in the literal mu19 model, before actual norm torsor pushforward.
-/

noncomputable section
namespace MazurTransfer.Mu19BialgebraPointLabelNormalization
open CyclicNineteenGroupAlgebraPoints
open NineteenRootsGaloisRepresentation
variable {R H K : Type} [CommRing R] [CommRing H] [Bialgebra R H]
variable [Field K] [CharZero K] [IsAlgClosed K] [Algebra R K]
variable (φ : H ≃ₐc[R] MonoidAlgebra R Cyclic)
variable (e : WithConv (H →ₐ[R] K) ≃ Additive (Roots K))
variable (he_add : ∀ f g, e (f * g) = e f + e g)

include he_add in
def arithmeticMulEquiv : WithConv (H →ₐ[R] K) ≃* Roots K where
  __ := e.trans Additive.toMul
  map_mul' f g := congrArg Additive.toMul (he_add f g)



end MazurTransfer.Mu19BialgebraPointLabelNormalization

#print axioms MazurTransfer.Mu19BialgebraPointLabelNormalization.arithmeticMulEquiv


