-- Prove2me | Definitions.Def_MazurTransfer_PolynomialPowerSubstitutionEquiv
-- name    : MazurTransfer_PolynomialPowerSubstitutionEquiv
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-17T06:09:24.60379+00:00
-- url     : https://prove2.me/theorems/77c2d27f-f525-4d59-bf9c-b95797a7b611
-- title:
--   The original power-substitution algebra isomorphism
-- statement:
--   For a commutative ring $R$ and natural number $n$, the specified maps give the original $R[T]$-algebra isomorphism $R[T][Y]/(Y^n-T)\cong R[X]$, where $T$ acts on $R[X]$ as $X^n$. This constructor is used by the power-substitution basis.
-- source:
--   MazurTheorem, Apache-2.0, Vas and contributors. One original constructor from PolynomialPowerSubstitutionPresentation.lean, with unchanged body, using the Proved public backward_forward identity and the published literal maps. The original closed type and data value are compared in the kernel. Native, strict and full frontend checks pass with standard axioms only. Named downstream consumers: the actual first- and inverse-chart parameter powers and arbitrarily-large integral FiniteMapData.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the polynomial ring with coefficient parameter acting by
X^n is the literal monic root algebra of Y^n-T.
Named downstream consumer: the power-substitution finite free basis used to
raise the degree of actual order-13 FiniteMapData.
-/
import Mathlib

import Definitions.Def_MazurTransfer_PolynomialPowerSubstitutionMaps
import Theorems.Thm_MazurTransfer_PolynomialPowerSubstitutionPresentation_backward_forward

noncomputable section
universe u
namespace MazurTransfer.PolynomialPowerSubstitutionPresentation
open Polynomial
variable (R : Type u) [CommRing R] (n : ℕ)

























def presentationEquiv : RootRing R n ≃ₐ[Source R n] Polynomial R where
  toFun := forward R n
  invFun := backward R n
  left_inv x := RingHom.congr_fun (backward_forward R n) x
  right_inv x := RingHom.congr_fun (forward_backward R n) x
  map_add' := (forward R n).map_add
  map_mul' := (forward R n).map_mul
  commutes' p := by
    change forward R n (AdjoinRoot.of (relation R n) p) = powerMap R n p
    simp [forward]

end MazurTransfer.PolynomialPowerSubstitutionPresentation
#print axioms MazurTransfer.PolynomialPowerSubstitutionPresentation.presentationEquiv


