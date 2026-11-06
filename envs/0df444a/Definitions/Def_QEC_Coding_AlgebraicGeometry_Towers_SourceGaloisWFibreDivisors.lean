-- Prove2me | Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceGaloisWFibreDivisors
-- name    : QEC_Coding_AlgebraicGeometry_Towers_SourceGaloisWFibreDivisors
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T05:02:02.498078+00:00
-- url     : https://prove2.me/theorems/f1d9b1e6-2036-49c0-8072-ec3395ce2116
-- title:
--   Source Galois WFibre Divisors
-- statement:
--   Definitions and structural lemmas for Source Galois WFibre Divisors, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/SourceGaloisWFibreDivisors.lean

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceGaloisWResidueDegrees
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Divisors_FinitePlaceDivisor
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_sourceGaloisWInfinityPrime_finite
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_sourceGaloisWInfinityPrime_nonempty
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_sourceGaloisWZeroPrime_finite
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_sourceGaloisWZeroPrime_nonempty

set_option autoImplicit false
namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
open scoped BigOperators
noncomputable section
abbrev sourceGaloisWFibreDivisors_E (m : ℕ) := SourceGaloisClosureField m
noncomputable local instance sourceGaloisWFibreDivisors_closurePolynomialAlgebra (m : ℕ) :
    Algebra (Polynomial F256) (sourceGaloisWFibreDivisors_E m) :=
  ((algebraMap (RatFunc F256) (sourceGaloisWFibreDivisors_E m)).comp
    (algebraMap (Polynomial F256) (RatFunc F256))).toAlgebra
attribute [local instance] sourceGaloisWFibreDivisors_closurePolynomialAlgebra
noncomputable local instance sourceGaloisWFibreDivisors_closurePolynomialRatFuncScalarTower (m : ℕ) :
    IsScalarTower (Polynomial F256) (RatFunc F256) (sourceGaloisWFibreDivisors_E m) :=
  IsScalarTower.of_algebraMap_eq' rfl
attribute [local instance] sourceGaloisWFibreDivisors_closurePolynomialRatFuncScalarTower
noncomputable local instance sourceGaloisWFibreDivisors_closureRatFuncIsSeparable (m : ℕ) :
    Algebra.IsSeparable (RatFunc F256) (sourceGaloisWFibreDivisors_E m) :=
  IsGalois.to_isSeparable
attribute [local instance] sourceGaloisWFibreDivisors_closureRatFuncIsSeparable
noncomputable local instance sourceGaloisWFibreDivisors_sourceGaloisWZeroPrimeFintype (m : ℕ) :
    Fintype (SourceGaloisWZeroPrime m) :=
  Set.Finite.fintype (sourceGaloisWZeroPrime_finite m)
attribute [local instance] sourceGaloisWFibreDivisors_sourceGaloisWZeroPrimeFintype
noncomputable local instance sourceGaloisWFibreDivisors_sourceGaloisWInfinityPrimeFintype (m : ℕ) :
    Fintype (SourceGaloisWInfinityPrime m) :=
  Set.Finite.fintype (sourceGaloisWInfinityPrime_finite m)
attribute [local instance] sourceGaloisWFibreDivisors_sourceGaloisWInfinityPrimeFintype
local instance sourceGaloisWFibreDivisors_sourceGaloisWZeroPrimeNonempty (m : ℕ) :
    Nonempty (SourceGaloisWZeroPrime m) :=
  sourceGaloisWZeroPrime_nonempty m
attribute [local instance] sourceGaloisWFibreDivisors_sourceGaloisWZeroPrimeNonempty
local instance sourceGaloisWFibreDivisors_sourceGaloisWInfinityPrimeNonempty (m : ℕ) :
    Nonempty (SourceGaloisWInfinityPrime m) :=
  sourceGaloisWInfinityPrime_nonempty m
attribute [local instance] sourceGaloisWFibreDivisors_sourceGaloisWInfinityPrimeNonempty
noncomputable def sourceGaloisWZeroFibreDivisor (m : ℕ) :
    Divisor (GlobalPlace F256 (SourceGaloisClosureField m)) :=
  GlobalPlace.finitePlaceDivisor (sourceGaloisWZeroPlaceOfPrime m)
noncomputable def sourceGaloisWInfinityFibreDivisor (m : ℕ) :
    Divisor (GlobalPlace F256 (SourceGaloisClosureField m)) :=
  GlobalPlace.finitePlaceDivisor (sourceGaloisWInfinityPlaceOfPrime m)
end
end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth


