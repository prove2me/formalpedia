-- Prove2me | Definitions.Def_D1Bound5_FiniteA5Coefficients_Definitions
-- name    : D1Bound5_FiniteA5Coefficients_Definitions
-- status  : Definition
-- author  : @tp
-- created : 2026-10-23T22:29:02.109999+00:00
-- url     : https://prove2.me/theorems/b9db8840-aefb-4fdb-9217-35afa3332c6d
-- title:
--   Finite A5Coefficients
-- statement:
--   Definitions for finite a5coefficients in the argument bounding Diophantine D(1) sets in imaginary quadratic integer rings. The named objects in this bundle include `finiteA5Coeff0`, `finiteA5Coeff1`, `finiteA5Coeff2`, `finiteA5Coeff3`, `finiteA5Coeff4`, `finiteA5Coeff5`, `finiteA5RootCoeff`, `finiteA5CoefficientSums`.
-- source:
--   D1Bound5/FiniteA5Coefficients.lean, lines 6-7, SHA-256 013a8fb6a9d65f4705b504b84ef5b5f353d0efaf35648d2c9faeff0d1acac74d; D1Bound5/FiniteA5Coefficients.lean, lines 9-10, SHA-256 013a8fb6a9d65f4705b504b84ef5b5f353d0efaf35648d2c9faeff0d1acac74d; D1Bound5/FiniteA5Coefficients.lean, lines 12-13, SHA-256 013a8fb6a9d65f4705b504b84ef5b5f353d0efaf35648d2c9faeff0d1acac74d; D1Bound5/FiniteA5Coefficients.lean, lines 15-16, SHA-256 013a8fb6a9d65f4705b504b84ef5b5f353d0efaf35648d2c9faeff0d1acac74d; D1Bound5/FiniteA5Coefficients.lean, lines 18-19, SHA-256 013a8fb6a9d65f4705b504b84ef5b5f353d0efaf35648d2c9faeff0d1acac74d; D1Bound5/FiniteA5Coefficients.lean, lines 21-22, SHA-256 013a8fb6a9d65f4705b504b84ef5b5f353d0efaf35648d2c9faeff0d1acac74d; D1Bound5/FiniteA5Coefficients.lean, lines 24-25, SHA-256 013a8fb6a9d65f4705b504b84ef5b5f353d0efaf35648d2c9faeff0d1acac74d; D1Bound5/FiniteA5Coefficients.lean, lines 100-101, SHA-256 013a8fb6a9d65f4705b504b84ef5b5f353d0efaf35648d2c9faeff0d1acac74d. Project: https://github.com/tomislav-math/d1-bound5-lean

import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_FiniteHomogeneousTwo_Definitions

section
namespace D1Bound5

def finiteA5Coeff0 : Fin 3 → Fin 2 → Fin 8 → ℤ :=
  ![![![0,0,0,-12870,-5720,780,-120,10],![-10,120,-780,5720,12870,0,0,0]],![![0,0,-9009,-19305,-4290,390,-45,3],![6,-120,2340,17160,12870,0,0,0]],![![0,0,0,12870,17160,2340,-120,6],![3,-45,390,-4290,-19305,-9009,0,0]]]

def finiteA5Coeff1 : Fin 3 → Fin 2 → Fin 9 → ℤ :=
  ![![![0,0,0,0,-127270,51480,-17220,3800,-390],![390,-3800,17220,-51480,127270,0,0,0,0]],![![0,0,0,-115830,-57200,14300,-3000,490,-40],![-58,808,-6780,40040,127270,0,0,0,0]],![![0,0,0,0,127270,40040,-6780,808,-58],![-40,490,-3000,14300,-57200,-115830,0,0,0]]]

def finiteA5Coeff2 : Fin 3 → Fin 2 → Fin 10 → ℤ :=
  ![![![0,0,0,0,0,-457600,453200,-231120,63920,-7600],![7600,-63920,231120,-453200,457600,0,0,0,0,0]],![![0,0,0,0,-514800,286000,-127600,41520,-8480,800],![896,-9824,51648,-177760,457600,0,0,0,0,0]],![![0,0,0,0,0,457600,-177760,51648,-9824,896],![800,-8480,41520,-127600,286000,-514800,0,0,0,0]]]

def finiteA5Coeff3 : Fin 3 → Fin 2 → Fin 11 → ℤ :=
  ![![![0,0,0,0,0,0,-765600,1085920,-693120,223200,-29600],![29600,-223200,693120,-1085920,765600,0,0,0,0,0,0]],![![0,0,0,0,0,-1029600,1320000,-913440,382080,-91200,9600],![8640,-79872,318816,-690624,765600,0,0,0,0,0,0]],![![0,0,0,0,0,0,765600,-690624,318816,-79872,8640],![9600,-91200,382080,-913440,1320000,-1029600,0,0,0,0,0]]]

def finiteA5Coeff4 : Fin 3 → Fin 2 → Fin 12 → ℤ :=
  ![![![0,0,0,0,0,0,0,-605440,1056000,-779520,279680,-40320],![40320,-279680,779520,-1056000,605440,0,0,0,0,0,0,0]],![![0,0,0,0,0,0,-950400,1724800,-1492480,729600,-195200,22400],![16640,-135680,457728,-782848,605440,0,0,0,0,0,0,0]],![![0,0,0,0,0,0,0,605440,-782848,457728,-135680,16640],![22400,-195200,729600,-1492480,1724800,-950400,0,0,0,0,0,0]]]

def finiteA5Coeff5 : Fin 3 → Fin 2 → Fin 13 → ℤ :=
  ![![![0,0,0,0,0,0,0,0,-183040,366080,-299520,116480,-17920],![17920,-116480,299520,-366080,183040,0,0,0,0,0,0,0,0]],![![0,0,0,0,0,0,0,-329472,732160,-732160,399360,-116480,14336],![8960,-66560,199680,-292864,183040,0,0,0,0,0,0,0,0]],![![0,0,0,0,0,0,0,0,183040,-292864,199680,-66560,8960],![14336,-116480,399360,-732160,732160,-329472,0,0,0,0,0,0,0]]]

def finiteA5RootCoeff {R : Type*} [CommRing R] (x y : R) (i : Fin 3) (j : Fin 2) : Fin 6 → R :=
  ![finiteHomogeneousTwo 7 (finiteA5Coeff0 i j) x y,finiteHomogeneousTwo 8 (finiteA5Coeff1 i j) x y,finiteHomogeneousTwo 9 (finiteA5Coeff2 i j) x y,finiteHomogeneousTwo 10 (finiteA5Coeff3 i j) x y,finiteHomogeneousTwo 11 (finiteA5Coeff4 i j) x y,finiteHomogeneousTwo 12 (finiteA5Coeff5 i j) x y]


















def finiteA5CoefficientSums : Fin 3 → Fin 6 → ℤ :=
  ![![39000,400320,2426880,5594880,5521920,1966080],![65538,365816,1676928,5609472,7113216,3075072],![65538,365816,1676928,5609472,7113216,3075072]]













end D1Bound5
end


