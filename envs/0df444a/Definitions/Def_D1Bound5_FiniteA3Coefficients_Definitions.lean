-- Prove2me | Definitions.Def_D1Bound5_FiniteA3Coefficients_Definitions
-- name    : D1Bound5_FiniteA3Coefficients_Definitions
-- status  : Definition
-- author  : @tp
-- created : 2026-10-23T23:09:23.586372+00:00
-- url     : https://prove2.me/theorems/ee44b06e-0816-400b-a034-6222cba2746d
-- title:
--   Finite A3Coefficients
-- statement:
--   Definitions for finite a3coefficients in the argument bounding Diophantine D(1) sets in imaginary quadratic integer rings. The named objects in this bundle include `finiteA3Coeff0`, `finiteA3Coeff1`, `finiteA3Coeff2`, `finiteA3Coeff3`, `finiteA3RootCoeff`, `finiteA3CoefficientSums`.
-- source:
--   D1Bound5/FiniteA3Coefficients.lean, lines 6-7, SHA-256 7440cce2f6cdd37d87275749638987bd7427e186ac1d7f24fa8ba39b953689c0; D1Bound5/FiniteA3Coefficients.lean, lines 9-10, SHA-256 7440cce2f6cdd37d87275749638987bd7427e186ac1d7f24fa8ba39b953689c0; D1Bound5/FiniteA3Coefficients.lean, lines 12-13, SHA-256 7440cce2f6cdd37d87275749638987bd7427e186ac1d7f24fa8ba39b953689c0; D1Bound5/FiniteA3Coefficients.lean, lines 15-16, SHA-256 7440cce2f6cdd37d87275749638987bd7427e186ac1d7f24fa8ba39b953689c0; D1Bound5/FiniteA3Coefficients.lean, lines 18-19, SHA-256 7440cce2f6cdd37d87275749638987bd7427e186ac1d7f24fa8ba39b953689c0; D1Bound5/FiniteA3Coefficients.lean, lines 31-32, SHA-256 7440cce2f6cdd37d87275749638987bd7427e186ac1d7f24fa8ba39b953689c0. Project: https://github.com/tomislav-math/d1-bound5-lean

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

def finiteA3Coeff0 : Fin 3 → Fin 2 → Fin 4 → ℤ :=
  ![![![0,-70,-28,2],![-2,28,70,0]],![![-35,-105,-21,1],![6,84,70,0]],![![0,70,84,6],![1,-21,-105,-35]]]

def finiteA3Coeff1 : Fin 3 → Fin 2 → Fin 5 → ℤ :=
  ![![![0,0,-406,140,-22],![22,-140,406,0,0]],![![0,-350,-168,42,-4],![-10,84,406,0,0]],![![0,0,406,84,-10],![-4,42,-168,-350,0]]]

def finiteA3Coeff2 : Fin 3 → Fin 2 → Fin 6 → ℤ :=
  ![![![0,0,0,-672,504,-120],![120,-504,672,0,0,0]],![![0,0,-840,504,-168,24],![32,-224,672,0,0,0]],![![0,0,0,672,-224,32],![24,-168,504,-840,0,0]]]

def finiteA3Coeff3 : Fin 3 → Fin 2 → Fin 7 → ℤ :=
  ![![![0,0,0,0,-336,336,-96],![96,-336,336,0,0,0,0]],![![0,0,0,-560,672,-336,64],![48,-224,336,0,0,0,0]],![![0,0,0,0,336,-224,48],![64,-336,672,-560,0,0,0]]]

def finiteA3RootCoeff {R : Type*} [CommRing R] (x y : R) (i : Fin 3) (j : Fin 2) : Fin 4 → R :=
  ![finiteHomogeneousTwo 3 (finiteA3Coeff0 i j) x y,finiteHomogeneousTwo 4 (finiteA3Coeff1 i j) x y,finiteHomogeneousTwo 5 (finiteA3Coeff2 i j) x y,finiteHomogeneousTwo 6 (finiteA3Coeff3 i j) x y]



def finiteA3CoefficientSums : Fin 3 → Fin 4 → ℤ :=
  ![![200,1136,2592,1536],![322,1064,2464,2240],![322,1064,2464,2240]]









end D1Bound5
end


