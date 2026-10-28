-- Prove2me | Definitions.Def_D1Bound5_FiniteN3Height_Definitions
-- name    : D1Bound5_FiniteN3Height_Definitions
-- status  : Definition
-- author  : @tp
-- created : 2026-10-23T22:26:42.021799+00:00
-- url     : https://prove2.me/theorems/0b70fb13-bfa9-4ff1-a639-ac6726b9c3b1
-- title:
--   Finite N3Height
-- statement:
--   Definitions for finite n3height in the argument bounding Diophantine D(1) sets in imaginary quadratic integer rings. The named objects in this bundle include `finiteN3Coeff0`, `finiteN3Coeff1`, `finiteN3Coeff2`, `finiteN3Coeff3`.
-- source:
--   D1Bound5/FiniteN3Height.lean, lines 8-11, SHA-256 f481f700219409141bd10895fbdbd58481a503388f7da4c50027895a33e66039; D1Bound5/FiniteN3Height.lean, lines 13-16, SHA-256 f481f700219409141bd10895fbdbd58481a503388f7da4c50027895a33e66039; D1Bound5/FiniteN3Height.lean, lines 18-21, SHA-256 f481f700219409141bd10895fbdbd58481a503388f7da4c50027895a33e66039; D1Bound5/FiniteN3Height.lean, lines 23-26, SHA-256 f481f700219409141bd10895fbdbd58481a503388f7da4c50027895a33e66039. Project: https://github.com/tomislav-math/d1-bound5-lean

import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

section
namespace D1Bound5

def finiteN3Coeff0 : Fin 3 → Fin 2 → Fin 5 → ℤ :=
  ![![![0,0,-126,36,-6], ![6,-36,126,0,0]],
    ![![0,-105,-63,9,-1], ![-2,36,126,0,0]],
    ![![0,0,126,36,-2], ![-1,9,-63,-105,0]]]

def finiteN3Coeff1 : Fin 3 → Fin 2 → Fin 6 → ℤ :=
  ![![![0,0,0,-630,444,-102], ![102,-444,630,0,0,0]],
    ![![0,0,-756,378,-120,18], ![22,-172,630,0,0,0]],
    ![![0,0,0,630,-172,22], ![18,-120,378,-756,0,0]]]

def finiteN3Coeff2 : Fin 3 → Fin 2 → Fin 7 → ℤ :=
  ![![![0,0,0,0,-952,920,-256], ![256,-920,952,0,0,0,0]],
    ![![0,0,0,-1512,1680,-792,144], ![120,-592,952,0,0,0,0]],
    ![![0,0,0,0,952,-592,120], ![144,-792,1680,-1512,0,0,0]]]

def finiteN3Coeff3 : Fin 3 → Fin 2 → Fin 8 → ℤ :=
  ![![![0,0,0,0,0,-448,512,-160], ![160,-512,448,0,0,0,0,0]],
    ![![0,0,0,0,-896,1344,-768,160], ![96,-384,448,0,0,0,0,0]],
    ![![0,0,0,0,0,448,-384,96], ![160,-768,1344,-896,0,0,0,0]]]














end D1Bound5
end


