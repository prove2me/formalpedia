-- Prove2me | Definitions.Def_D1Bound5_FinitePHeight_Definitions
-- name    : D1Bound5_FinitePHeight_Definitions
-- status  : Definition
-- author  : @tp
-- created : 2026-10-23T23:16:54.759545+00:00
-- url     : https://prove2.me/theorems/437f73de-f8bd-4b7e-a41e-efbb4315fec0
-- title:
--   Finite PHeight
-- statement:
--   Integer coefficient and the three anchor exponents. The named objects in this bundle include `FinitePTerm`, `finitePTermValue`, `finitePRootTerms`, `finitePRootCoeff`, `finitePRootColumn`.
-- source:
--   D1Bound5/FinitePHeight.lean, lines 14-15, SHA-256 314dc2ce401e7d406d8613d27c9a6ab48d94b1783ab8ee80b2eda5b7bee22fae; D1Bound5/FinitePHeight.lean, lines 17-19, SHA-256 314dc2ce401e7d406d8613d27c9a6ab48d94b1783ab8ee80b2eda5b7bee22fae; D1Bound5/FinitePHeight.lean, lines 21-23, SHA-256 314dc2ce401e7d406d8613d27c9a6ab48d94b1783ab8ee80b2eda5b7bee22fae; D1Bound5/FinitePHeight.lean, lines 25-27, SHA-256 314dc2ce401e7d406d8613d27c9a6ab48d94b1783ab8ee80b2eda5b7bee22fae; D1Bound5/FinitePHeight.lean, lines 29-31, SHA-256 314dc2ce401e7d406d8613d27c9a6ab48d94b1783ab8ee80b2eda5b7bee22fae. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Definitions.Def_D1Bound5_FinitePMatrix_Definitions

section
open Finset

namespace D1Bound5

attribute [local simp] Matrix.cons_val_two Matrix.cons_val_three

/-- Integer coefficient and the three anchor exponents. -/
abbrev FinitePTerm := ℤ × ℕ × ℕ × ℕ

def finitePTermValue {R : Type*} [CommRing R]
    (t : FinitePTerm) (a b s : R) : R :=
  (t.1 : R)*a^t.2.1*b^t.2.2.1*s^t.2.2.2

/-- Terms are obtained after the H and V row cancellations. -/
def finitePRootTerms : Fin 4 → Fin 3 → Fin 3 → Fin 3 → FinitePTerm :=
  ![![![![(7, 2, 0, 0), (-35, 1, 1, 0), (0, 0, 0, 0)], ![(35, 1, 1, 0), (-7, 0, 2, 0), (0, 0, 0, 0)], ![(0, 0, 0, 0), (0, 0, 0, 0), (0, 0, 0, 0)]], ![![(64, 3, 0, 0), (-140, 2, 1, 0), (0, 0, 0, 0)], ![(140, 1, 2, 0), (-64, 0, 3, 0), (0, 0, 0, 0)], ![(0, 0, 0, 0), (0, 0, 0, 0), (0, 0, 0, 0)]], ![![(72, 4, 0, 0), (-120, 3, 1, 0), (0, 0, 0, 0)], ![(120, 1, 3, 0), (-72, 0, 4, 0), (0, 0, 0, 0)], ![(0, 0, 0, 0), (0, 0, 0, 0), (0, 0, 0, 0)]]], ![![![(-35, 1, 1, 0), (35, 1, 0, 1), (0, 0, 0, 0)], ![(35, 1, 1, 0), (-35, 0, 1, 1), (0, 0, 0, 0)], ![(35, 0, 1, 1), (-35, 1, 0, 1), (0, 0, 0, 0)]], ![![(-140, 2, 1, 0), (140, 2, 0, 1), (0, 0, 0, 0)], ![(140, 1, 2, 0), (-140, 0, 2, 1), (0, 0, 0, 0)], ![(140, 0, 1, 2), (-140, 1, 0, 2), (0, 0, 0, 0)]], ![![(-120, 3, 1, 0), (120, 3, 0, 1), (0, 0, 0, 0)], ![(120, 1, 3, 0), (-120, 0, 3, 1), (0, 0, 0, 0)], ![(120, 0, 1, 3), (-120, 1, 0, 3), (0, 0, 0, 0)]]], ![![![(-15, 3, 0, 0), (56, 2, 1, 0), (-105, 1, 2, 0)], ![(70, 1, 2, 0), (-6, 0, 3, 0), (0, 0, 0, 0)], ![(0, 0, 0, 0), (0, 0, 0, 0), (0, 0, 0, 0)]], ![![(-180, 4, 0, 0), (512, 3, 1, 0), (-420, 2, 2, 0)], ![(100, 1, 3, 0), (-12, 0, 4, 0), (0, 0, 0, 0)], ![(0, 0, 0, 0), (0, 0, 0, 0), (0, 0, 0, 0)]], ![![(-240, 5, 0, 0), (576, 4, 1, 0), (-360, 3, 2, 0)], ![(24, 0, 5, 0), (0, 0, 0, 0), (0, 0, 0, 0)], ![(0, 0, 0, 0), (0, 0, 0, 0), (0, 0, 0, 0)]]], ![![![(-15, 3, 0, 0), (56, 2, 0, 1), (-105, 1, 0, 2)], ![(15, 0, 3, 0), (-56, 0, 2, 1), (105, 0, 1, 2)], ![(70, 1, 0, 2), (-70, 0, 1, 2), (0, 0, 0, 0)]], ![![(-180, 4, 0, 0), (512, 3, 0, 1), (-420, 2, 0, 2)], ![(180, 0, 4, 0), (-512, 0, 3, 1), (420, 0, 2, 2)], ![(100, 1, 0, 3), (-100, 0, 1, 3), (0, 0, 0, 0)]], ![![(-240, 5, 0, 0), (576, 4, 0, 1), (-360, 3, 0, 2)], ![(240, 0, 5, 0), (-576, 0, 4, 1), (360, 0, 3, 2)], ![(0, 0, 0, 0), (0, 0, 0, 0), (0, 0, 0, 0)]]]]

def finitePRootCoeff {R : Type*} [CommRing R]
    (a b s : R) (i : Fin 4) (l j : Fin 3) : R :=
  ∑ t, finitePTermValue (finitePRootTerms i l j t) a b s

def finitePRootColumn {R : Type*} [CommRing R]
    (a b s c : R) (i : Fin 4) (j : Fin 3) : R :=
  finitePDividedMatrix a b s c i j.succ



















end D1Bound5
end


