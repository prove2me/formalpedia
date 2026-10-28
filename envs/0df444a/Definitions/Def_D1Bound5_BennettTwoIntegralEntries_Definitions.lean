-- Prove2me | Definitions.Def_D1Bound5_BennettTwoIntegralEntries_Definitions
-- name    : D1Bound5_BennettTwoIntegralEntries_Definitions
-- status  : Definition
-- author  : @tp
-- created : 2026-10-23T23:21:58.047622+00:00
-- url     : https://prove2.me/theorems/346e2b96-6681-4509-9b78-233a9d1a13f9
-- title:
--   Bennett Two Integral Entries
-- statement:
--   The interpolation nodes for two fixed entries: H=ab, alpha=(0,b,a). The named objects in this bundle include `bennettTwoNodes`, `bennettTwoClearedEntry`.
-- source:
--   D1Bound5/BennettTwoIntegralEntries.lean, lines 11-12, SHA-256 07d63d84699ae294fc3d395f046972fa36aa179a18de306e5f612beceaaf5f1b; D1Bound5/BennettTwoIntegralEntries.lean, lines 64-69, SHA-256 07d63d84699ae294fc3d395f046972fa36aa179a18de306e5f612beceaaf5f1b. Project: https://github.com/tomislav-math/d1-bound5-lean

import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Combinatorics.Enumerative.Catalan.Basic
import Mathlib.RingTheory.Binomial
import Mathlib.RingTheory.PowerSeries.Binomial
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_BennettClearedResidues_Definitions

section
open Finset

namespace D1Bound5

variable {F : Type*} [Field F] [CharZero F]

/-- The interpolation nodes for two fixed entries: H=ab, alpha=(0,b,a). -/
def bennettTwoNodes (a b : F) : Fin 3 → F := ![0, b, a]















/-- The actual cleared two-anchor entry. The factor equals the manuscript's
(4 H^2 c Delta^2)^k after absorbing N^-k into the cleared polynomial G. -/
noncomputable def bennettTwoClearedEntry (a b c : F) (k : ℕ) (i j : Fin 3) : F :=
  (4 * a * b * (a - b) ^ 2) ^ k *
    (bennettClearedResidue Finset.univ (bennettTwoNodes a b) k (1 / 2 : F) i j).eval
      (a * b * c)











end D1Bound5
end


