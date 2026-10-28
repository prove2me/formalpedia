-- Prove2me | Definitions.Def_D1Bound5_PellLightFiniteAdapter_Definitions
-- name    : D1Bound5_PellLightFiniteAdapter_Definitions
-- status  : Definition
-- author  : @tp
-- created : 2026-10-24T00:32:47.720882+00:00
-- url     : https://prove2.me/theorems/8486379f-e5a6-4713-a2b7-b441157aa25d
-- title:
--   Pell Light Finite Adapter
-- statement:
--   Reuse the original finite certificate type, graph and completeness theorems after kernel checking the pure-Init arithmetic certificate. The named objects in this bundle include `pellFiniteCertificateOfLight`.
-- source:
--   D1Bound5/PellLightFiniteAdapter.lean, lines 6-17, SHA-256 96ff6ac14eb6a647b8e31a65059a8e9131235f8aa64792a5f99cfec0eae68b95. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.Group.Int.Units
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Algebra.Squarefree.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Int.GCD
import Mathlib.Data.Int.Sqrt
import Mathlib.Data.List.Defs
import Mathlib.Data.Rat.Lemmas
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.NumberTheory.DiophantineApproximation.Basic
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.RingTheory.Int.Basic
import Mathlib.Tactic
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_PellCFPrefixCheck_Definitions
import Definitions.Def_D1Bound5_PellFiniteCertificate_Definitions
import Definitions.Def_D1Bound5_PellLightCFBridge_Definitions
import Definitions.Def_D1Bound5_PellLightCF_Definitions
import Definitions.Def_D1Bound5_PellMatchingCheck_Definitions
import Definitions.Def_D1Bound5_UnitPairArithmeticModel_Definitions

section
namespace D1Bound5

/-- Reuse the original finite certificate type, graph and completeness
theorems after kernel checking the pure-Init arithmetic certificate. -/
def pellFiniteCertificateOfLight (d X a0 : ℤ) (N : ℕ)
    (graph : PellMatchingCertificate d)
    (hcheck : pellLightFiniteCheck d a0 X N graph.magnitudes = true) :
    PellFiniteCertificate d X where
  a0 := a0
  lastIndex := N
  graph := graph
  prefix_checked := (pellLightFiniteCheck_sound d a0 X N graph.magnitudes hcheck).1
  stopping := (pellLightFiniteCheck_sound d a0 X N graph.magnitudes hcheck).2.1
  magnitudes_eq := (pellLightFiniteCheck_sound d a0 X N graph.magnitudes hcheck).2.2

end D1Bound5
end


