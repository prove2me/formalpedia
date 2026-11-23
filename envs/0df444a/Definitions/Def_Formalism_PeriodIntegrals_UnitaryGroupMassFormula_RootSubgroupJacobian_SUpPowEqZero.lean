-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_RootSubgroupJacobian_SUpPowEqZero
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_RootSubgroupJacobian_SUpPowEqZero
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T00:55:14.857497+00:00
-- url     : https://prove2.me/theorems/899e72d8-ab11-4196-9d30-50362c457fa7
-- title:
--   SUp Pow Eq Zero
-- statement:
--   Definitions and structural lemmas for SUp Pow Eq Zero, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/RootSubgroupJacobian/SUpPowEqZero.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_RootSubgroupBasics_TriShear
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix
noncomputable section
namespace PI.AmpRootJacW
variable {n : ℕ}
def SUp (V : Matrix (Fin n) (Fin n) ℂ) : Prop := ∀ i j : Fin n, j.val ≤ i.val → V i j = 0
def gInv (V : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  ∑ m ∈ Finset.range (n + 2), (-V) ^ m
section Pat
variable (S : Finset (Fin n × Fin n))
def vM (v : S → ℂ) : Matrix (Fin n) (Fin n) ℂ := fun i j => if h : (i, j) ∈ S then v ⟨(i, j), h⟩ else 0
def invC (v : S → ℂ) : S → ℂ := fun q => gInv (vM S v) q.1.1 q.1.2
def rk (q : S) : ℕ := q.1.2.val - q.1.1.val
def hSh (q : S) (v : S → ℂ) : ℂ :=
  -(∑ m ∈ Finset.range n, ((-vM S v) ^ (m + 1 + 1)) q.1.1 q.1.2)
end Pat
end PI.AmpRootJacW


