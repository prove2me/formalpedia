-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialDifferentialWords_IsWeightedHomogeneousPairingLeft
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialDifferentialWords_IsWeightedHomogeneousPairingLeft
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T23:12:18.309894+00:00
-- url     : https://prove2.me/theorems/1e1422ac-08f4-4375-88e5-003f1a98fa3b
-- title:
--   Is Weighted Homogeneous Pairing Left
-- statement:
--   Definitions and structural lemmas for Is Weighted Homogeneous Pairing Left, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PolynomialDifferentialWords/IsWeightedHomogeneousPairingLeft.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialDifferentialWords_KappaRight
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
noncomputable section
namespace PI.OpWords.WeightedHomogeneousPolynomialDifferentialWords
variable {K : Type} [Field K] [CharZero K] {k : ℕ}
variable (K) in

def chiF (i0 : Fin k) : Fin k ⊕ Fin k → Pol K k :=
  Sum.elim (fun j => X (Sum.inl j)) (fun j => X (Sum.inl i0) * X (Sum.inr j))
variable (K) in

def tp (i0 : Fin k) : Pol K k := ∑ j ∈ Finset.univ.erase i0, X (Sum.inl j) * X (Sum.inr j)
variable (K) in

def psiF (i0 : Fin k) : Fin k ⊕ Fin k → Pol K k :=
  Sum.elim (fun j => X (Sum.inl j))
    (fun j => if j = i0 then - tp K i0 else X (Sum.inl i0) * X (Sum.inr j))
end PI.OpWords.WeightedHomogeneousPolynomialDifferentialWords


