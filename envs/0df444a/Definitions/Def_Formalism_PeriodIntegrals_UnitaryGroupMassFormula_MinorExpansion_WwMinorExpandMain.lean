-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MinorExpansion_WwMinorExpandMain
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MinorExpansion_WwMinorExpandMain
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T02:45:32.16806+00:00
-- url     : https://prove2.me/theorems/d5ef9bff-6a43-451d-bb60-5303dfb38fe5
-- title:
--   Ww Minor Expand Main
-- statement:
--   Definitions and structural lemmas for Ww Minor Expand Main, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MinorExpansion/WwMinorExpandMain.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_WwMinorExpand
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MonomialFrameSpan_DetSubmatrixFun
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
namespace PI.WwMinorExpandWork
open PI.WwMinorExpand
variable {Lt : Type} [Fintype Lt] [DecidableEq Lt] (N0 N1 : ℕ)
def minX (s : Lt) (p : ℕ) (J : Fin p ↪o Fin N0) : MvPolynomial (Lt × ℕ × Fin N0) ℤ :=
  Matrix.det (Matrix.of fun i k : Fin p =>
    (MvPolynomial.X (s, (i : ℕ), J k) : MvPolynomial (Lt × ℕ × Fin N0) ℤ))
def RepM (s : Lt) (p : ℕ) (x : MvPolynomial (KM.XZ Lt N0 N1) ℤ) : Prop :=
  ∃ d : (Fin p ↪o Fin N0) → MvPolynomial (Lt × Fin N0 × Fin N1) ℤ,
    x = ∑ J, MvPolynomial.rename Sum.inl (minX N0 s p J) * MvPolynomial.rename Sum.inr (d J)
end PI.WwMinorExpandWork


