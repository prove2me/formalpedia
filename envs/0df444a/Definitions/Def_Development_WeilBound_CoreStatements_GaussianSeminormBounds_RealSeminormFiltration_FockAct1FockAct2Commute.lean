-- Prove2me | Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_FockAct1FockAct2Commute
-- name    : Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_FockAct1FockAct2Commute
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:20:52.35168+00:00
-- url     : https://prove2.me/theorems/ed24d710-c9a4-4502-8e75-d0f65534bc23
-- title:
--   Fock Act1 Fock Act2 Commute
-- statement:
--   Definitions and structural lemmas for Fock Act1 Fock Act2 Commute, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/GaussianSeminormBounds/RealSeminormFiltration/FockAct1FockAct2Commute.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_JointBlockShapes_JointShape
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial FockH1Action
namespace PositivityTheory.KReal
section Abstract
variable {ι E : Type*} [Fintype ι] [DecidableEq ι] [Ring E] [Algebra ℂ E]
def quadT (R L : ι → E) (A : Matrix ι ι ℂ) : E := ∑ i, ∑ j, A i j • (R i * L j)
def quartT (R L : ι → E) (A B : Matrix ι ι ℂ) : E :=
  ∑ i, ∑ j, ∑ k, ∑ l, (A i j * B k l) • (R i * R k * (L j * L l))
end Abstract
section Fock
variable {σ : Type*} [DecidableEq σ]
end Fock
section Lines
variable {p q r s : ℕ}
end Lines
end PositivityTheory.KReal
end


