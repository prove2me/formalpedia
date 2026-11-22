-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MatrixCoefficientBound_ProdFormula
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MatrixCoefficientBound_ProdFormula
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T20:52:11.774142+00:00
-- url     : https://prove2.me/theorems/51e87139-8307-41a6-ac25-9885e5478a79
-- title:
--   Prod Formula
-- statement:
--   Definitions and structural lemmas for Prod Formula, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MatrixCoefficientBound/ProdFormula.lean

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GGMirabolic
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MatrixCoefficientBound_PermRepApply
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
open Classical
namespace PI.GGMatBoundW
open Formalism.L2.SG.GGMirabolic
section Prod
variable {ι : Type} [Fintype ι] {Fq : ι → Type} [∀ v, Field (Fq v)] [∀ v, Fintype (Fq v)] {k : ℕ}
def beta (ψ : ∀ v, AddChar (Fq v) ℂ) (s : Finset ι) (x : ∀ v, GL (Fin k) (Fq v)) : ℂ :=
  if ∀ w, w ∉ s → x w = 1 then ∏ v ∈ s, gam (ψ v) (x v) else 0
variable {V : Type} [AddCommGroup V] [Module ℂ V]
end Prod
end PI.GGMatBoundW


