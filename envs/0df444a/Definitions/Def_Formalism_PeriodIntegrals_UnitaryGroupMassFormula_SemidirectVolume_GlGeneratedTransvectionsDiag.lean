-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_GlGeneratedTransvectionsDiag
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_GlGeneratedTransvectionsDiag
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T00:13:03.700104+00:00
-- url     : https://prove2.me/theorems/1ae13ee6-03cf-4dee-b8bc-13b8020484c0
-- title:
--   Gl Generated Transvections Diag
-- statement:
--   Definitions and structural lemmas for Gl Generated Transvections Diag, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SemidirectVolume/GlGeneratedTransvectionsDiag.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_CjDefs
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PI.VolSemiDirect.W.Cj
open Matrix
def genSet (A : Type) [CommRing A] (k : ℕ) : Set (GL (Fin k) A) :=
  {g | ∃ i j c, i ≠ j ∧ (g : Matrix (Fin k) (Fin k) A) = transvection i j c} ∪
    {g | ∃ d : Fin k → A, (g : Matrix (Fin k) (Fin k) A) = diagonal d}
section
variable {A : Type} [CommRing A] {k : ℕ}
def InG (M : Matrix (Fin k) (Fin k) A) : Prop :=
  ∃ g ∈ Subgroup.closure (genSet A k), (g : Matrix (Fin k) (Fin k) A) = M
def Red (m : ℕ) (M : Matrix (Fin k) (Fin k) A) : Prop :=
  ∀ i j : Fin k, (i.val < m ∨ j.val < m) → M i j = (1 : Matrix (Fin k) (Fin k) A) i j
end
end PI.VolSemiDirect.W.Cj


