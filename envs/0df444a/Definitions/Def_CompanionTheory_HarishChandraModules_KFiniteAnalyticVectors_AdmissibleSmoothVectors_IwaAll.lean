-- Prove2me | Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_IwaAll
-- name    : CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_IwaAll
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T06:06:52.948045+00:00
-- url     : https://prove2.me/theorems/eaf5cbe1-7eb0-479e-82ed-9b6e92a30e54
-- title:
--   Iwa All
-- statement:
--   Definitions and structural lemmas for Iwa All, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/KFiniteAnalyticVectors/AdmissibleSmoothVectors/IwaAll.lean

import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_MapStdPoly
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_IwaCore
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace CompanionTheory.D.gk.admitted
open Matrix PI.UpqRep
namespace CholeskyDecomposition
variable {n : ℕ}
def pr (ε : Fin n → Bool) (i : Fin n) : Fin n := if ε i.rev = ε i then i else i.rev
def ht (ε : Fin n → Bool) (i : Fin n) : ℤ := if ε i.rev = ε i then 0 else 2 * (i : ℤ) + 1 - n
def sg (ε : Fin n → Bool) (i : Fin n) : ℂ := if ε i then 1 else -1
def wt (ε : Fin n → Bool) (i : Fin n) : ℂ := if ε i.rev = ε i then sg ε i else 1
end CholeskyDecomposition
end CompanionTheory.D.gk.admitted


