-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_ShapeFromFacts
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_ShapeFromFacts
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T05:07:08.557545+00:00
-- url     : https://prove2.me/theorems/78d8c794-6477-40ef-be3e-223c1e1c2041
-- title:
--   Shape From Facts
-- statement:
--   Definitions and structural lemmas for Shape From Facts, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockJointMultiplicity/ShapeFromFacts.lean

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_GlobalTheory
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix FockH1Action
namespace PI.WFJM.Shape
open PI.FJM
section Gen
variable {n : ℕ}
def αP (f : Fin n → ℚ) : Fin (nP f) → ℕ := fun i => ⌊f (Fin.castLE (nP_le_nW f) i)⌋₊
def αN (f : Fin n → ℚ) : Fin (nN f) → ℕ := fun i => ⌊-f (Fin.rev (Fin.castLE (nN_le f) i))⌋₊
def lpos {m : ℕ} (α : Fin m → ℕ) : List ℤ := List.ofFn fun i => (α i : ℤ)
def lneg {m : ℕ} (α : Fin m → ℕ) : List ℤ := (List.ofFn fun i => -(α i : ℤ)).reverse
end Gen
end PI.WFJM.Shape
namespace PI.FJM
open PI.WFJM.Shape
end PI.FJM


