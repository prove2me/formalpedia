-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_KoszulExactness_Ii
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_KoszulExactness_Ii
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T10:00:18.157803+00:00
-- url     : https://prove2.me/theorems/aa6fef9e-561b-4806-9ca2-5f567ff838ef
-- title:
--   Ii
-- statement:
--   Definitions and structural lemmas for Ii, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/KoszulExactness/Ii.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_KoszulExact
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
universe u
namespace PI.KoszulExact
def eb (R : Type u) [CommRing R] {D : ℕ} (k : Fin D) : ExteriorAlgebra R (Fin D → R) :=
  ExteriorAlgebra.ι R (Pi.single k 1)
def Li (R : Type u) [CommRing R] (D : ℕ) (i : ℕ) : Submodule R (ExteriorAlgebra R (Fin D → R)) :=
  Submodule.span R (eb R '' {k : Fin D | (k : ℕ) < i})
def Ii {R : Type u} [CommRing R] {D : ℕ} (s : Fin D → R) (i : ℕ) : Ideal R :=
  Ideal.span (s '' {k : Fin D | (k : ℕ) < i})
end PI.KoszulExact


