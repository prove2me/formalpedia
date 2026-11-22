-- Prove2me | Definitions.Def_Formalism_LatticeRigidity_HeightMinimum_PowFinrankEqZeroOfTracePow
-- name    : Formalism_LatticeRigidity_HeightMinimum_PowFinrankEqZeroOfTracePow
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T19:42:24.908506+00:00
-- url     : https://prove2.me/theorems/c1b7aaf6-a16e-45ef-a50f-2024e0de0341
-- title:
--   Pow Finrank Eq Zero Of Trace Pow
-- statement:
--   Definitions and structural lemmas for Pow Finrank Eq Zero Of Trace Pow, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LatticeRigidity/HeightMinimum/PowFinrankEqZeroOfTracePow.lean

import Definitions.Def_Formalism_LatticeRigidity_StatementD
import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Formalism.SA.P
open Matrix Polynomial
open scoped ComplexOrder
section TracePow
variable {K V : Type*} [Field K] [IsAlgClosed K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]
theorem finite_eig (f : Module.End K V) : {μ | f.maxGenEigenspace μ ≠ ⊥}.Finite := by
  first
  | exact WellFoundedGT.finite_ne_bot_of_iSupIndep (Module.End.independent_maxGenEigenspace f)
  | exact WellFoundedGT.finite_ne_bot_of_iSupIndep (Module.End.iSupIndep_maxGenEigenspace f)
  | exact CompleteLattice.WellFoundedGT.finite_ne_bot_of_iSupIndep
      (Module.End.independent_maxGenEigenspace f)
  | exact CompleteLattice.WellFoundedGT.finite_ne_bot_of_independent
      (Module.End.independent_maxGenEigenspace f)
  | exact CompleteLattice.WellFounded.finite_ne_bot_of_independent wellFounded_gt
      (Module.End.independent_maxGenEigenspace f)
  | exact (Module.End.independent_maxGenEigenspace f).finite_ne_bot
  | exact (Module.End.iSupIndep_maxGenEigenspace f).finite_ne_bot
end TracePow
section Lattice
variable {R K : Type*} [CommRing R] [IsDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
end Lattice
end Formalism.SA.P


