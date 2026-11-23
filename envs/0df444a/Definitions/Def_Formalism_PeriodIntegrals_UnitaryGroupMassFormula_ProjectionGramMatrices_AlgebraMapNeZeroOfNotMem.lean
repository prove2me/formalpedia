-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProjectionGramMatrices_AlgebraMapNeZeroOfNotMem
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProjectionGramMatrices_AlgebraMapNeZeroOfNotMem
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T04:53:49.196792+00:00
-- url     : https://prove2.me/theorems/297a3e7f-bf79-45e0-bd77-60b1dc143a55
-- title:
--   Algebra Map Ne Zero Of Not Mem
-- statement:
--   Definitions and structural lemmas for Algebra Map Ne Zero Of Not Mem, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ProjectionGramMatrices/AlgebraMapNeZeroOfNotMem.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_DivisionRowsRationalLattice
import Definitions.Def_Formalism_PeriodIntegrals_IdxCalc
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_IndexBasic
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PI.Dv.ProjGramW
open NumberField IsDedekindDomain Formalism.BasicNotions
def IdxDet : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (V : Type) [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
    [IsScalarTower (𝓞 K) K V] (w : HeightOneSpectrum (𝓞 K)) (d : ℕ) (b : Fin d → V),
    LinearIndependent K b → ∀ C : Matrix (Fin d) (Fin d) K, C.det ≠ 0 →
    idxAt w (Submodule.span (𝓞 K) (Set.range b))
      (Submodule.span (𝓞 K) (Set.range fun j => ∑ i, C i j • b i)) = vAdd w C.det
section Gen
variable {K : Type} [Field K] [NumberField K] {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]
end Gen
section Herm
variable {K : Type} [Field K] [NumberField K] [StarRing K]
end Herm
end PI.Dv.ProjGramW


