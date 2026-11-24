-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GreenLabelCharpoly_IrreducibleCharpolyInv
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GreenLabelCharpoly_IrreducibleCharpolyInv
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:16:52.050704+00:00
-- url     : https://prove2.me/theorems/839214ac-4d48-473a-ac72-9316cc791cb2
-- title:
--   Irreducible Charpoly Inv
-- statement:
--   Definitions and structural lemmas for Irreducible Charpoly Inv, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GreenLabelCharpoly/IrreducibleCharpolyInv.lean

import Mathlib
import Definitions.Def_Formalism_PadicSubsetSums_CentralIdempotents_GaloisConjCentralIdempotent
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GreenLabelCharpoly_RootPowCard
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial CategoryTheory Formalism.IrreducibleCountingLemmas.TYPES
noncomputable section
namespace PI.GreenLabelMapW
variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
def greenLab (Cv : LabelConv K) (d : ℕ) (τ : FDRep ℂ (GL (Fin d) K)) : K[X] :=
  Classical.epsilon (fun P => HasCuspLabel Cv τ P)
end PI.GreenLabelMapW


