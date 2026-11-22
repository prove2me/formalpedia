-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GaugeLatticeShifts_RCocompactPfStmt
-- name    : Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GaugeLatticeShifts_RCocompactPfStmt
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:27:41.340283+00:00
-- url     : https://prove2.me/theorems/3aae3faf-512d-4e1a-a1cb-e738a586d57f
-- title:
--   RCocompact Pf Stmt
-- statement:
--   Definitions and structural lemmas for RCocompact Pf Stmt, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/ClosedLocalOrbits/GaugeLatticeShifts/RCocompactPfStmt.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Formalism.L2.SG.Pf.RCoc
def KerBaseChange : Prop :=
  ∀ (K L : Type) [Field K] [Field L] (f : K →+* L) (m p : Type) [Fintype m] [Fintype p] [DecidableEq p]
    (A : Matrix m p K), ∃ P : Matrix p p K, A * P = 0 ∧
      ∀ z : p → L, (A.map f).mulVec z = 0 → (P.map f).mulVec z = z
end Formalism.L2.SG.Pf.RCoc


