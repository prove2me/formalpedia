-- Prove2me | Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_CntSym
-- name    : Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_CntSym
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:41:43.72715+00:00
-- url     : https://prove2.me/theorems/eae730ee-d2c3-449b-a5f9-8b59d1894f1a
-- title:
--   Cnt Sym
-- statement:
--   Definitions and structural lemmas for Cnt Sym, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/CntSym.lean

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_ExtendedColumns
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
namespace Formalism.InvariantFactorPaths.ColumnFamilies
open Formalism.InvariantFactorPaths.GelfandTsetlinBases (dGT)
def qk_symEquiv (n b : ℕ) : SymIdx n b ≃ {P : Fin n → ℕ // ∑ i, P i = b} where
  toFun α := ⟨fun a => (α.1 a : ℕ), α.2⟩
  invFun P := ⟨fun a => ⟨P.1 a, by
    have := single_le_sum (f := P.1) (fun i _ => Nat.zero_le _) (mem_univ a)
    have h2 := P.2
    omega⟩, P.2⟩
  left_inv α := rfl
  right_inv P := rfl
end Formalism.InvariantFactorPaths.ColumnFamilies


