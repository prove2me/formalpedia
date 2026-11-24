-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_LuLowerLowerTriangular
-- name    : Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_LuLowerLowerTriangular
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-24T17:38:10.594113+00:00
-- url     : https://prove2.me/theorems/c7a3831a-b594-4d6b-8103-217a9c6593d7
-- title:
--   Lu Lower Lower Triangular
-- statement:
--   Definitions and structural lemmas for Lu Lower Lower Triangular, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/LuLowerLowerTriangular.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_IsClosedFlagsIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_UniMatBlockTriangular
import Theorems.Thm_GlobalTheory_FullFlag_map_sub
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.FullFlag.map_sub


set_option autoImplicit false
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.FlagPts
variable {k : Type} [Field k] {n : ℕ}
def leadBlock (P : Matrix (Fin n) (Fin n) k) (m : Fin n) : Matrix (Fin (m + 1)) (Fin (m + 1)) k :=
  P.submatrix (Fin.castLE m.isLt) (Fin.castLE m.isLt)
def leadMinor (P : Matrix (Fin n) (Fin n) k) (m : Fin n) : k := (leadBlock P m).det
def luNum (P : Matrix (Fin n) (Fin n) k) (a m : Fin n) : k :=
  ∑ l : Fin (m + 1), P a (Fin.castLE m.isLt l) * (leadBlock P m).cramer (Pi.single (Fin.last m) 1) l
def luLower (P : Matrix (Fin n) (Fin n) k) : Matrix (Fin n) (Fin n) k := fun a m =>
  if a = m then 1 else if m < a then luNum P a m / leadMinor P m else 0
example (P : Matrix (Fin (n + 1)) (Fin (n + 1)) k) : leadMinor P (Fin.last n) = P.det := by
  simp [leadMinor, leadBlock]
end GlobalTheory.FlagPts


