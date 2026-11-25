-- Prove2me | Definitions.Def_GroundTheory_AutomorphicForms_WhittakerCells
-- name    : GroundTheory_AutomorphicForms_WhittakerCells
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-25T00:23:26.084813+00:00
-- url     : https://prove2.me/theorems/18581445-9250-4c74-9465-15afb2d09d83
-- title:
--   Whittaker Cells
-- statement:
--   Definitions and structural lemmas for Whittaker Cells, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/WhittakerCells.lean

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_FiniteBruhat
import Definitions.Def_GroundTheory_AutomorphicForms_Iwasawa
import Theorems.Thm_GroundTheory_Automorphic_borel_diag_ne_zero
import Theorems.Thm_GroundTheory_Automorphic_exists_mem_doubleCoset_permGL

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace GroundTheory.Automorphic
namespace Whittaker
open Matrix DoubleCoset
variable {F : Type*} [Field F] {n : ℕ}
section Rank
def rowsFrom (i : Fin n) : Matrix (Fin n) (Fin n) F := diagonal fun r => if i ≤ r then 1 else 0
def colsTo (j : Fin n) : Matrix (Fin n) (Fin n) F := diagonal fun c => if c ≤ j then 1 else 0
noncomputable def llRank (i j : Fin n) (g : GL (Fin n) F) : ℕ :=
  (rowsFrom i * (g : Matrix (Fin n) (Fin n) F) * colsTo j).rank
section Topology
variable [TopologicalSpace F] [IsTopologicalRing F] [T1Space F]
end Topology
end Rank
section Cell
noncomputable def bruhatCell (g : GL (Fin n) F) : Equiv.Perm (Fin n) :=
  (exists_mem_doubleCoset_permGL g).choose
end Cell
section NormalForm
noncomputable def borelDiag {b : GL (Fin n) F} (hb : b ∈ borel n F) : Fin n → Fˣ :=
  fun i => Units.mk0 _ (borel_diag_ne_zero hb i)
end NormalForm
section Minor
def bottomRows (k : Fin n) (a : Fin (k.val + 1)) : Fin n :=
  ⟨n - (k.val + 1) + a.val, by have := a.isLt; have := k.isLt; omega⟩
noncomputable def cellMinor (w : Equiv.Perm (Fin n)) (g : GL (Fin n) F) (k : Fin n) : F :=
  ((g : Matrix (Fin n) (Fin n) F).submatrix (bottomRows k) fun a => w⁻¹ (bottomRows k a)).det
noncomputable def prodFrom (t : Fin n → Fˣ) (s : ℕ) : F :=
  ∏ x ∈ Finset.univ.filter (fun x : Fin n => s ≤ x.val), (t x : F)
end Minor
end Whittaker
end GroundTheory.Automorphic


