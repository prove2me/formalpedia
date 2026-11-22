-- Prove2me | Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_MulInvBlockDiagApplySameBlock
-- name    : Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_MulInvBlockDiagApplySameBlock
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T19:11:27.7608+00:00
-- url     : https://prove2.me/theorems/4f0f7ec6-90fc-4bd9-a987-77a026e207e2
-- title:
--   Mul Inv Block Diag Apply Same Block
-- statement:
--   Definitions and structural lemmas for Mul Inv Block Diag Apply Same Block, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/DoubleCosetMeasures/LowerUnipotentOrbits/MulInvBlockDiagApplySameBlock.lean

import Definitions.Def_Formalism_DoubleCosetMeasures_Statement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open Matrix
namespace Formalism.DoubleCosetMeasures.P
open Formalism.DoubleCosetMeasures
namespace Phase
theorem revIn_lt : ∀ (s : List ℕ) (j : ℕ), j < s.sum → revIn s j < s.sum
  | [], j, h => by simpa [revIn] using h
  | a :: s, j, h => by
    simp only [revIn, List.sum_cons] at h ⊢
    split_ifs with hj
    · omega
    · have := revIn_lt s (j - a) (by omega); omega
def revF (s : List ℕ) (a : Fin s.sum) : Fin s.sum := ⟨revIn s a, revIn_lt s a a.2⟩
variable {K : Type} [CommRing K]
def mono (s : List ℕ) (f : Fin s.sum → K) : Matrix (Fin s.sum) (Fin s.sum) K :=
  fun a c => if c = revF s a then f a else 0
def ptI (s : List ℕ) (t : ℕ → Kˣ) : Matrix (Fin s.sum) (Fin s.sum) K :=
  mono s (fun a => (((t (blk s a))⁻¹ : Kˣ) : K))
def bdiag (s : List ℕ) (x : Matrix (Fin s.sum) (Fin s.sum) K) : Matrix (Fin s.sum) (Fin s.sum) K :=
  fun a c => if blk s a = blk s c then x a c else 0
end Phase
end Formalism.DoubleCosetMeasures.P


