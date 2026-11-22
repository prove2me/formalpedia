-- Prove2me | Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_InterlacingOfBlocksSecondCase
-- name    : Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_InterlacingOfBlocksSecondCase
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T20:31:49.249897+00:00
-- url     : https://prove2.me/theorems/c9b5e7e0-e084-4c54-8a99-855ca903e3a5
-- title:
--   Interlacing Of Blocks Second Case
-- statement:
--   Definitions and structural lemmas for Interlacing Of Blocks Second Case, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/InterlacingOfBlocksSecondCase.lean

import Definitions.Def_Formalism_FlagUnipotentLattices_MemLpTwoOfOneTop
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.HermitianLatticeCounting.S8 MeasureTheory Filter Topology TensorProduct Finset
set_option linter.all false
noncomputable section
namespace Formalism.HermitianLatticeCounting.P
def gdet {A : Type*} [Ring A] (t : ℕ) (F : ℕ → ℕ → ℂ → A) (x : ℂ) : A :=
  ∑ σ : Equiv.Perm (Fin t),
    ((Equiv.Perm.sign σ : ℤ) : A) * (List.ofFn fun p : Fin t => F (σ p) p (x - (p : ℂ))).prod
def rowN {n : ℕ} (r k : ℕ) (c w : ℕ → Fin n) (p : ℕ) : Fin n :=
  if p < r then c (p + 1) else if p < r + k then w (p - r) else c (p - k + 1)
def colN {n : ℕ} (r k : ℕ) (c w : ℕ → Fin n) (p : ℕ) : Fin n :=
  if p < r then c p else if p < r + k then w (p - r) else c (p - k)
def gN {n : ℕ} (r k : ℕ) (c w : ℕ → Fin n) (p : ℕ) : Fin n :=
  if p = 0 then c r else if p ≤ r then c (p - 1) else if p ≤ r + k then w (p - r - 1) else c (p - k)
end Formalism.HermitianLatticeCounting.P


