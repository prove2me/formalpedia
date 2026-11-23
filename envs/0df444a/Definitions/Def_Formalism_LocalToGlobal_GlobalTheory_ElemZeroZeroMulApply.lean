-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_ElemZeroZeroMulApply
-- name    : Formalism_LocalToGlobal_GlobalTheory_ElemZeroZeroMulApply
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T02:16:02.846087+00:00
-- url     : https://prove2.me/theorems/d0add570-2a05-4fc4-92e0-19094ab27090
-- title:
--   Elem Zero Zero Mul Apply
-- statement:
--   Definitions and structural lemmas for Elem Zero Zero Mul Apply, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GlobalTheory/ElemZeroZeroMulApply.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Formalism.L2.GlobalTheoryTheory.ColValS
open Matrix
variable {O : Type} [CommRing O]
def el {n : ℕ} (b a : Fin n) (c : O) : Matrix (Fin n) (Fin n) O := 1 + Matrix.single b a c
def Gen (O : Type) [CommRing O] (n : ℕ) : Submonoid (Matrix (Fin n) (Fin n) O) :=
  Submonoid.closure {g | ∃ (b a : Fin n) (c : O), g = el b a c}
def bord {m : ℕ} (M : Matrix (Fin m) (Fin m) O) : Matrix (Fin (m+1)) (Fin (m+1)) O :=
  Matrix.of (Fin.cons (Fin.cons 1 0) (fun i => Fin.cons 0 (M i)))
def colS {m : ℕ} (f : Fin m → O) : Matrix (Fin (m+1)) (Fin (m+1)) O :=
  1 + ∑ i, Matrix.single i.succ 0 (f i)
def rowS {m : ℕ} (g : Fin m → O) : Matrix (Fin (m+1)) (Fin (m+1)) O :=
  1 + ∑ j, Matrix.single 0 j.succ (g j)
variable [IsLocalRing O]
end Formalism.L2.GlobalTheoryTheory.ColValS


