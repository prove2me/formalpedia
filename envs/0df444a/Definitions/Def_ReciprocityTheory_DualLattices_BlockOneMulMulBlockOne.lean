-- Prove2me | Definitions.Def_ReciprocityTheory_DualLattices_BlockOneMulMulBlockOne
-- name    : ReciprocityTheory_DualLattices_BlockOneMulMulBlockOne
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T14:17:39.272859+00:00
-- url     : https://prove2.me/theorems/aa664a7b-e59a-4b6c-a462-e95ebe46943e
-- title:
--   Block One Mul Mul Block One
-- statement:
--   Definitions and structural lemmas for Block One Mul Mul Block One, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/BlockOneMulMulBlockOne.lean

import Definitions.Def_ReciprocityTheory_DualLattices_UpSmith
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
namespace ReciprocityTheory.PGsh.Up.Smith
section general
variable {R : Type} [CommRing R]
def Vm {N : ℕ} (j0 : Fin (N + 1)) (s : Fin (N + 1) → R) : Matrix (Fin (N + 1)) (Fin (N + 1)) R :=
  Matrix.of fun k l =>
    if l = j0 then (if k = j0 then 1 else 0) else ((if k = l then 1 else 0) - (if k = j0 then s l else 0))
def piv {N : ℕ} (i0 : Fin (N + 1)) : Equiv.Perm (Fin (N + 1)) :=
  (finSuccEquiv N).trans (finSuccEquiv' i0).symm
def bd1 {N M : ℕ} (P : Matrix (Fin N) (Fin M) R) : Matrix (Fin (N + 1)) (Fin (M + 1)) R :=
  Matrix.of fun i j => Fin.cases (Fin.cases 1 (fun _ => 0) j) (fun l => Fin.cases 0 (fun k => P l k) j) i
end general
variable {C : Type} [Field C] {v : Valuation C NNReal} {R : Type} [CommRing R] [Algebra R C]
end ReciprocityTheory.PGsh.Up.Smith


