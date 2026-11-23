-- Prove2me | Definitions.Def_ReciprocityTheory_DualLattices_MemDualLatMapFourier
-- name    : ReciprocityTheory_DualLattices_MemDualLatMapFourier
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T14:23:44.009582+00:00
-- url     : https://prove2.me/theorems/7cef4d53-6055-44a9-820c-a78a8a30f8de
-- title:
--   Mem Dual Lat Map Fourier
-- statement:
--   Definitions and structural lemmas for Mem Dual Lat Map Fourier, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/MemDualLatMapFourier.lean

import Definitions.Def_ReciprocityTheory_DualLattices_ValuationFourierLeOne
import Definitions.Def_ReciprocityTheory_DualLattices_CharTableIsUnit
import Definitions.Def_ReciprocityTheory_DualLattices_TransposeMulSelf
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset Matrix
namespace ReciprocityTheory.PGsh.L2
variable {C : Type} [Field C] {R : Type} [CommRing R] [Algebra R C]
variable {N : Type} [AddCommGroup N] [Fintype N] [DecidableEq N]
variable {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H]
def tableM (e : H ≃ AddChar N C) (σ : H ≃ N) : Matrix N N C :=
  Matrix.of fun x j => e (σ.symm j) x
end ReciprocityTheory.PGsh.L2


