-- Prove2me | Definitions.Def_ReciprocityTheory_DualLattices_DvdOfCoeffZero
-- name    : ReciprocityTheory_DualLattices_DvdOfCoeffZero
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T04:18:16.141807+00:00
-- url     : https://prove2.me/theorems/353a22e5-9458-4fb8-bce5-305fab21c015
-- title:
--   Dvd Of Coeff Zero
-- statement:
--   Definitions and structural lemmas for Dvd Of Coeff Zero, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/DvdOfCoeffZero.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_CyclicRecursionStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open WittVector Ideal
namespace ReciprocityTheory.PGsh
variable {p : ℕ} [hp : Fact p.Prime]
section Sharp
variable {O : Type} [CommRing O] [Fact ¬IsUnit (p : O)] [IsAdicComplete (span {(p : O)}) O]
def sh (x : PreTilt O p) (n : ℕ) : O :=
  (((_root_.frobeniusEquiv (PreTilt O p) p).symm)^[n] x).untilt
end Sharp
section Ker
variable (C : Type) [Field C] [CharZero C] (v : Valuation C NNReal)
  {O : Type} [CommRing O] [Algebra O C] (hv : v.Integers O)
  [Fact ¬IsUnit (p : O)] [IsAdicComplete (span {(p : O)}) O]
include hv
end Ker
end ReciprocityTheory.PGsh


