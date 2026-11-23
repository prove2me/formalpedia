-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FontaineAinfLocalDomainXiAdicOrder
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_FontaineAinfLocalDomainXiAdicOrder
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T15:24:59.965789+00:00
-- url     : https://prove2.me/theorems/d57b7a71-9d6b-42a4-84ba-e310e3d55938
-- title:
--   Fontaine Ainf Local Domain Xi Adic Order
-- statement:
--   Definitions and structural lemmas for Fontaine Ainf Local Domain Xi Adic Order, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FontaineAinfLocalDomainXiAdicOrder.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_CotangentSurjective
import Definitions.Def_ReciprocityTheory_DualLattices_CyclicRecursionStatement
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_XiMulNu
import Definitions.Def_ReciprocityTheory_DualLattices_AinfFacts
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
namespace GlobalTheory.AinfXi
section Tilt
variable {p : ℕ} [hp : Fact p.Prime] {O : Type} [CommRing O] [Fact ¬IsUnit (p : O)]
end Tilt
section Witt
variable {p : ℕ} [hp : Fact p.Prime] {R : Type} [CommRing R] [CharP R p] [PerfectRing R p]
end Witt
section Main
open GlobalTheory.Sandwich
variable {p : ℕ} [hp : Fact p.Prime] {C : Type} [Field C] [IsAlgClosed C] [CharZero C]
  {v : Valuation C NNReal} {O : Type} [CommRing O] [Algebra O C]
  [Fact ¬IsUnit (p : O)] [IsAdicComplete (span {(p : O)}) O]
variable (hv : v.Integers O) (ε : PreTilt O p) (hε : IsPrimitiveRoot (root ε).untilt p)
include hv hε
end Main
section Statement
open ReciprocityTheory.PGsh.Up GlobalTheory.Sandwich Matrix
end Statement
end GlobalTheory.AinfXi


