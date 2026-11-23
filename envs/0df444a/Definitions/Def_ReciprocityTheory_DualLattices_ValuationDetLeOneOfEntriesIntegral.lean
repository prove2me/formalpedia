-- Prove2me | Definitions.Def_ReciprocityTheory_DualLattices_ValuationDetLeOneOfEntriesIntegral
-- name    : ReciprocityTheory_DualLattices_ValuationDetLeOneOfEntriesIntegral
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T14:17:06.596948+00:00
-- url     : https://prove2.me/theorems/b14aa7a1-5c21-4207-9d27-79a4b3db0eba
-- title:
--   Valuation Det Le One Of Entries Integral
-- statement:
--   Definitions and structural lemmas for Valuation Det Le One Of Entries Integral, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/ValuationDetLeOneOfEntriesIntegral.lean

import Definitions.Def_ReciprocityTheory_DualLattices_TensorSpan
import Definitions.Def_ReciprocityTheory_DualLattices_IsUnitDetOfSpanEq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Finset
namespace ReciprocityTheory.PGsh.L2
variable {C : Type} [Field C] {R : Type} [CommRing R] [Algebra R C] {v : Valuation C NNReal}
variable {N : Type} [AddCommGroup N] [Fintype N] [DecidableEq N]
def h3co (K : AddSubgroup N) [DecidablePred (· ∈ K)] (β : Matrix K K C) (f : N → C) (x : N) : K → C :=
  β⁻¹ *ᵥ fun k : K => f (x + k)
def h3T (K : AddSubgroup N) [DecidablePred (· ∈ K)] (β : Matrix K K C) (k : K) : Matrix K K C :=
  Matrix.of fun l l' => (β⁻¹ *ᵥ fun k' : K => β (k + k') l) l'
def h3mm (K : AddSubgroup N) [DecidablePred (· ∈ K)] (β : Matrix K K C) (f : K → N → C) (x : N) : Matrix K K C :=
  Matrix.of fun j l => h3co K β (f j) x l
def hopfOrderSubgroup (AA : HopfOrder (C := C) R N) : Subring (N → C) where
  carrier := AA.carrier
  mul_mem' := fun ha hb => AA.mul_mem _ _ ha hb
  one_mem' := AA.one_mem
  add_mem' := fun ha hb => AA.carrier.add_mem ha hb
  zero_mem' := AA.carrier.zero_mem
  neg_mem' := fun ha => AA.carrier.neg_mem ha
end ReciprocityTheory.PGsh.L2


