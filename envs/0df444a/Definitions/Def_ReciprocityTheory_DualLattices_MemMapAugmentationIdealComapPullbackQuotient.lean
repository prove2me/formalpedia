-- Prove2me | Definitions.Def_ReciprocityTheory_DualLattices_MemMapAugmentationIdealComapPullbackQuotient
-- name    : ReciprocityTheory_DualLattices_MemMapAugmentationIdealComapPullbackQuotient
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T14:26:19.981942+00:00
-- url     : https://prove2.me/theorems/92bdab78-71e8-4233-983f-b38ce8f8f077
-- title:
--   Mem Map Augmentation Ideal Comap Pullback Quotient
-- statement:
--   Definitions and structural lemmas for Mem Map Augmentation Ideal Comap Pullback Quotient, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/MemMapAugmentationIdealComapPullbackQuotient.lean

import Definitions.Def_ReciprocityTheory_DualLattices_ExistsFamilyValuationDetEqOne
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
section family
variable (hv : v.Integers R) (AA : HopfOrder (C := C) R N) (K : AddSubgroup N)
  [DecidablePred (· ∈ K)] (β : Matrix K K C) (hβ : IsUnit β.det)
  (hAK : AA.carrier.map (resK (R := R) K) = Submodule.span R (Set.range fun j k => β k j))
  (f : K → N → C) (hf : ∀ j, f j ∈ AA.carrier) (hdet : ∀ x, v (h3mm K β f x).det = 1)
end family
end ReciprocityTheory.PGsh.L2


