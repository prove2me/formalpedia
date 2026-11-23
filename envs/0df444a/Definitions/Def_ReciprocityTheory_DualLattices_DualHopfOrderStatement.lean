-- Prove2me | Definitions.Def_ReciprocityTheory_DualLattices_DualHopfOrderStatement
-- name    : ReciprocityTheory_DualLattices_DualHopfOrderStatement
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T14:16:31.099092+00:00
-- url     : https://prove2.me/theorems/428ed212-80dd-4f87-ae6a-5605c5f722bb
-- title:
--   Dual Hopf Order Statement
-- statement:
--   Definitions and structural lemmas for Dual Hopf Order Statement, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/DualHopfOrderStatement.lean

import Definitions.Def_ReciprocityTheory_DualLattices_TensorSpan
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace ReciprocityTheory.PGsh.L2
variable {C : Type} [Field C] {R : Type} [CommRing R] [Algebra R C]
def DualHopfOrderStatement : Prop :=
  ∀ (v : Valuation C NNReal), v.Integers R →
  ∀ (N H : Type) [AddCommGroup N] [Fintype N] [DecidableEq N] [AddCommGroup H] [Fintype H]
    [DecidableEq H] (e : H ≃ AddChar N C), (∀ h h', e (h + h') = e h * e h') →
    Fintype.card H = Fintype.card N →
    ∀ AA : HopfOrder (C := C) R N,
      ∃ AD : HopfOrder (C := C) R H,
        AD.carrier = (dualLat AA.carrier).map (fourier (R := R) fun h a => e h a) ∧
        (dualLat AD.carrier).map (fourier (R := R) fun a h => e h a) = AA.carrier ∧
        ∀ c c', HasColen R v AA.carrier c → HasColen R v AD.carrier c' →
          (c * c') ^ 2 = v (Fintype.card N : C) ^ Fintype.card N
end ReciprocityTheory.PGsh.L2


