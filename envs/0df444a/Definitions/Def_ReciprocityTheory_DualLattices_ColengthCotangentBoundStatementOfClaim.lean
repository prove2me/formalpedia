-- Prove2me | Definitions.Def_ReciprocityTheory_DualLattices_ColengthCotangentBoundStatementOfClaim
-- name    : ReciprocityTheory_DualLattices_ColengthCotangentBoundStatementOfClaim
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T14:18:49.106521+00:00
-- url     : https://prove2.me/theorems/3dd8a413-3f8a-4920-93f9-88b4fced9838
-- title:
--   Colength Cotangent Bound Statement Of Claim
-- statement:
--   Definitions and structural lemmas for Colength Cotangent Bound Statement Of Claim, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/ColengthCotangentBoundStatementOfClaim.lean

import Definitions.Def_ReciprocityTheory_DualLattices_ColengthCotangentBoundStatement
import Definitions.Def_ReciprocityTheory_DualLattices_PrimeHopfOrderStatement
import Definitions.Def_ReciprocityTheory_DualLattices_IsLocalOfIntegers
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace ReciprocityTheory.PGsh.Up
open ReciprocityTheory.PGsh.L2
def ColengthCotangentValuation (p : ℕ) (C : Type) [Field C] (v : Valuation C NNReal) (R : Type) [CommRing R]
    [Algebra R C] : Prop :=
  ∀ (N : Type) [AddCommGroup N] [Fintype N] [DecidableEq N], (∀ x : N, p • x = 0) →
    ∀ AA : HopfOrder (C := C) R N,
    ∃ (n : ℕ) (g : Fin n → N → C) (δ : Fin n → R),
      (∀ i, g i ∈ augIdeal AA.carrier) ∧
      (∀ f ∈ augIdeal AA.carrier, ∃ r : Fin n → R,
        f - ∑ j, r j • g j ∈ sqIdeal (augIdeal AA.carrier)) ∧
      (∀ i, ∃ a : Fin n → R,
        δ i • g i - ∑ j, (if j < i then a j else 0) • g j ∈ sqIdeal (augIdeal AA.carrier)) ∧
      ∀ c, HasColen R v AA.carrier c →
        c ^ 2 = (∏ i, v (algebraMap R C (δ i))) ^ Fintype.card N
end ReciprocityTheory.PGsh.Up


