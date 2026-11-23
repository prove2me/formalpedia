-- Prove2me | Definitions.Def_ReciprocityTheory_DualLattices_ColengthCotangentBoundStatement
-- name    : ReciprocityTheory_DualLattices_ColengthCotangentBoundStatement
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T14:15:41.868809+00:00
-- url     : https://prove2.me/theorems/ed6356a6-dde1-4ae0-af4d-02387c056f1b
-- title:
--   Colength Cotangent Bound Statement
-- statement:
--   Definitions and structural lemmas for Colength Cotangent Bound Statement, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/ColengthCotangentBoundStatement.lean

import Definitions.Def_ReciprocityTheory_DualLattices_CotangentSurjective
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
namespace ReciprocityTheory.PGsh.Up
open ReciprocityTheory.PGsh.L2
def ColengthCotangentBoundStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C]
    (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C],
    v.Integers R → v (p : C) < 1 →
    ∀ (N : Type) [AddCommGroup N] [Fintype N] [DecidableEq N], (∀ x : N, p • x = 0) →
    ∀ (AA : HopfOrder (C := C) R N) (lenN lenOm : NNReal),
      HasColen R v AA.carrier lenN → HasLen v R (OmAA AA.carrier) lenOm →
      lenN ^ 2 ≤ lenOm ^ Fintype.card N
end ReciprocityTheory.PGsh.Up


