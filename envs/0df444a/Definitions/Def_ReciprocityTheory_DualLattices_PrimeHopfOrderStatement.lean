-- Prove2me | Definitions.Def_ReciprocityTheory_DualLattices_PrimeHopfOrderStatement
-- name    : ReciprocityTheory_DualLattices_PrimeHopfOrderStatement
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T14:15:47.558413+00:00
-- url     : https://prove2.me/theorems/cbe37077-fd89-4f40-a112-6153b4cfd653
-- title:
--   Prime Hopf Order Statement
-- statement:
--   Definitions and structural lemmas for Prime Hopf Order Statement, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/PrimeHopfOrderStatement.lean

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
def PrimeHopfOrderStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C]
    (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C],
    v.Integers R → v (p : C) < 1 →
    ∀ AA : HopfOrder (C := C) R (ZMod p),
    ∃ (x ω : ZMod p → C) (δ : R),
      x ∈ AA.carrier ∧ x 0 = 0 ∧ (∀ a, ω a ^ p = ω a) ∧ (∀ a, v (ω a - (a.val : C)) < 1) ∧
      (∀ a, x a = ω a * x 1) ∧ x ^ p = (fun a => algebraMap R C δ * x a) ∧
      v (algebraMap R C δ) = v (x 1) ^ (p - 1) ∧
      AA.carrier = Submodule.span R (Set.range fun j : Fin p => x ^ (j : ℕ)) ∧
      augIdeal AA.carrier = Submodule.span R {y | ∃ j : ℕ, 1 ≤ j ∧ j < p ∧ y = x ^ j} ∧
      sqIdeal (augIdeal AA.carrier) = Submodule.span R
        ({fun a => algebraMap R C δ * x a} ∪ {y | ∃ j : ℕ, 2 ≤ j ∧ j < p ∧ y = x ^ j}) ∧
      HasColen R v AA.carrier (v (x 1) ^ (p * (p - 1) / 2))
end ReciprocityTheory.PGsh.Up


