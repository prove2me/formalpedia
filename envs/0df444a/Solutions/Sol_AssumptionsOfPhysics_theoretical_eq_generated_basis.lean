-- Prove2me | solution 1 for AssumptionsOfPhysics.theoretical_eq_generated_basis
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-03T04:33:20.095848+00:00
-- url     : https://prove2.me/submissions/189a9b74-b918-4eef-a972-1418c59f1602

import Mathlib
import Definitions.Def_AoP_ExperimentalDomains

set_option autoImplicit false

namespace AoP74611c7f

open AssumptionsOfPhysics

theorem fin_to_neg {Ω : Type*} {B : Set (Set Ω)} {s : Set Ω}
    (h : FinConjCountDisj B s) : NegFinConjCountDisj B s := by
  induction h with
  | basic hs => exact NegFinConjCountDisj.basic hs
  | univ => exact NegFinConjCountDisj.univ
  | empty =>
    have := NegFinConjCountDisj.compl (NegFinConjCountDisj.univ (B := B))
    simpa using this
  | inter _ _ ih1 ih2 => exact NegFinConjCountDisj.inter ih1 ih2
  | iUnion f _ ih => exact NegFinConjCountDisj.iUnion f ih

theorem neg_mono {Ω : Type*} {B C : Set (Set Ω)} (hBC : ∀ b ∈ B, NegFinConjCountDisj C b)
    {s : Set Ω} (h : NegFinConjCountDisj B s) : NegFinConjCountDisj C s := by
  induction h with
  | basic hs => exact hBC _ hs
  | univ => exact NegFinConjCountDisj.univ
  | compl _ ih => exact NegFinConjCountDisj.compl ih
  | inter _ _ ih1 ih2 => exact NegFinConjCountDisj.inter ih1 ih2
  | iUnion f _ ih => exact NegFinConjCountDisj.iUnion f ih

end AoP74611c7f

open AssumptionsOfPhysics in
theorem solution {Ω : Type*} (D : ExperimentalDomain Ω)
    (B : Set (Set Ω)) (hB : IsBasis D.stmts B) :
    D.theoretical = {s | NegFinConjCountDisj B s} := by
  ext s
  constructor
  · intro h
    exact AoP74611c7f.neg_mono (fun b hb => AoP74611c7f.fin_to_neg (hB.2 b hb)) h
  · intro h
    exact AoP74611c7f.neg_mono (fun b hb => NegFinConjCountDisj.basic (hB.1 hb)) h
