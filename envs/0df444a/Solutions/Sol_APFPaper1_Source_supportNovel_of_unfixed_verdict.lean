-- Prove2me | solution 1 for APFPaper1.Source.supportNovel_of_unfixed_verdict
-- status  : ACCEPTED   (prove)
-- author  : @FiniteUniverse
-- created : 2026-11-14T06:10:48.962201+00:00
-- url     : https://prove2.me/submissions/2566af51-307a-473a-bc82-d6ed0e4cd1dc

/-
APF Foundation Ledger — theorem node DRAFT (session EthanBrooke-01WrrBvu, 2026-11-13; not gated, not reviewed)
name: APFPaper1_support_novel_bridge
title: A distinction whose verdict is not fixed by what any near-cheapest protocol for a family maintains is support-novel over that family
inputs_revision: 2026-10-04.1
mathlib_rev: 0df444a360eaa60ab8c11dca51a86af692955474
source: Paper 1 Supplement v9.28: def:physical-distinction (1745-1750, a distinction is a separator with
 values 0 and 1), def:record-support-rank (2624, support novelty), rem:cost-monotonicity-model (2313, a
 filter "cannot create a separator that was not already maintained by the source register"), and the remark
 at 1824 ("a derived discriminator reading a digit of an already-maintained record": the increment vanishes).
consumes_inputs: none. CONDITIONAL on hsound, a law on the source data that the Lean form of `sufficient`
 does not carry: records sufficient to realize a distinction fix its verdict.
statement: (supportNovel_of_unfixed_verdict) let records sufficient for d fix the verdict of d. If, for some
 positive eta, every protocol that serves S at a bill no more than eta above the family cost of S has two
 states that agree on every record it maintains and differ in the verdict of d, then d is support-novel
 over S.
not_claimed: hsound for the original source data; that near-cheapest protocols for a given family maintain
 nothing that separates more than the family does.
-/
import Definitions.Def_APFPaper1_FamilyCost

set_option autoImplicit false
namespace APFPaper1.Source

theorem supportNovel_of_unfixed_verdict {D P R Record Ω Val : Type*}
    (wholeResource : P → R) (calibration : R → NNReal) (maintained : P → Set Record)
    (sufficient : P → Set Record → D → Prop) (usesToRealize : P → D → Set Record → Prop)
    (reads : P → Record → Ω → Val) (verdict : D → Ω → Prop) (S : Finset D) (d : D)
    (hsound : ∀ (p : P) (sigma : Set Record), sufficient p sigma d →
      ∀ x y : Ω, (∀ r ∈ sigma, reads p r x = reads p r y) → (verdict d x ↔ verdict d y))
    (eta : ℝ) (heta : 0 < eta)
    (hunfixed : ∀ p : P,
      (∀ e ∈ S, ∃ sigma : Set Record,
        sigma ⊆ maintained p ∧ sufficient p sigma e ∧ usesToRealize p e sigma) →
      (calibration (wholeResource p) : ℝ) ≤
        familyCost wholeResource calibration maintained sufficient usesToRealize S + eta →
      ∃ x y : Ω, (∀ r ∈ maintained p, reads p r x = reads p r y) ∧ ¬ (verdict d x ↔ verdict d y)) :
    supportNovel wholeResource calibration maintained sufficient usesToRealize S d :=
  ⟨eta, heta, fun p hserve hbill ⟨sigma, hsub, hsuf⟩ => by
    obtain ⟨x, y, hagree, hne⟩ := hunfixed p hserve hbill
    exact hne (hsound p sigma hsuf x y (fun r hr => hagree r (hsub hr)))⟩

end APFPaper1.Source


universe apfNative_u_1 apfNative_u_2 apfNative_u_3 apfNative_u_4 apfNative_u_5 apfNative_u_6
theorem solution :
∀ {D : Type apfNative_u_1} {P : Type apfNative_u_2} {R : Type apfNative_u_3} {Record : Type apfNative_u_4}
  {Ω : Type apfNative_u_5} {Val : Type apfNative_u_6} (wholeResource : P → R) (calibration : R → NNReal)
  (maintained : P → Set.{apfNative_u_4} Record) (sufficient : P → Set.{apfNative_u_4} Record → D → Prop)
  (usesToRealize : P → D → Set.{apfNative_u_4} Record → Prop) (reads : P → Record → Ω → Val) (verdict : D → Ω → Prop)
  (S : Finset.{apfNative_u_1} D) (d : D)
  (hsound :
    ∀ (p : P) (sigma : Set.{apfNative_u_4} Record),
      sufficient p sigma d →
        ∀ (x y : Ω),
          (∀ (r : Record),
              @Membership.mem.{apfNative_u_4, apfNative_u_4} Record (Set.{apfNative_u_4} Record)
                  (@Set.instMembership.{apfNative_u_4} Record) sigma r →
                @Eq.{apfNative_u_6 + 1} Val (reads p r x) (reads p r y)) →
            Iff (verdict d x) (verdict d y))
  (eta : Real)
  (heta : @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) eta)
  (hunfixed :
    ∀ (p : P),
      (∀ (e : D),
          @Membership.mem.{apfNative_u_1, apfNative_u_1} D (Finset.{apfNative_u_1} D)
              (@SetLike.instMembership.{apfNative_u_1, apfNative_u_1} (Finset.{apfNative_u_1} D) D
                (@Finset.instSetLike.{apfNative_u_1} D))
              S e →
            @Exists.{apfNative_u_4 + 1} (Set.{apfNative_u_4} Record) fun (sigma : Set.{apfNative_u_4} Record) =>
              And
                (@LE.le.{apfNative_u_4} (Set.{apfNative_u_4} Record) (@Set.instLE.{apfNative_u_4} Record) sigma
                  (maintained p))
                (And (sufficient p sigma e) (usesToRealize p e sigma))) →
        @LE.le.{0} Real Real.instLE (NNReal.toReal (calibration (wholeResource p)))
            (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
              (@APFPaper1.Source.familyCost.{apfNative_u_1, apfNative_u_2, apfNative_u_3, apfNative_u_4} D P R Record
                wholeResource calibration maintained sufficient usesToRealize S)
              eta) →
          @Exists.{apfNative_u_5 + 1} Ω fun (x : Ω) =>
            @Exists.{apfNative_u_5 + 1} Ω fun (y : Ω) =>
              And
                (∀ (r : Record),
                  @Membership.mem.{apfNative_u_4, apfNative_u_4} Record (Set.{apfNative_u_4} Record)
                      (@Set.instMembership.{apfNative_u_4} Record) (maintained p) r →
                    @Eq.{apfNative_u_6 + 1} Val (reads p r x) (reads p r y))
                (Not (Iff (verdict d x) (verdict d y)))),
  @APFPaper1.Source.supportNovel.{apfNative_u_1, apfNative_u_2, apfNative_u_3, apfNative_u_4} D P R Record wholeResource
    calibration maintained sufficient usesToRealize S d := by
  exact @APFPaper1.Source.supportNovel_of_unfixed_verdict
