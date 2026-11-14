-- Prove2me | solution 1 for APFB05.novel_chain_bound_stagewise
-- status  : ACCEPTED   (prove)
-- author  : @FiniteUniverse
-- created : 2026-11-14T05:48:01.709786+00:00
-- url     : https://prove2.me/submissions/bd7da297-70ac-4f73-abb4-80f19968a522

/-
APF Foundation Ledger — theorem node DRAFT (session EthanBrooke-01WrrBvu, 2026-11-13; not gated, not reviewed)
name: APFB05_novel_chain_stagewise
title: From B05's declared form: a chain of families, each adding one support-novel distinction and each admissible, has length at most the capacity divided by the floor
inputs_revision: 2026-10-04.1
mathlib_rev: 0df444a360eaa60ab8c11dca51a86af692955474
source: FOUNDATION_INPUTS B05 in declared form (APFB05.MarginalFloor), B04 through the capacity in ledger
 admissibility. The platform node APFB05.support_novel_chain_capacity_bound states the same bound asking
 admissibility of the last family only; its proof is on the platform and the copy in this draft tree is a
 stub. This node proves the bound here, asking admissibility of every stage, so that nothing in this tree
 rests on the stub.
consumes_inputs: B05 (APFB05.MarginalFloor) as a hypothesis. No other input.
statement: (APFB05.novel_chain_bound_stagewise) if S (i+1) is S i with one tested distinction added that is
 support-novel over S i, for each i below n, and every S i up to n is ledger-admissible at the capacity, then
 n times the floor is at most the family cost of S n, and n is at most the capacity divided by the floor.
reading: a step that draws something support-novel each time it is taken can be taken at most capacity over
 floor times. No assumption that bills add up is used; B05's floor does the work. And so a step that can be
 taken without end draws something support-novel at most that many times.
not_claimed: anything about the bill of a word; that a hold bills nothing.
-/
import Definitions.Def_APF_B05_DeclaredInput_r2
import Theorems.Thm_APFPaper1_Source_familyCost_nonneg
import Theorems.Thm_APFPaper1_Source_familyCost_mono
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.Linarith

set_option autoImplicit false

open APFPaper1.Source

theorem APFB05.novel_chain_bound_stagewise
    {Context : Type*} {D P R Record : Context → Type*} [∀ g, DecidableEq (D g)]
    (wholeResource : (g : Context) → P g → R g)
    (calibration : (g : Context) → R g → NNReal)
    (maintained : (g : Context) → P g → Set (Record g))
    (sufficient : (g : Context) → P g → Set (Record g) → D g → Prop)
    (usesToRealize : (g : Context) → P g → D g → Set (Record g) → Prop)
    (tested : (g : Context) → D g → Prop) (C epsilon : Context → ℝ)
    (hB05 : APFB05.MarginalFloor wholeResource calibration maintained sufficient usesToRealize
      tested C epsilon)
    (g : Context) (n : ℕ) (S : ℕ → Finset (D g)) (d : ℕ → D g)
    (hstep : ∀ i < n, S (i + 1) = insert (d i) (S i))
    (htested : ∀ i < n, tested g (d i))
    (hnovel : ∀ i < n, supportNovel (wholeResource g) (calibration g) (maintained g)
      (sufficient g) (usesToRealize g) (S i) (d i))
    (hadm : ∀ i ≤ n, familyAdmissible (wholeResource g) (calibration g) (maintained g)
      (sufficient g) (usesToRealize g) (C g) (S i)) :
    (n : ℝ) * epsilon g ≤ familyCost (wholeResource g) (calibration g) (maintained g)
        (sufficient g) (usesToRealize g) (S n) ∧
      (n : ℝ) ≤ C g / epsilon g := by
  obtain ⟨heps, hfloor⟩ := hB05 g
  have key : ∀ k : ℕ, k ≤ n → (k : ℝ) * epsilon g ≤
      familyCost (wholeResource g) (calibration g) (maintained g) (sufficient g)
        (usesToRealize g) (S k) := by
    intro k
    induction k with
    | zero =>
      intro _
      rw [Nat.cast_zero, zero_mul]
      exact familyCost_nonneg _ _ _ _ _ _
    | succ k ih =>
      intro hk
      have hk' : k < n := hk
      have h1 := ih (Nat.le_of_lt hk')
      have hins : familyAdmissible (wholeResource g) (calibration g) (maintained g)
          (sufficient g) (usesToRealize g) (C g) (insert (d k) (S k)) := by
        rw [← hstep k hk']
        exact hadm (k + 1) hk
      have h2 := hfloor (S k) (d k) (htested k hk') (hadm k (Nat.le_of_lt hk')) hins
        (hnovel k hk')
      rw [hstep k hk']
      push_cast
      linarith
  have hn := key n (le_refl n)
  exact ⟨hn, (le_div_iff₀ heps).mpr (le_trans hn (hadm n (le_refl n)).2)⟩


universe apfNative_u_1 apfNative_u_2 apfNative_u_3 apfNative_u_4 apfNative_u_5
theorem solution :
∀ {Context : Type apfNative_u_1} {D : Context → Type apfNative_u_2} {P : Context → Type apfNative_u_3}
  {R : Context → Type apfNative_u_4} {Record : Context → Type apfNative_u_5}
  [inst : (g : Context) → DecidableEq.{apfNative_u_2 + 1} (D g)] (wholeResource : (g : Context) → P g → R g)
  (calibration : (g : Context) → R g → NNReal) (maintained : (g : Context) → P g → Set.{apfNative_u_5} (Record g))
  (sufficient : (g : Context) → P g → Set.{apfNative_u_5} (Record g) → D g → Prop)
  (usesToRealize : (g : Context) → P g → D g → Set.{apfNative_u_5} (Record g) → Prop)
  (tested : (g : Context) → D g → Prop) (C epsilon : Context → Real)
  (hB05 :
    @APFB05.MarginalFloor.{apfNative_u_1, apfNative_u_2, apfNative_u_3, apfNative_u_4, apfNative_u_5} Context D P R
      Record inst wholeResource calibration maintained sufficient usesToRealize tested C epsilon)
  (g : Context) (n : Nat) (S : Nat → Finset.{apfNative_u_2} (D g)) (d : Nat → D g)
  (hstep :
    ∀ (i : Nat),
      @LT.lt.{0} Nat instLTNat i n →
        @Eq.{apfNative_u_2 + 1} (Finset.{apfNative_u_2} (D g))
          (S
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) i
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
          (@Insert.insert.{apfNative_u_2, apfNative_u_2} (D g) (Finset.{apfNative_u_2} (D g))
            (@Finset.instInsert.{apfNative_u_2} (D g) (inst g)) (d i) (S i)))
  (htested : ∀ (i : Nat), @LT.lt.{0} Nat instLTNat i n → tested g (d i))
  (hnovel :
    ∀ (i : Nat),
      @LT.lt.{0} Nat instLTNat i n →
        @APFPaper1.Source.supportNovel.{apfNative_u_2, apfNative_u_3, apfNative_u_4, apfNative_u_5} (D g) (P g) (R g)
          (Record g) (wholeResource g) (calibration g) (maintained g) (sufficient g) (usesToRealize g) (S i) (d i))
  (hadm :
    ∀ (i : Nat),
      @LE.le.{0} Nat instLENat i n →
        @APFPaper1.Source.familyAdmissible.{apfNative_u_2, apfNative_u_3, apfNative_u_4, apfNative_u_5} (D g) (P g)
          (R g) (Record g) (wholeResource g) (calibration g) (maintained g) (sufficient g) (usesToRealize g) (C g)
          (S i)),
  And
    (@LE.le.{0} Real Real.instLE
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) (@Nat.cast.{0} Real Real.instNatCast n)
        (epsilon g))
      (@APFPaper1.Source.familyCost.{apfNative_u_2, apfNative_u_3, apfNative_u_4, apfNative_u_5} (D g) (P g) (R g)
        (Record g) (wholeResource g) (calibration g) (maintained g) (sufficient g) (usesToRealize g) (S n)))
    (@LE.le.{0} Real Real.instLE (@Nat.cast.{0} Real Real.instNatCast n)
      (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
        (C g) (epsilon g))) := by
  exact @APFB05.novel_chain_bound_stagewise
