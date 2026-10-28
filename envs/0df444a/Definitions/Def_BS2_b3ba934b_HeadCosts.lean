-- Prove2me | Definitions.Def_BS2_b3ba934b_HeadCosts
-- name    : BS2_b3ba934b_HeadCosts
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T04:02:47.970991+00:00
-- url     : https://prove2.me/theorems/45f29efb-3ab6-49ce-a1a4-0bb7caceb52a
-- title:
--   Sensitivity separation: HeadCosts (complete source module)
-- statement:
--   Complete Lean source module `HeadCosts` from the two verified sensitivity separation proofs. The module supplies the definitions, auxiliary lemmas, and exact finite certificates used by its dependent modules. All original declarations and proof bodies are retained; only local import module paths are changed for Prove2Me. The final campaign goals are published separately as theorems with submitted solutions.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/HeadCosts.lean; original SHA-256 5d4a0873736723d0ebe3955104bb13e558443ffd4e86df00cd8e4f3c06d25794; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

/- Actual conditional boundary costs at one two-child head. -/
import Definitions.Def_BS2_b3ba934b_GradedPositiveBoundary
import Mathlib.Data.Finset.Powerset
import Mathlib.Tactic.FinCases

set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option linter.unusedSectionVars false

namespace ThreeBoundHeadCharge
open OAI.Paper320 ThreeBoundWitness ThreeBoundProfiles ThreeBoundPositive
open scoped Classical BigOperators
noncomputable section

variable {L I V : Type} [Preorder L] [Fintype I] [Fintype V]

def headBits (v : V) (s : Bool → Finset I) : Finset ((V × Bool) × I) :=
  liftBits v false (s false) ∪ liftBits v true (s true)

theorem headBits_card (v : V) (s : Bool → Finset I) :
    (headBits v s).card = (s false).card + (s true).card := by
  have hd : Disjoint (liftBits v false (s false)) (liftBits v true (s true)) := by
    apply Finset.disjoint_left.mpr
    rintro ⟨⟨w,c⟩,a⟩ hx hy
    have hxf := (mem_liftBits v w false c a _).1 hx
    have hyt := (mem_liftBits v w true c a _).1 hy
    exact Bool.false_ne_true (hxf.2.1.symm.trans hyt.2.1)
  simp only [headBits,Finset.card_union_of_disjoint hd,card_liftBits]

@[simp] theorem mem_headBits (v w : V) (s : Bool → Finset I) (c : Bool) (a : I) :
    ((w,c),a) ∈ headBits v s ↔ w = v ∧ a ∈ s c := by
  cases c <;> simp [headBits,mem_liftBits]

theorem card_bool_finset (h : Finset Bool) :
    h.card = (if false ∈ h then 1 else 0) + (if true ∈ h then 1 else 0) := by
  have he : h = (if false ∈ h then {false} else ∅) ∪
      (if true ∈ h then {true} else ∅) := by
    ext b
    cases b <;> by_cases hf : false ∈ h <;> by_cases ht : true ∈ h <;> simp [hf,ht]
  rw [he]
  by_cases hf : false ∈ h <;> by_cases ht : true ∈ h <;> simp [hf,ht]

def positiveParts (F : L → (I → Bool) → Bool) (g t : L)
    (x : Bool → I → Bool) (missing : Bool) (hit : Finset Bool) (c : Bool) : Finset I :=
  (if c = missing then flipsTo (F t) true (x c) else ∅) ∪
    (if c ∈ hit then flipsTo (F g) false (x c) else ∅)

def positiveCost (a u j n : ℕ) : ℕ :=
  if n = 0 then a else if n = 1 then max u (a+j) else j + max u a

theorem positiveCost_mono (a u j m n : ℕ) (hmn : m ≤ n) :
    positiveCost a u j m ≤ positiveCost a u j n := by
  unfold positiveCost
  split_ifs <;> omega

theorem head_cost_of_local_bounds
    (F : L → (I → Bool) → Bool) (g t : L)
    (x : Bool → I → Bool) (missing : Bool) (hit : Finset Bool) (v : V)
    (a u j incoming : ℕ)
    (ha : (flipsTo (F t) true (x missing)).card ≤ a)
    (hj : (flipsTo (F g) false (x (!missing))).card ≤ j)
    (hu : missing ∈ hit → ((flipsTo (F t) true (x missing)) ∪
      (flipsTo (F g) false (x missing))).card ≤ u)
    (hcount : hit.card ≤ incoming) :
    (headBits v (positiveParts F g t x missing hit)).card ≤
      positiveCost a u j incoming := by
  apply le_trans (b := positiveCost a u j hit.card) _
    (positiveCost_mono a u j hit.card incoming hcount)
  rw [headBits_card,card_bool_finset]
  cases missing <;>
    by_cases hf : false ∈ hit <;> by_cases ht' : true ∈ hit <;>
    simp [positiveParts,positiveCost,hf,ht'] at * <;> omega

/-- Actual P/D/B costs, after deduplicating incoming arcs to selected children. -/
theorem positive_head_cost
    (F : L → (I → Bool) → Bool) (g gw barrier t : L)
    (x : Bool → I → Bool) (missing : Bool) (hit : Finset Bool) (v : V)
    (a u j incoming : ℕ)
    (hp : PBound F g barrier t a) (hd : DBound F g gw barrier t u)
    (hb : BBound F g t j)
    (hg : F g (x missing) = true) (hbar : F barrier (x missing) = false)
    (ht : F t (x (!missing)) = true)
    (heligible : ∀ c ∈ hit, F gw (x c) = true)
    (hcount : hit.card ≤ incoming) :
    (headBits v (positiveParts F g t x missing hit)).card ≤
      positiveCost a u j incoming := by
  have ha := hp (x missing) hg hbar
  have hj := hb (x (!missing)) ht
  have hu : missing ∈ hit →
      ((flipsTo (F t) true (x missing)) ∪
        (flipsTo (F g) false (x missing))).card ≤ u := by
    intro hm
    simpa only [Finset.union_comm] using hd (x missing) (heligible missing hm) hbar
  exact head_cost_of_local_bounds F g t x missing hit v a u j incoming ha hj hu hcount

/-- The positive-only D cost may be minimized with the sum of the P and
    weak-guard B costs; weak eligibility is required only at hit children. -/
theorem positive_head_cost_min
    (F : L → (I → Bool) → Bool) (g gw barrier t : L)
    (x : Bool → I → Bool) (missing : Bool) (hit : Finset Bool) (v : V)
    (a d s j incoming : ℕ)
    (hp : PBound F g barrier t a) (hd : DBound F g gw barrier t d)
    (hs : BBound F g gw s) (hb : BBound F g t j)
    (hg : F g (x missing) = true) (hbar : F barrier (x missing) = false)
    (ht : F t (x (!missing)) = true)
    (heligible : ∀ c ∈ hit, F gw (x c) = true)
    (hcount : hit.card ≤ incoming) :
    (headBits v (positiveParts F g t x missing hit)).card ≤
      positiveCost a (min d (a+s)) j incoming := by
  apply head_cost_of_local_bounds F g t x missing hit v a (min d (a+s)) j incoming
    (hp (x missing) hg hbar) (hb (x (!missing)) ht) _ hcount
  intro hm
  apply le_min
  · simpa only [Finset.union_comm] using hd (x missing) (heligible missing hm) hbar
  · exact (Finset.card_union_le _ _).trans
      (Nat.add_le_add (hp (x missing) hg hbar) (hs (x missing) (heligible missing hm)))

def overlapCost (a u j n : ℕ) : ℕ :=
  if n = 0 then a else if n = 1 then max u (a+j) else u+j

/-- The overlap H has an accepted preceding target at its missing child.
    P, M and D all use that stronger actual interval. This proves both minima
    in the recurrence, including the condition that the union cost dominates a. -/
theorem overlap_head_cost
    (F : L → (I → Bool) → Bool) (g previous weak t : L)
    (x : Bool → I → Bool) (missing : Bool) (hit : Finset Bool) (v : V)
    (p d m j incoming : ℕ)
    (hp : PBound F previous weak t p)
    (hd : DBound F g previous weak t d)
    (hm : MBound F g previous weak m) (hb : BBound F g t j)
    (hprev : F previous (x missing) = true) (hweak : F weak (x missing) = false)
    (ht : F t (x (!missing)) = true)
    (hcount : hit.card ≤ incoming) :
    let a := min p d
    let u := min d (a+m)
    (headBits v (positiveParts F g t x missing hit)).card ≤
      overlapCost a u j incoming := by
  dsimp only
  let a := min p d
  let u := min d (a+m)
  have hdc := hd (x missing) hprev hweak
  have ha : (flipsTo (F t) true (x missing)).card ≤ a := by
    apply le_min (hp (x missing) hprev hweak)
    exact (Finset.card_le_card (Finset.subset_union_right)).trans hdc
  have hu : ((flipsTo (F t) true (x missing)) ∪
      (flipsTo (F g) false (x missing))).card ≤ u := by
    apply le_min
    · simpa only [Finset.union_comm] using hdc
    · exact (Finset.card_union_le _ _).trans
        (Nat.add_le_add ha (hm (x missing) hprev hweak))
  have hau : a ≤ u := by
    dsimp [a,u]
    omega
  have hcost := head_cost_of_local_bounds F g t x missing hit v a u j incoming ha
    (hb (x (!missing)) ht) (fun _ => hu) hcount
  have he : positiveCost a u j incoming = overlapCost a u j incoming := by
    unfold positiveCost overlapCost
    split_ifs <;> omega
  rw [he] at hcost
  exact hcost

def guardParts (F : L → (I → Bool) → Bool) (g : L)
    (x : Bool → I → Bool) (hit : Finset Bool) (c : Bool) : Finset I :=
  if c ∈ hit then flipsTo (F g) false (x c) else ∅

def guardCost (one two n : ℕ) : ℕ :=
  if n = 0 then 0 else if n = 1 then one else two

theorem guardCost_mono (one two m n : ℕ) (h : one ≤ two) (hmn : m ≤ n) :
    guardCost one two m ≤ guardCost one two n := by
  unfold guardCost
  split_ifs <;> omega

/-- Pure lower guard head: both children are in the full interval and at least
    one is in the lower subinterval. The exact recurrence formula follows. -/
theorem lower_guard_head_cost
    (F : L → (I → Bool) → Bool) (g t weakNext strongNext : L)
    (x : Bool → I → Bool) (hit : Finset Bool) (v : V)
    (m low middle incoming : ℕ)
    (hm : MBound F g t strongNext m)
    (hl : MBound F g t weakNext low)
    (hh : MBound F g weakNext strongNext middle)
    (ht : ∀ c, F t (x c) = true)
    (hn : ∀ c, F strongNext (x c) = false)
    (hweak : F weakNext (x false) = false ∨ F weakNext (x true) = false)
    (hcount : hit.card ≤ incoming) :
    (headBits v (guardParts F g x hit)).card ≤
      guardCost (min m (max low middle))
        (min (2*m) (max (2*low) (low+middle))) incoming := by
  have hmono : min m (max low middle) ≤ min (2*m) (max (2*low) (low+middle)) := by
    apply le_min
    · omega
    · have hmax : max low middle ≤ max (2*low) (low+middle) := by omega
      exact (min_le_right _ _).trans hmax
  have hfull : ∀ c, (flipsTo (F g) false (x c)).card ≤ m :=
    fun c => hm (x c) (ht c) (hn c)
  have hsplit : ∀ c, (flipsTo (F g) false (x c)).card ≤ max low middle := by
    intro c
    cases hw : F weakNext (x c) with
    | false => exact (hl (x c) (ht c) hw).trans (le_max_left _ _)
    | true => exact (hh (x c) hw (hn c)).trans (le_max_right _ _)
  have hsum : (flipsTo (F g) false (x false)).card +
      (flipsTo (F g) false (x true)).card ≤ max (2*low) (low+middle) := by
    rcases hweak with hw | hw
    · have hf := hl (x false) (ht false) hw
      cases hw' : F weakNext (x true) with
      | false => have hh' := hl (x true) (ht true) hw'; omega
      | true => have hh' := hh (x true) hw' (hn true); omega
    · have ht' := hl (x true) (ht true) hw
      cases hw' : F weakNext (x false) with
      | false => have hh' := hl (x false) (ht false) hw'; omega
      | true => have hh' := hh (x false) hw' (hn false); omega
  apply le_trans (b := guardCost (min m (max low middle))
      (min (2*m) (max (2*low) (low+middle))) hit.card) _
    (guardCost_mono _ _ _ _ hmono hcount)
  rw [headBits_card,card_bool_finset]
  have hf := hfull false
  have ht' := hfull true
  have hsf := hsplit false
  have hst := hsplit true
  by_cases hf' : false ∈ hit <;> by_cases ht'' : true ∈ hit <;>
    simp [guardParts,guardCost,hf',ht''] <;> omega

/-- Top guard heads use the accepted-target B cost once per selected child. -/
theorem top_guard_head_cost
    (F : L → (I → Bool) → Bool) (g t : L)
    (x : Bool → I → Bool) (hit : Finset Bool) (v : V) (j incoming : ℕ)
    (hb : BBound F g t j) (ht : ∀ c, F t (x c) = true)
    (hcount : hit.card ≤ incoming) :
    (headBits v (guardParts F g x hit)).card ≤ guardCost j (2*j) incoming := by
  have hf := hb (x false) (ht false)
  have ht' := hb (x true) (ht true)
  apply le_trans (b := guardCost j (2*j) hit.card) _
    (guardCost_mono _ _ _ _ (by omega) hcount)
  rw [headBits_card,card_bool_finset]
  by_cases h0 : false ∈ hit <;> by_cases h1 : true ∈ hit <;>
    simp [guardParts,guardCost,h0,h1] <;> omega

end
end ThreeBoundHeadCharge

#print axioms ThreeBoundHeadCharge.positive_head_cost
#print axioms ThreeBoundHeadCharge.lower_guard_head_cost
#print axioms ThreeBoundHeadCharge.top_guard_head_cost


