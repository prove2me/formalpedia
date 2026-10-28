-- Prove2me | Definitions.Def_BS2_b3ba934b_Q2CandidateTypes
-- name    : BS2_b3ba934b_Q2CandidateTypes
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T04:02:15.564936+00:00
-- url     : https://prove2.me/theorems/96a5a394-eff0-4ae5-9574-35802ffd2733
-- title:
--   Sensitivity separation: Q2CandidateTypes (complete source module)
-- statement:
--   Complete Lean source module `Q2CandidateTypes` from the two verified sensitivity separation proofs. The module supplies the definitions, auxiliary lemmas, and exact finite certificates used by its dependent modules. All original declarations and proof bodies are retained; only local import module paths are changed for Prove2Me. The final campaign goals are published separately as theorems with submitted solutions.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Q2CandidateTypes.lean; original SHA-256 7e8db07c231331862a069853ead1b29e5e7fab51f5c60add93e739c5f3441575; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

/-
Exact eight-type decomposition for equal-target graded rows through tolerance 2.

The predicates below refer to the actual child truth values and actual failed
guard count. The classification does not assume a sensitivity bound. It can be
instantiated with target b z := F (threshold b) z, and guard := F g.
-/
import Definitions.Def_BS2_b3ba934b_GuardAugmentation
import Definitions.Def_BS2_b3ba934b_Q2Enumeration
import Mathlib.Tactic.FinCases

set_option autoImplicit false
set_option maxHeartbeats 3000000

namespace Q2CandidateTypes
open scoped Classical
open TournamentHighRows

variable {X V : Type}

/-- One lower target is false and its partner is true, at the exact tier. -/
def TargetCandidate (target : ℕ → X → Prop) (Q d b : ℕ) (x y : X) : Prop :=
  b ≤ Q ∧ d = b ∧
    ((¬ target b x ∧ target b y) ∨ (target b x ∧ ¬ target b y))

/-- The positive part of a target candidate has two guard-true children. -/
def PositiveCandidate (guard : X → Prop) (target : ℕ → X → Prop)
    (Q d b : ℕ) (x y : X) : Prop :=
  TargetCandidate target Q d b x y ∧ guard x ∧ guard y

/-- A guard candidate would accept after removal of one actual failed guard. -/
def GuardCandidate (target : ℕ → X → Prop) (Q d b : ℕ) (x y : X) : Prop :=
  b ≤ Q ∧ d = b+1 ∧ target b x ∧ target b y

def High (guard : X → Prop) (target : ℕ → X → Prop)
    (Q d : ℕ) (x y : X) : Prop :=
  (∃ b, PositiveCandidate guard target Q d b x y) ∨
    (∃ b, GuardCandidate target Q d b x y)

/-- Fixed checkpoint order: P0, P1-only, P2-only, G0-only, G1-only,
    G2, H1=P1∩G0, H2=P2∩G1. -/
def budget (k : Fin 8) : ℕ :=
  match k.val with
  | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 1
  | 4 => 2 | 5 => 3 | 6 => 1 | _ => 2

theorem budget_eq_enumerator : budget = ThreeBoundQ2.budget := rfl

theorem positivePrefix_budget_le (q : ℕ) (k : Fin 8)
    (h : ThreeBoundQ2.positivePrefix q k = true) : budget k ≤ q := by
  fin_cases k <;> simp [ThreeBoundQ2.positivePrefix, ThreeBoundQ2.positiveLevel, budget] at h ⊢ <;>
    omega

def OfKind (guard : X → Prop) (target : ℕ → X → Prop)
    (Q d : ℕ) (x y : X) (k : Fin 8) : Prop :=
  let P := fun b => PositiveCandidate guard target Q d b x y
  let G := fun b => GuardCandidate target Q d b x y
  match k.val with
  | 0 => P 0
  | 1 => P 1 ∧ ¬ G 0
  | 2 => P 2 ∧ ¬ G 1
  | 3 => G 0 ∧ ¬ P 1
  | 4 => G 1 ∧ ¬ P 2
  | 5 => G 2
  | 6 => P 1 ∧ G 0
  | _ => P 2 ∧ G 1

theorem budget_le_three (k : Fin 8) : budget k ≤ 3 := by
  fin_cases k <;> decide

theorem ofKind_count (guard : X → Prop) (target : ℕ → X → Prop)
    (Q d : ℕ) (x y : X) (k : Fin 8)
    (hk : OfKind guard target Q d x y k) : d = budget k := by
  fin_cases k <;> simp only [OfKind, budget] at *
  · exact hk.1.2.1
  · exact hk.1.1.2.1
  · exact hk.1.1.2.1
  · exact hk.1.2.1
  · exact hk.1.2.1
  · exact hk.2.1
  · exact hk.1.1.2.1
  · exact hk.1.1.2.1

theorem ofKind_high (guard : X → Prop) (target : ℕ → X → Prop)
    (Q d : ℕ) (x y : X) (k : Fin 8)
    (hk : OfKind guard target Q d x y k) : High guard target Q d x y := by
  fin_cases k <;> simp only [OfKind] at hk
  · exact Or.inl ⟨0,hk⟩
  · exact Or.inl ⟨1,hk.1⟩
  · exact Or.inl ⟨2,hk.1⟩
  · exact Or.inr ⟨0,hk.1⟩
  · exact Or.inr ⟨1,hk.1⟩
  · exact Or.inr ⟨2,hk⟩
  · exact Or.inl ⟨1,hk.1⟩
  · exact Or.inl ⟨2,hk.1⟩

/-- These eight mutually exclusive types exhaust the actual high candidates. -/
theorem high_iff_exists_kind (guard : X → Prop) (target : ℕ → X → Prop)
    (Q d : ℕ) (hQ : Q ≤ 2) (x y : X) :
    High guard target Q d x y ↔ ∃ k : Fin 8, OfKind guard target Q d x y k := by
  classical
  constructor
  · rintro (⟨b,hb⟩ | ⟨b,hb⟩)
    · have hbQ : b ≤ Q := hb.1.1
      have hb012 : b = 0 ∨ b = 1 ∨ b = 2 := by omega
      rcases hb012 with rfl | rfl | rfl
      · exact ⟨0,hb⟩
      · by_cases hg : GuardCandidate target Q d 0 x y
        · exact ⟨6,hb,hg⟩
        · exact ⟨1,hb,hg⟩
      · by_cases hg : GuardCandidate target Q d 1 x y
        · exact ⟨7,hb,hg⟩
        · exact ⟨2,hb,hg⟩
    · have hbQ : b ≤ Q := hb.1
      have hb012 : b = 0 ∨ b = 1 ∨ b = 2 := by omega
      rcases hb012 with rfl | rfl | rfl
      · by_cases hp : PositiveCandidate guard target Q d 1 x y
        · exact ⟨6,hp,hb⟩
        · exact ⟨3,hb,hp⟩
      · by_cases hp : PositiveCandidate guard target Q d 2 x y
        · exact ⟨7,hp,hb⟩
        · exact ⟨4,hb,hp⟩
      · exact ⟨5,hb⟩
  · rintro ⟨k,hk⟩
    exact ofKind_high guard target Q d x y k hk

theorem kind_unique (guard : X → Prop) (target : ℕ → X → Prop)
    (Q d : ℕ) (x y : X) (k l : Fin 8)
    (hk : OfKind guard target Q d x y k)
    (hl : OfKind guard target Q d x y l) : k = l := by
  have hck := ofKind_count guard target Q d x y k hk
  have hcl := ofKind_count guard target Q d x y l hl
  fin_cases k <;> fin_cases l <;>
    simp only [budget, OfKind] at hck hcl hk hl ⊢ <;>
    first | rfl | omega | tauto

theorem high_iff_exists_unique_kind (guard : X → Prop) (target : ℕ → X → Prop)
    (Q d : ℕ) (hQ : Q ≤ 2) (x y : X) :
    High guard target Q d x y ↔ ∃! k : Fin 8, OfKind guard target Q d x y k := by
  constructor
  · intro h
    obtain ⟨k,hk⟩ := (high_iff_exists_kind guard target Q d hQ x y).1 h
    exact ⟨k,hk,fun l hl => kind_unique guard target Q d x y l k hl hk⟩
  · rintro ⟨k,hk,_⟩
    exact ofKind_high guard target Q d x y k hk

/-- Every high candidate has both actual guard predicates true. -/
theorem high_guard_true (guard : X → Prop) (target : ℕ → X → Prop)
    (Q d : ℕ) (x y : X)
    (hgt : ∀ b, b ≤ Q → ∀ z, target b z → guard z)
    (hh : High guard target Q d x y) : guard x ∧ guard y := by
  rcases hh with ⟨b,hb⟩ | ⟨b,hb⟩
  · exact hb.2
  · exact ⟨hgt b hb.1 x hb.2.2.1,hgt b hb.1 y hb.2.2.2⟩

/-- The two guard families can overlap a positive candidate only at the
    immediately preceding tier. This follows from the actual failure count. -/
theorem positive_guard_overlap (guard : X → Prop) (target : ℕ → X → Prop)
    (Q d b c : ℕ) (x y : X)
    (hp : PositiveCandidate guard target Q d b x y)
    (hg : GuardCandidate target Q d c x y) : b = c+1 := by
  have hpcount := hp.1.2.1
  have hgcount := hg.2.1
  omega

def Accepted (target : ℕ → X → Prop) (Q d : ℕ) (x y : X) : Prop :=
  d ≤ Q ∧ target d x ∧ target d y

/-- A pure lower guard candidate has two false next targets. If exactly one
    next target were false it would be the overlap type, and if neither were
    false the row would already accept. -/
theorem pure_guard_next_both_false (guard : X → Prop) (target : ℕ → X → Prop)
    (Q d b : ℕ) (x y : X) (hbQ : b+1 ≤ Q)
    (hgt : ∀ c, c ≤ Q → ∀ z, target c z → guard z)
    (hg : GuardCandidate target Q d b x y)
    (hp : ¬ PositiveCandidate guard target Q d (b+1) x y)
    (hno : ¬ Accepted target Q d x y) :
    ¬ target (b+1) x ∧ ¬ target (b+1) y := by
  classical
  have hd : d = b+1 := hg.2.1
  have hxg : guard x := hgt b hg.1 x hg.2.2.1
  have hyg : guard y := hgt b hg.1 y hg.2.2.2
  have hnotboth : ¬ (target (b+1) x ∧ target (b+1) y) := by
    rintro ⟨hx,hy⟩
    exact hno ⟨by omega,hd.symm ▸ hx,hd.symm ▸ hy⟩
  constructor
  · intro hx
    have hy : ¬ target (b+1) y := fun hy => hnotboth ⟨hx,hy⟩
    exact hp ⟨⟨hbQ,hd,Or.inr ⟨hx,hy⟩⟩,hxg,hyg⟩
  · intro hy
    have hx : ¬ target (b+1) x := fun hx => hnotboth ⟨hx,hy⟩
    exact hp ⟨⟨hbQ,hd,Or.inl ⟨hx,hy⟩⟩,hxg,hyg⟩

section ActualRows
variable [Fintype V]

noncomputable def highRows (R : V → V → Prop) (ell : V → V → Bool)
    (guard : X → Prop) (target : ℕ → X → Prop) (Q : ℕ)
    (children : V → Bool → X) : Finset V := by
  classical
  exact Finset.univ.filter fun v => High guard target Q
    (guardFailures R ell guard children v).card (children v false) (children v true)

/-- Actual high rows admit the checkpoint's exact type tags. The associated
    typed tournament has precisely the stated failure budget at every vertex. -/
theorem actual_high_typed (R : V → V → Prop) (ell : V → V → Bool)
    (guard : X → Prop) (target : ℕ → X → Prop) (Q : ℕ) (hQ : Q ≤ 2)
    (children : V → Bool → X)
    (hgt : ∀ b, b ≤ Q → ∀ z, target b z → guard z) :
    ∃ tag : V → Fin 8,
      (∀ v ∈ highRows R ell guard target Q children,
        OfKind guard target Q (guardFailures R ell guard children v).card
          (children v false) (children v true) (tag v)) ∧
      (∀ v ∈ highRows R ell guard target Q children,
        (guardFailures R ell guard children v).card = budget (tag v)) ∧
      (∀ v ∈ highRows R ell guard target Q children,
        (outNeighbors R (highRows R ell guard target Q children) v).card ≤ budget (tag v)) := by
  classical
  let H := highRows R ell guard target Q children
  have hex : ∀ v ∈ H, ∃ k : Fin 8, OfKind guard target Q
      (guardFailures R ell guard children v).card (children v false) (children v true) k := by
    intro v hv
    exact (high_iff_exists_kind guard target Q _ hQ _ _).1 (Finset.mem_filter.mp hv).2
  let tag : V → Fin 8 := fun v => if hv : v ∈ H then Classical.choose (hex v hv) else 0
  have hk : ∀ v ∈ H, OfKind guard target Q (guardFailures R ell guard children v).card
      (children v false) (children v true) (tag v) := by
    intro v hv
    simpa only [tag,dif_pos hv] using Classical.choose_spec (hex v hv)
  have hcount : ∀ v ∈ H, (guardFailures R ell guard children v).card = budget (tag v) := by
    intro v hv
    exact ofKind_count guard target Q _ _ _ (tag v) (hk v hv)
  have hhigh : ∀ v ∈ H, ∀ c : Bool, guard (children v c) := by
    intro v hv c
    have hboth := high_guard_true guard target Q _ _ _ hgt (Finset.mem_filter.mp hv).2
    cases c
    · exact hboth.1
    · exact hboth.2
  refine ⟨tag,hk,hcount,?_⟩
  intro v hv
  rw [← hcount v hv]
  exact Finset.card_le_card (out_high_subset_failures R ell guard children H hhigh v)

theorem actual_high_card_le_seven (R : V → V → Prop) (hR : IsTournament R)
    (ell : V → V → Bool) (guard : X → Prop) (target : ℕ → X → Prop)
    (Q : ℕ) (hQ : Q ≤ 2) (children : V → Bool → X)
    (hgt : ∀ b, b ≤ Q → ∀ z, target b z → guard z) :
    (highRows R ell guard target Q children).card ≤ 7 := by
  obtain ⟨tag,_,_,hout⟩ := actual_high_typed R ell guard target Q hQ children hgt
  apply card_le_of_outdegree_le R hR _ 3
  intro v hv
  exact (hout v hv).trans (budget_le_three (tag v))

/-- The exact tag-prefix restrictions used by the executable enumeration follow
    from actual guard budgets. In particular q=0,1,2 gives limits 1,3,5. -/
theorem actual_positive_prefix_card_bound (R : V → V → Prop) (hR : IsTournament R)
    (ell : V → V → Bool) (guard : X → Prop) (target : ℕ → X → Prop)
    (Q : ℕ) (children : V → Bool → X)
    (hgt : ∀ b, b ≤ Q → ∀ z, target b z → guard z)
    (tag : V → Fin 8)
    (hcount : ∀ v ∈ highRows R ell guard target Q children,
      (guardFailures R ell guard children v).card = budget (tag v)) (q : ℕ) :
    ((highRows R ell guard target Q children).filter
      fun v => ThreeBoundQ2.positivePrefix q (tag v) = true).card ≤ 2*q+1 := by
  classical
  let pref := (highRows R ell guard target Q children).filter
    fun v => ThreeBoundQ2.positivePrefix q (tag v) = true
  apply positive_prefix_card_le R hR ell guard children pref q
  · intro v hv c
    have hvH := (Finset.mem_filter.mp hv).1
    have hh := high_guard_true guard target Q _ _ _ hgt (Finset.mem_filter.mp hvH).2
    cases c
    · exact hh.1
    · exact hh.2
  · intro v hv
    have hvH := (Finset.mem_filter.mp hv).1
    rw [hcount v hvH]
    exact positivePrefix_budget_le q (tag v) (Finset.mem_filter.mp hv).2

/-- The remaining global degree restriction in allowedTypes is also semantic. -/
theorem actual_high_budget_sum_bound (R : V → V → Prop) (hR : IsTournament R)
    (ell : V → V → Bool) (guard : X → Prop) (target : ℕ → X → Prop)
    (Q : ℕ) (children : V → Bool → X)
    (hgt : ∀ b, b ≤ Q → ∀ z, target b z → guard z)
    (tag : V → Fin 8)
    (hcount : ∀ v ∈ highRows R ell guard target Q children,
      (guardFailures R ell guard children v).card = budget (tag v)) :
    let H := highRows R ell guard target Q children
    H.card * (H.card-1) ≤ 2 * ∑ v ∈ H, ThreeBoundQ2.budget (tag v) := by
  classical
  let H := highRows R ell guard target Q children
  have hh : ∀ v ∈ H, ∀ c : Bool, guard (children v c) := by
    intro v hv c
    have hh := high_guard_true guard target Q _ _ _ hgt (Finset.mem_filter.mp hv).2
    cases c
    · exact hh.1
    · exact hh.2
  apply every_high_subset_budget_bound R hR ell guard children H
    (fun v => ThreeBoundQ2.budget (tag v)) hh
  · intro v hv
    exact le_of_eq (hcount v hv)
  · exact Finset.Subset.refl H

end ActualRows
end Q2CandidateTypes

#print axioms Q2CandidateTypes.high_iff_exists_unique_kind
#print axioms Q2CandidateTypes.positive_guard_overlap
#print axioms Q2CandidateTypes.pure_guard_next_both_false
#print axioms Q2CandidateTypes.actual_high_typed
#print axioms Q2CandidateTypes.actual_high_card_le_seven
#print axioms Q2CandidateTypes.actual_positive_prefix_card_bound
#print axioms Q2CandidateTypes.actual_high_budget_sum_bound


