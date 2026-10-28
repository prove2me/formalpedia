-- Prove2me | Definitions.Def_BS2_b3ba934b_FullProfileClosure
-- name    : BS2_b3ba934b_FullProfileClosure
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T04:05:58.378698+00:00
-- url     : https://prove2.me/theorems/e5bbb09e-e595-45dd-8233-e633bc241943
-- title:
--   Sensitivity separation: FullProfileClosure (complete source module)
-- statement:
--   Complete Lean source module `FullProfileClosure` from the two verified sensitivity separation proofs. The module supplies the definitions, auxiliary lemmas, and exact finite certificates used by its dependent modules. All original declarations and proof bodies are retained; only local import module paths are changed for Prove2Me. The final campaign goals are published separately as theorems with submitted solutions.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/FullProfileClosure.lean; original SHA-256 5a60de39b5ad6accffb5dbd5d6529c02c34ba478739e73e4c3db3c10e08132be; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

/- Soundness of the complete finite five-profile closure procedure.
The update schedule is the one in graded2_union_recurrence.IntegerModel.close.
It does not establish the raw sensitivity transfer preceding that procedure. -/
import Definitions.Def_BS2_b3ba934b_ProfileClosures
import Mathlib.Data.List.FinRange

set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option linter.unusedSectionVars false

namespace ThreeBoundFullProfile
open ThreeBoundProfiles
open scoped Classical
noncomputable section

variable {n : ℕ} {I : Type} [Fintype I]

inductive Coord (n : ℕ) where
  | a : Fin n → Fin n → Coord n
  | b : Fin n → Fin n → Coord n
  | m : Fin n → Fin n → Coord n
  | p : Fin n → Fin n → Coord n
  | d : Fin n → Fin n → Fin n → Coord n
  deriving DecidableEq

abbrev Profile (n : ℕ) := Coord n → ℕ

def next (j : Fin n) : Fin n :=
  if h : j.val+1 < n then ⟨j.val+1,h⟩ else j

def prev (j : Fin n) : Fin n := ⟨j.val-1,(Nat.sub_le _ _).trans_lt j.isLt⟩

theorem next_val (j : Fin n) (h : j.val+1 < n) : (next j).val = j.val+1 := by
  simp [next,h]

theorem self_le_next (j : Fin n) : j ≤ next j := by
  unfold next
  split_ifs <;> simp only [Fin.le_iff_val_le_val] <;> omega

theorem prev_le_self (j : Fin n) : prev j ≤ j := by
  exact Nat.sub_le _ _

theorem next_le_of_lt (i j : Fin n) (h : i < j) : next i ≤ j := by
  have hi : i.val+1 < n := by have hj := j.isLt; exact lt_of_le_of_lt h hj
  change (next i).val ≤ j.val
  rw [next_val i hi]
  exact h

theorem le_prev_of_lt (i j : Fin n) (h : i < j) : i ≤ prev j := by
  change i.val ≤ j.val-1
  have hh : i.val < j.val := h
  omega

theorem next_lt_n_of_lt (i j : Fin n) (h : i < j) : i.val+1 < n :=
  lt_of_le_of_lt h j.isLt

/-- Only the triangular and adjacent-gap coordinates carry an obligation.
The unused coordinates make in-place updates uncomplicated and harmless. -/
def Sem (F : Fin n → (I → Bool) → Bool) : Coord n → ℕ → Prop
  | .a i j, v => i ≤ j → ABound F i j v
  | .b i j, v => i ≤ j → BBound F i j v
  | .m i j, v => i ≤ j → j.val+1 < n → MBound F i j (next j) v
  | .p j l, v => j < l → PBound F j (next j) l v
  | .d i j l, v => i ≤ j → j < l → DBound F i j (next j) l v

def Upper (F : Fin n → (I → Bool) → Bool) (v : Profile n) : Prop :=
  ∀ c, Sem F c (v c)

theorem sem_mono (F : Fin n → (I → Bool) → Bool) (c : Coord n) (a b : ℕ)
    (hab : a ≤ b) (ha : Sem F c a) : Sem F c b := by
  cases c with
  | a i j => exact fun hij x hx => (ha hij x hx).trans hab
  | b i j => exact fun hij x hx => (ha hij x hx).trans hab
  | m i j => exact fun hij hn x hx hy => (ha hij hn x hx hy).trans hab
  | p j l => exact fun hjl x hx hy => (ha hjl x hx hy).trans hab
  | d i j l => exact fun hij hjl x hx hy => (ha hij hjl x hx hy).trans hab

theorem sem_min (F : Fin n → (I → Bool) → Bool) (c : Coord n) (a b : ℕ)
    (ha : Sem F c a) (hb : Sem F c b) : Sem F c (min a b) := by
  cases c with
  | a i j => exact fun hij => a_min F i j a b (ha hij) (hb hij)
  | b i j => exact fun hij => b_min F i j a b (ha hij) (hb hij)
  | m i j => exact fun hij hn => m_min F i j (next j) a b (ha hij hn) (hb hij hn)
  | p j l => exact fun hjl => p_min F j (next j) l a b (ha hjl) (hb hjl)
  | d i j l =>
      exact fun hij hjl => d_min F i j (next j) l a b (ha hij hjl) (hb hij hjl)

theorem upper_mono (F : Fin n → (I → Bool) → Bool) (v w : Profile n)
    (hvw : ∀ c, v c ≤ w c) (hv : Upper F v) : Upper F w :=
  fun c => sem_mono F c _ _ (hvw c) (hv c)

def meet (v w : Profile n) : Profile n := fun c => min (v c) (w c)

theorem meet_sound (F : Fin n → (I → Bool) → Bool) (v w : Profile n)
    (hv : Upper F v) (hw : Upper F w) : Upper F (meet v w) :=
  fun c => sem_min F c _ _ (hv c) (hw c)

/-- Each constructor is exactly one of the semantic closure rules. The index
conditions are part of the command, not assumed by the execution theorem. -/
inductive Rule (n : ℕ) where
  | aCond (i j : Fin n) (h : i < j)
  | aTarget (i j : Fin n) (h : i < j)
  | bTarget (i j : Fin n) (h : i < j)
  | bCond (i j : Fin n) (h : i < j)
  | mFromB (i j : Fin n) (h : i ≤ j) (hn : j.val+1 < n)
  | mTarget (i j : Fin n) (h : i < j) (hn : j.val+1 < n)
  | pFromA (j l : Fin n) (h : j < l)
  | pTarget (j l : Fin n) (h : j.val+1 < l.val)
  | dFromMP (i j l : Fin n) (h : i ≤ j) (hl : j < l)
  | dDown (i j l : Fin n) (h : i < j) (hl : j < l)
  | dUp (i j l : Fin n) (h : i ≤ j) (hl : j.val+1 < l.val)
  | bPartition (i j : Fin n) (h : i ≤ j) (hn : j.val+1 < n)
  | aPartition (j l : Fin n) (h : j < l)

def Rule.target : Rule n → Coord n
  | .aCond i j _ | .aTarget i j _ => .a i j
  | .bTarget i j _ | .bCond i j _ => .b i j
  | .mFromB i j _ _ | .mTarget i j _ _ => .m i j
  | .pFromA j l _ | .pTarget j l _ => .p j l
  | .dFromMP i j l _ _ | .dDown i j l _ _ | .dUp i j l _ _ => .d i j l
  | .bPartition i j _ _ => .b i j
  | .aPartition j l _ => .a (next j) l

def Rule.value (v : Profile n) : Rule n → ℕ
  | .aCond i j _ => v (.a (next i) j)
  | .aTarget i j _ => v (.a i (prev j))
  | .bTarget i j _ => v (.b (next i) j)
  | .bCond i j _ => v (.b i (prev j))
  | .mFromB i j _ _ => v (.b i j)
  | .mTarget i j _ _ => v (.m (next i) j)
  | .pFromA j l _ => v (.a (next j) l)
  | .pTarget j l _ => v (.p j (prev l))
  | .dFromMP i j l _ _ => v (.m i j)+v (.p j l)
  | .dDown i j l _ _ => v (.d (next i) j l)
  | .dUp i j l _ _ => v (.d i j (prev l))
  | .bPartition i j _ _ => max (v (.b i (next j))) (v (.m i j))
  | .aPartition j l _ => max (v (.a j l)) (v (.p j l))

theorem rule_sound (F : Fin n → (I → Bool) → Bool) (hF : Nested F)
    (v : Profile n) (hv : Upper F v) (r : Rule n) :
    Sem F r.target (r.value v) := by
  cases r with
  | aCond i j h =>
      intro _
      exact a_condition_weaken F hF i (next i) j (self_le_next i) _
        (hv (.a (next i) j) (next_le_of_lt i j h))
  | aTarget i j h =>
      intro _
      exact a_target_strengthen F hF i (prev j) j (prev_le_self j) _
        (hv (.a i (prev j)) (le_prev_of_lt i j h))
  | bTarget i j h =>
      intro _
      exact b_target_weaken F hF i (next i) j (self_le_next i) _
        (hv (.b (next i) j) (next_le_of_lt i j h))
  | bCond i j h =>
      intro _
      exact b_condition_strengthen F hF i (prev j) j (prev_le_self j) _
        (hv (.b i (prev j)) (le_prev_of_lt i j h))
  | mFromB i j h hn =>
      intro _ _
      exact m_of_b F i j (next j) _ (hv (.b i j) h)
  | mTarget i j h hn =>
      intro _ _
      exact m_target_weaken F hF i (next i) j (next j) (self_le_next i) _
        (hv (.m (next i) j) (next_le_of_lt i j h) hn)
  | pFromA j l h =>
      intro _
      exact p_of_a F j (next j) l _ (hv (.a (next j) l) (next_le_of_lt j l h))
  | pTarget j l h =>
      have hj : j < prev l := by change j.val < l.val-1; omega
      intro _
      exact p_target_strengthen F hF j (next j) (prev l) l
        (prev_le_self l) _ (hv (.p j (prev l)) hj)
  | dFromMP i j l h hl =>
      intro _ _
      exact d_of_m_add_p F i j (next j) l _ _
        (hv (.m i j) h (next_lt_n_of_lt j l hl)) (hv (.p j l) hl)
  | dDown i j l h hl =>
      intro _ _
      exact d_down_target_weaken F hF i (next i) j (next j) l (self_le_next i) _
        (hv (.d (next i) j l) (next_le_of_lt i j h) hl)
  | dUp i j l h hl =>
      have hj : j < prev l := by change j.val < l.val-1; omega
      intro _ _
      exact d_up_target_strengthen F hF i j (next j) (prev l) l
        (prev_le_self l) _ (hv (.d i j (prev l)) h hj)
  | bPartition i j h hn =>
      intro _
      exact b_partition F i j (next j) _ _
        (hv (.b i (next j)) (h.trans (self_le_next j))) (hv (.m i j) h hn)
  | aPartition j l h =>
      intro _
      exact a_partition F j (next j) l _ _ (hv (.a j l) h.le) (hv (.p j l) h)

def applyRule (tighten : Bool) (v : Profile n) (r : Rule n) : Profile n :=
  fun c => if c = r.target then
    if tighten then min (v c) (r.value v) else r.value v
    else v c

theorem applyRule_sound (F : Fin n → (I → Bool) → Bool) (hF : Nested F)
    (tighten : Bool) (v : Profile n) (hv : Upper F v) (r : Rule n) :
    Upper F (applyRule tighten v r) := by
  intro c
  by_cases hc : c = r.target
  · subst c
    cases tighten with
    | false => simpa only [applyRule, if_pos rfl, Bool.false_eq_true, if_false, if_true]
        using rule_sound F hF v hv r
    | true => simpa only [applyRule, if_pos rfl, if_true]
        using sem_min F r.target _ _ (hv r.target) (rule_sound F hF v hv r)
  · simpa only [applyRule, if_neg hc] using hv c

def runRules (tighten : Bool) : List (Rule n) → Profile n → Profile n
  | [], v => v
  | r::rs, v => runRules tighten rs (applyRule tighten v r)

theorem runRules_sound (F : Fin n → (I → Bool) → Bool) (hF : Nested F)
    (tighten : Bool) (rs : List (Rule n)) (v : Profile n) (hv : Upper F v) :
    Upper F (runRules tighten rs v) := by
  induction rs generalizing v with
  | nil => exact hv
  | cons r rs ih => exact ih _ (applyRule_sound F hF tighten v hv r)

/-- B envelopes: reverse traversal gives max of the final B bound and all
intervening M gaps. Keeping a separate envelope preserves the Python pass's
accumulator exactly, before its minimum with the original B entries. -/
def bRules (n : ℕ) : List (Rule n) :=
  (List.finRange n).flatMap fun i =>
    (List.finRange n).reverse.filterMap fun j =>
      if h : i ≤ j ∧ j.val+1 < n then some (.bPartition i j h.1 h.2) else none

/-- A envelopes: forward traversal gives max of the initial A bound and all
preceding P gaps, before its minimum with the original A entries. -/
def aRules (n : ℕ) : List (Rule n) :=
  (List.finRange n).flatMap fun l =>
    (List.finRange n).filterMap fun j =>
      if h : j < l then some (.aPartition j l h) else none

/-- Triangular A/B ordering, traversed by increasing interval length. -/
def orderRules (n : ℕ) : List (Rule n) :=
  (List.range n).flatMap fun gap =>
    (List.finRange n).flatMap fun i =>
      if h : 0 < gap ∧ i.val+gap < n then
        let j : Fin n := ⟨i.val+gap,h.2⟩
        have hij : i < j := by change i.val < i.val+gap; omega
        [.aCond i j hij,.aTarget i j hij,.bTarget i j hij,.bCond i j hij]
      else []

def mRules (j : Fin n) (hn : j.val+1 < n) : List (Rule n) :=
  (List.finRange n).reverse.flatMap fun i =>
    if h : i ≤ j then
      [.mFromB i j h hn] ++ (if hi : i < j then [.mTarget i j hi hn] else [])
    else []

def pRules (j : Fin n) : List (Rule n) :=
  (List.finRange n).flatMap fun l =>
    if h : j < l then
      [.pFromA j l h] ++ (if hl : j.val+1 < l.val then [.pTarget j l hl] else [])
    else []

def dRules (j : Fin n) : List (Rule n) :=
  (List.finRange n).reverse.flatMap fun i =>
    (List.finRange n).flatMap fun l =>
      if h : i ≤ j ∧ j < l then
        [.dFromMP i j l h.1 h.2] ++
          (if hi : i < j then [.dDown i j l hi h.2] else []) ++
          (if hl : j.val+1 < l.val then [.dUp i j l h.1 hl] else [])
      else []

def gapRules (n : ℕ) : List (Rule n) :=
  (List.finRange n).flatMap fun j =>
    if hn : j.val+1 < n then mRules j hn ++ pRules j ++ dRules j else []

/-- The complete closure procedure, in the same order as the exact verifier.
The first two passes use envelopes; all remaining updates use minima. -/
def close (v : Profile n) : Profile n :=
  let w₁ := meet v (runRules false (bRules n) v)
  let w₂ := meet w₁ (runRules false (aRules n) w₁)
  runRules true (gapRules n) (runRules true (orderRules n) w₂)

theorem close_sound (F : Fin n → (I → Bool) → Bool) (hF : Nested F)
    (v : Profile n) (hv : Upper F v) : Upper F (close v) := by
  unfold close
  apply runRules_sound F hF
  apply runRules_sound F hF
  apply meet_sound F
  · exact meet_sound F _ _ hv (runRules_sound F hF false (bRules n) v hv)
  · apply runRules_sound F hF
    exact meet_sound F _ _ hv (runRules_sound F hF false (bRules n) v hv)

theorem sensitivity_le_closed_diagonal (F : Fin n → (I → Bool) → Bool)
    (hF : Nested F) (v : Profile n) (hv : Upper F v) (i : Fin n) :
    OAI.Paper320.sensitivity (F i) ≤
      max (close v (.a i i)) (close v (.b i i)) :=
  sensitivity_le_diagonal_max F i _ _
    (close_sound F hF v hv (.a i i) le_rfl)
    (close_sound F hF v hv (.b i i) le_rfl)

end
end ThreeBoundFullProfile

#print axioms ThreeBoundFullProfile.close_sound
#print axioms ThreeBoundFullProfile.sensitivity_le_closed_diagonal


