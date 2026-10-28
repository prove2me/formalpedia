-- Prove2me | Definitions.Def_BS2_b3ba934b_ClosureCertificate
-- name    : BS2_b3ba934b_ClosureCertificate
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T05:46:17.181179+00:00
-- url     : https://prove2.me/theorems/58a73fbd-ad4b-4bd7-a63e-fb5b51a079b4
-- title:
--   Sensitivity separation: ClosureCertificate (complete source module)
-- statement:
--   Complete Lean source module `ClosureCertificate` from the two verified sensitivity separation proofs. The module supplies the definitions, auxiliary lemmas, and exact finite certificates used by its dependent modules. All original declarations and proof bodies are retained; only local import module paths are changed for Prove2Me. The final campaign goals are published separately as theorems with submitted solutions.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/ClosureCertificate.lean; original SHA-256 bc6b5758158196e25c384f9b6d527a2e020b577675a25c6d2a48edc187cf4af5; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

/- A small trusted checker for exact closure certificates.

Each node cites either an input bound or one of the already proved semantic
closure rules, with references strictly earlier in the finite program. The
checker validates coordinates and integer inequalities. A successful check
therefore proves a semantic upper profile for every natural scaling of the
input. No executable output is used as an unverified premise. -/
import Definitions.Def_BS2_b3ba934b_FlatProfiles
import Definitions.Def_BS2_b3ba934b_ClosureHomogeneity

set_option autoImplicit false
set_option maxHeartbeats 3000000

namespace ThreeBoundNumeric.ClosureCertificate
open ThreeBoundProfiles ThreeBoundFullProfile

variable {n : ℕ}

def source₀ : Rule n → Coord n
  | .aCond i j _ => .a (next i) j
  | .aTarget i j _ => .a i (prev j)
  | .bTarget i j _ => .b (next i) j
  | .bCond i j _ => .b i (prev j)
  | .mFromB i j _ _ => .b i j
  | .mTarget i j _ _ => .m (next i) j
  | .pFromA j l _ => .a (next j) l
  | .pTarget j l _ => .p j (prev l)
  | .dFromMP i j l _ _ => .m i j
  | .dDown i j l _ _ => .d (next i) j l
  | .dUp i j l _ _ => .d i j (prev l)
  | .bPartition i j _ _ => .b i (next j)
  | .aPartition j l _ => .a j l

def source₁ (r : Rule n) : Coord n :=
  match r with
  | .dFromMP _ j l _ _ => .p j l
  | .bPartition i j _ _ => .m i j
  | .aPartition j l _ => .p j l
  | _ => source₀ r

def combine : Rule n → ℕ → ℕ → ℕ
  | .dFromMP .., x, y => x+y
  | .bPartition .., x, y => max x y
  | .aPartition .., x, y => max x y
  | _, x, _ => x

theorem combine_scale (r : Rule n) (c x y : ℕ) :
    combine r (c*x) (c*y) = c*combine r x y := by
  cases r <;> simp [combine,Nat.mul_add,Nat.mul_max_mul_left]

theorem rule_sound_two {I : Type} [Fintype I]
    (F : Fin n → (I → Bool) → Bool) (hF : Nested F) (r : Rule n)
    (x y : ℕ) (hx : Sem F (source₀ r) x) (hy : Sem F (source₁ r) y) :
    Sem F r.target (combine r x y) := by
  cases r with
  | aCond i j h =>
      intro _
      exact a_condition_weaken F hF i (next i) j (self_le_next i) _
        (hx (next_le_of_lt i j h))
  | aTarget i j h =>
      intro _
      exact a_target_strengthen F hF i (prev j) j (prev_le_self j) _
        (hx (le_prev_of_lt i j h))
  | bTarget i j h =>
      intro _
      exact b_target_weaken F hF i (next i) j (self_le_next i) _
        (hx (next_le_of_lt i j h))
  | bCond i j h =>
      intro _
      exact b_condition_strengthen F hF i (prev j) j (prev_le_self j) _
        (hx (le_prev_of_lt i j h))
  | mFromB i j h hn =>
      intro _ _
      exact m_of_b F i j (next j) _ (hx h)
  | mTarget i j h hn =>
      intro _ _
      exact m_target_weaken F hF i (next i) j (next j) (self_le_next i) _
        (hx (next_le_of_lt i j h) hn)
  | pFromA j l h =>
      intro _
      exact p_of_a F j (next j) l _ (hx (next_le_of_lt j l h))
  | pTarget j l h =>
      have hj : j < prev l := by change j.val < l.val-1; omega
      intro _
      exact p_target_strengthen F hF j (next j) (prev l) l (prev_le_self l) _ (hx hj)
  | dFromMP i j l h hl =>
      intro _ _
      exact d_of_m_add_p F i j (next j) l _ _
        (hx h (next_lt_n_of_lt j l hl)) (hy hl)
  | dDown i j l h hl =>
      intro _ _
      exact d_down_target_weaken F hF i (next i) j (next j) l (self_le_next i) _
        (hx (next_le_of_lt i j h) hl)
  | dUp i j l h hl =>
      have hj : j < prev l := by change j.val < l.val-1; omega
      intro _ _
      exact d_up_target_strengthen F hF i j (next j) (prev l) l (prev_le_self l) _
        (hx h hj)
  | bPartition i j h hn =>
      intro _
      exact b_partition F i j (next j) _ _
        (hx (h.trans (self_le_next j))) (hy h hn)
  | aPartition j l h =>
      intro _
      exact a_partition F j (next j) l _ _ (hx h.le) (hy h)

inductive Reason (n : ℕ) where
  | input
  | step : Rule n → ℕ → ℕ → Reason n

structure Node (n : ℕ) where
  coord : Coord n
  value : ℕ
  reason : Reason n

inductive Table (α : Type) where
  | leaf : α → Table α
  | branch : ℕ → Table α → Table α → Table α

def Table.get {α : Type} : Table α → ℕ → α
  | .leaf v, _ => v
  | .branch cut left right, i => if i<cut then left.get i else right.get i

inductive PointerTable where
  | identity
  | fixed : ℕ → PointerTable
  | branch : ℕ → PointerTable → PointerTable → PointerTable

def PointerTable.get : PointerTable → ℕ → ℕ
  | .identity, i => i
  | .fixed v, _ => v
  | .branch cut left right, i => if i<cut then left.get i else right.get i

def checkNode (input : Profile n) (nodes : ℕ → Node n) (k : ℕ) : Bool :=
  let node := nodes k
  match node.reason with
  | .input => input node.coord ≤ node.value
  | .step r a b =>
      node.coord = r.target ∧ a<k ∧ b<k ∧
      (nodes a).coord = source₀ r ∧ (nodes b).coord = source₁ r ∧
      combine r (nodes a).value (nodes b).value ≤ node.value

def checkNodes (input : Profile n) (nodes : ℕ → Node n) (count : ℕ) : Bool :=
  (List.range count).all (checkNode input nodes)

theorem nodes_sound {I : Type} [Fintype I]
    (F : Fin n → (I → Bool) → Bool) (hF : Nested F)
    (input : Profile n) (nodes : ℕ → Node n) (count c : ℕ)
    (hi : Upper F (scale c input))
    (hn : ∀ k, k<count → checkNode input nodes k = true) :
    ∀ k, k<count → Sem F (nodes k).coord (c*(nodes k).value) := by
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
      intro hk
      have hcheck := hn k hk
      cases hr : (nodes k).reason with
      | input =>
          have hle : input (nodes k).coord ≤ (nodes k).value := by
            simpa [checkNode,hr] using hcheck
          exact sem_mono F (nodes k).coord _ _ (Nat.mul_le_mul_left c hle) (hi _)
      | step r a b =>
          have hs : (nodes k).coord = r.target ∧ a<k ∧ b<k ∧
              (nodes a).coord = source₀ r ∧ (nodes b).coord = source₁ r ∧
              combine r (nodes a).value (nodes b).value ≤ (nodes k).value := by
            simpa [checkNode,hr] using hcheck
          obtain ⟨hcoord,ha,hb,hca,hcb,hvalue⟩ := hs
          have hsa : Sem F (source₀ r) (c*(nodes a).value) := by
            rw [← hca]
            exact ih a ha (ha.trans hk)
          have hsb : Sem F (source₁ r) (c*(nodes b).value) := by
            rw [← hcb]
            exact ih b hb (hb.trans hk)
          rw [hcoord]
          apply sem_mono F r.target _ _ (Nat.mul_le_mul_left c hvalue)
          rw [← combine_scale]
          exact rule_sound_two F hF r _ _ hsa hsb

theorem checkNodes_sound {I : Type} [Fintype I]
    (F : Fin n → (I → Bool) → Bool) (hF : Nested F)
    (input : Profile n) (nodes : ℕ → Node n) (count c : ℕ)
    (hi : Upper F (scale c input))
    (hc : checkNodes input nodes count = true) :
    ∀ k, k<count → Sem F (nodes k).coord (c*(nodes k).value) :=
  nodes_sound F hF input nodes count c hi (fun k hk=>
    List.all_eq_true.mp hc k (List.mem_range.mpr hk))

def checkInterval (p : ℕ → Bool) (a b : ℕ) : Bool :=
  (interval a b).all p

theorem checkInterval_sound (p : ℕ → Bool) (a b : ℕ)
    (h : checkInterval p a b = true) (k : ℕ) (ha : a≤k) (hb : k<b) : p k=true :=
  List.all_eq_true.mp h k (mem_interval.mpr ⟨ha,hb⟩)

theorem checkInterval_join (p : ℕ → Bool) (a b c : ℕ)
    (hab : checkInterval p a b=true) (hbc : checkInterval p b c=true) :
    checkInterval p a c=true := by
  apply List.all_eq_true.mpr
  intro k hk
  obtain ⟨ha,hc⟩ := mem_interval.mp hk
  by_cases hb : k<b
  · exact checkInterval_sound p a b hab k ha hb
  · exact checkInterval_sound p b c hbc k (by omega) hc

def checkOutputAt (nodes : ℕ → Node n) (count : ℕ)
    (outIndex : Coord n → ℕ) (output : Profile n) (coord : Coord n) : Bool :=
  let k := outIndex coord
  k<count ∧ (nodes k).coord=coord ∧ (nodes k).value≤output coord

theorem outputAt_sound {I : Type} [Fintype I]
    (F : Fin n → (I → Bool) → Bool) (hF : Nested F)
    (input output : Profile n) (nodes : ℕ → Node n) (count c : ℕ)
    (outIndex : Coord n → ℕ) (coord : Coord n)
    (hi : Upper F (scale c input))
    (hn : ∀ k, k<count → checkNode input nodes k=true)
    (ho : checkOutputAt nodes count outIndex output coord=true) :
    Sem F coord (c*output coord) := by
  have h : outIndex coord<count ∧ (nodes (outIndex coord)).coord=coord ∧
      (nodes (outIndex coord)).value≤output coord := of_decide_eq_true ho
  obtain ⟨hlt,heq,hle⟩ := h
  have hs := nodes_sound F hF input nodes count c hi hn (outIndex coord) hlt
  rw [heq] at hs
  exact sem_mono F coord _ _ (Nat.mul_le_mul_left c hle) hs

def checkOutput (nodes : ℕ → Node n) (count : ℕ)
    (outIndex : Coord n → ℕ) (output : Profile n) : Bool :=
  (validCoords n).all fun coord =>
    let k := outIndex coord
    k<count ∧ (nodes k).coord=coord ∧ (nodes k).value≤output coord

theorem checked_closure {I : Type} [Fintype I]
    (F : Fin n → (I → Bool) → Bool) (hF : Nested F)
    (input output : Profile n) (nodes : ℕ → Node n) (count : ℕ)
    (outIndex : Coord n → ℕ) (c : ℕ)
    (hi : Upper F (scale c input))
    (hn : checkNodes input nodes count = true)
    (ho : checkOutput nodes count outIndex output = true) :
    Upper F (scale c output) := by
  intro coord
  by_cases hc : valid coord
  · have hcheck := List.all_eq_true.mp ho coord ((mem_validCoords coord).mpr hc)
    have hout : outIndex coord<count ∧ (nodes (outIndex coord)).coord=coord ∧
        (nodes (outIndex coord)).value≤output coord := of_decide_eq_true hcheck
    obtain ⟨hlt,heq,hle⟩ := hout
    have hs := checkNodes_sound F hF input nodes count c hi hn (outIndex coord) hlt
    rw [heq] at hs
    exact sem_mono F coord _ _ (Nat.mul_le_mul_left c hle) hs
  · exact sem_of_not_valid F coord _ hc

end ThreeBoundNumeric.ClosureCertificate

#print axioms ThreeBoundNumeric.ClosureCertificate.checked_closure


