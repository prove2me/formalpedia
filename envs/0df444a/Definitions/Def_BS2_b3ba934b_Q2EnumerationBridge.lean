-- Prove2me | Definitions.Def_BS2_b3ba934b_Q2EnumerationBridge
-- name    : BS2_b3ba934b_Q2EnumerationBridge
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T04:24:13.461908+00:00
-- url     : https://prove2.me/theorems/2c4ccc0b-0823-475f-838d-e0d4dafe1474
-- title:
--   Sensitivity separation: Q2EnumerationBridge (complete source module)
-- statement:
--   Complete Lean source module `Q2EnumerationBridge` from the two verified sensitivity separation proofs. The module supplies the definitions, auxiliary lemmas, and exact finite certificates used by its dependent modules. All original declarations and proof bodies are retained; only local import module paths are changed for Prove2Me. The final campaign goals are published separately as theorems with submitted solutions.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Q2EnumerationBridge.lean; original SHA-256 03a4fb36b007fff28d4e49eea18e6afba235c6589b867de536205b797b906503; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

/-
Canonical numbering and actual tournament-degree bridge for the executable
q2 enumerator.  This connects combinatorial coverage to finite tournaments,
without replacing sensitivity charging by numerical assumptions.
-/
import Definitions.Def_BS2_b3ba934b_Q2CandidateTypes
import Mathlib.Data.Prod.Lex
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Algebra.BigOperators.Fin

set_option autoImplicit false
set_option maxHeartbeats 3000000

namespace ThreeBoundQ2
open scoped Classical BigOperators

theorem exists_sorted_numbering {V : Type} [Fintype V] (tag : V → Kind) :
    ∃ e : Fin (Fintype.card V) ≃ V, Monotone (fun i => tag (e i)) := by
  classical
  let idx := Fintype.equivFin V
  let key : V → Kind ×ₗ Fin (Fintype.card V) := fun v => toLex (tag v,idx v)
  have hinj : Function.Injective key := by
    intro a b h
    apply idx.injective
    exact congrArg (fun p => (ofLex p).2) h
  letI : LinearOrder V := LinearOrder.lift' key hinj
  let e := Fintype.orderIsoFinOfCardEq V rfl
  refine ⟨e.toEquiv, ?_⟩
  intro i j hij
  exact Prod.Lex.monotone_fst (key (e i)) (key (e j)) (e.monotone hij)

@[simp] theorem mem_edges {n : ℕ} (i j : Fin n) :
    (i,j) ∈ edges n ↔ i < j := by
  simp [edges]

theorem edges_nodup (n : ℕ) : (edges n).Nodup := by
  unfold edges
  apply List.nodup_flatMap.mpr
  constructor
  · intro i _
    exact ((List.nodup_finRange n).filter _).map (fun _ _ h => congrArg Prod.snd h)
  · apply (List.nodup_finRange n).imp
    intro a b hab p hp hq
    obtain ⟨i, _, hi⟩ := List.mem_map.mp hp
    obtain ⟨j, _, hj⟩ := List.mem_map.mp hq
    exact hab (congrArg Prod.fst (hi.trans hj.symm))

def orientationBits {n : ℕ} (R : Fin n → Fin n → Prop) [DecidableRel R] : List Bool :=
  (edges n).map fun e => decide (R e.2 e.1)

def orientEdge {n : ℕ} (R : Fin n → Fin n → Prop) [DecidableRel R]
    (e : Fin n × Fin n) : Fin n × Fin n :=
  if R e.2 e.1 then e.swap else e

theorem directedEdges_map {V : Type} (es : List (V × V)) (d : V × V → Bool) :
    directedEdges es (es.map d) = es.map (fun e => if d e then e.swap else e) := by
  induction es with
  | nil => rfl
  | cons e es ih =>
      change (if d e then e.swap else e) :: directedEdges es (es.map d) =
        (if d e then e.swap else e) :: es.map (fun e => if d e then e.swap else e)
      rw [ih]

theorem directedEdges_orientation {n : ℕ} (R : Fin n → Fin n → Prop) [DecidableRel R] :
    directedEdges (edges n) (orientationBits R) = (edges n).map (orientEdge R) := by
  unfold orientationBits
  rw [directedEdges_map]
  congr 1
  funext e
  simp [orientEdge]

theorem orientEdge_injective_on {n : ℕ} (R : Fin n → Fin n → Prop) [DecidableRel R]
    (a b : Fin n × Fin n) (ha : a ∈ edges n) (hb : b ∈ edges n)
    (he : orientEdge R a = orientEdge R b) : a = b := by
  rcases a with ⟨a₁,a₂⟩
  rcases b with ⟨b₁,b₂⟩
  have ha := (mem_edges a₁ a₂).1 ha
  have hb := (mem_edges b₁ b₂).1 hb
  by_cases h₁ : R a₂ a₁ <;> by_cases h₂ : R b₂ b₁ <;>
    simp only [orientEdge, h₁, h₂, ↓reduceIte, Prod.swap, Prod.mk.injEq] at he
  · exact Prod.ext he.2 he.1
  · rcases he with ⟨rfl,rfl⟩
    exact False.elim (lt_asymm ha hb)
  · rcases he with ⟨rfl,rfl⟩
    exact False.elim (lt_asymm ha hb)
  · exact Prod.ext he.1 he.2

theorem directedEdges_nodup {n : ℕ} (R : Fin n → Fin n → Prop) [DecidableRel R] :
    (directedEdges (edges n) (orientationBits R)).Nodup := by
  rw [directedEdges_orientation]
  exact (edges_nodup n).map_on (fun a ha b hb he => orientEdge_injective_on R a b ha hb he)

theorem mem_directedEdges {n : ℕ} (R : Fin n → Fin n → Prop) [DecidableRel R]
    (hR : TournamentHighRows.IsTournament R) (v w : Fin n) :
    (v,w) ∈ directedEdges (edges n) (orientationBits R) ↔ R v w := by
  rw [directedEdges_orientation, List.mem_map]
  constructor
  · rintro ⟨⟨i,j⟩, he, hj⟩
    have hij := (mem_edges i j).1 he
    by_cases hr : R j i
    · simp only [orientEdge, hr, ↓reduceIte, Prod.swap, Prod.mk.injEq] at hj
      rcases hj with ⟨rfl,rfl⟩
      exact hr
    · simp only [orientEdge, hr, ↓reduceIte, Prod.mk.injEq] at hj
      rcases hj with ⟨rfl,rfl⟩
      exact (hR.orient _ _ (ne_of_lt hij)).2 hr
  · intro hvw
    have hvwne : v ≠ w := by
      intro h
      subst w
      exact hR.loopless v hvw
    rcases lt_or_gt_of_ne hvwne with hlt | hgt
    · have hnot : ¬ R w v := (hR.orient v w hvwne).1 hvw
      exact ⟨(v,w), (mem_edges v w).2 hlt, by simp [orientEdge, hnot]⟩
    · exact ⟨(w,v), (mem_edges w v).2 hgt, by simp [orientEdge, hvw]⟩

theorem outCount_eq_countP {V : Type} [DecidableEq V]
    (es : List (V × V)) (ds : List Bool) (v : V) :
    outCount es ds v = (directedEdges es ds).countP (fun e => e.1 = v) := by
  induction es generalizing ds with
  | nil => simp [outCount, directedEdges]
  | cons e es ih =>
      cases ds with
      | nil => simp [outCount, directedEdges]
      | cons d ds =>
          cases d
          · change (if e.1 = v then 1 else 0) + outCount es ds v =
              (e :: directedEdges es ds).countP (fun e => e.1 = v)
            rw [ih]
            by_cases h : e.1 = v <;> simp [List.countP_cons, h, Nat.add_comm]
          · change (if e.2 = v then 1 else 0) + outCount es ds v =
              (e.swap :: directedEdges es ds).countP (fun e => e.1 = v)
            rw [ih]
            by_cases h : e.2 = v <;> simp [List.countP_cons, h, Nat.add_comm]

theorem outCount_orientation_eq_card {n : ℕ} (R : Fin n → Fin n → Prop)
    [DecidableRel R] (hR : TournamentHighRows.IsTournament R) (v : Fin n) :
    outCount (edges n) (orientationBits R) v =
      ((Finset.univ : Finset (Fin n)).filter (R v)).card := by
  classical
  rw [outCount_eq_countP, ← (directedEdges_nodup R).card_eq_countP]
  apply Finset.card_bij (fun e _ => e.2)
  · intro e he
    obtain ⟨hed, hef⟩ := Finset.mem_filter.mp he
    have hr := (mem_directedEdges R hR e.1 e.2).1 (List.mem_toFinset.mp hed)
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simpa [hef] using hr⟩
  · intro a ha b hb hab
    have haf := (Finset.mem_filter.mp ha).2
    have hbf := (Finset.mem_filter.mp hb).2
    exact Prod.ext (haf.trans hbf.symm) hab
  · intro w hw
    have hr := (Finset.mem_filter.mp hw).2
    exact ⟨(v,w), Finset.mem_filter.mpr
      ⟨List.mem_toFinset.mpr ((mem_directedEdges R hR v w).2 hr), rfl⟩, rfl⟩

theorem card_filter_equiv {A B : Type} [Fintype A] [Fintype B]
    (e : A ≃ B) (p : B → Prop) [DecidablePred p] :
    ((Finset.univ : Finset A).filter fun a => p (e a)).card =
      ((Finset.univ : Finset B).filter p).card := by
  classical
  apply Finset.card_bij (fun a _ => e a)
  · intro a ha
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp ha).2⟩
  · intro a _ b _ hab
    exact e.injective hab
  · intro b hb
    exact ⟨e.symm b, by simpa using hb, e.apply_symm_apply b⟩

theorem length_filter_ofFn {A : Type} {n : ℕ} (f : Fin n → A) (p : A → Bool) :
    ((List.ofFn f).filter p).length =
      ((Finset.univ : Finset (Fin n)).filter fun i => p (f i) = true).card := by
  rw [List.ofFn_eq_map, ← List.countP_eq_length_filter, List.countP_map]
  symm
  simpa [Function.comp_def] using
    (List.nodup_finRange n).card_eq_countP (P := fun i => p (f i) = true)

/-- Every actual finite typed tournament satisfying the necessary q2 bounds
    has a sorted numbering whose exact 29-field record occurs in the proved
    executable table.  No orientation count or record count is assumed. -/
theorem typed_tournament_covered {V : Type} [Fintype V]
    (R : V → V → Prop) (hR : TournamentHighRows.IsTournament R) (tag : V → Kind)
    (hn : Fintype.card V ≤ 7)
    (hsum : Fintype.card V * (Fintype.card V - 1) / 2 ≤ ∑ v, budget (tag v))
    (hp : ∀ q, q ≤ 2 →
      ((Finset.univ : Finset V).filter fun v => positivePrefix q (tag v) = true).card ≤ 2*q+1)
    (hb : ∀ v, ((Finset.univ : Finset V).filter (R v)).card ≤ budget (tag v)) :
    ∃ (ts : List Kind) (ds : List Bool) (e : Fin ts.length ≃ V),
      ts.Pairwise (· ≤ ·) ∧
      (∀ i, ts.get i = tag (e i)) ∧
      ds = orientationBits (fun i j => R (e i) (e j)) ∧
      record (ts,ds) ∈ records := by
  classical
  obtain ⟨e₀, he₀⟩ := exists_sorted_numbering tag
  let ts := List.ofFn fun i => tag (e₀ i)
  have hlen : ts.length = Fintype.card V := List.length_ofFn
  let e : Fin ts.length ≃ V := (finCongr hlen).trans e₀
  have hget : ∀ i, ts.get i = tag (e i) := by
    intro i
    simp [ts, e, List.get_eq_getElem]
    apply congrArg (fun j => tag (e₀ j))
    apply Fin.ext
    rfl
  have hsorted : ts.Pairwise (· ≤ ·) := by
    apply List.pairwise_ofFn.mpr
    intro i j hij
    exact he₀ hij.le
  let R' : Fin ts.length → Fin ts.length → Prop := fun i j => R (e i) (e j)
  have hR' : TournamentHighRows.IsTournament R' := by
    constructor
    · intro i
      exact hR.loopless (e i)
    · intro i j hij
      exact hR.orient (e i) (e j) (fun h => hij (e.injective h))
  have hsum' : (ts.map budget).sum = ∑ v, budget (tag v) := by
    simp only [ts, List.map_ofFn, List.sum_ofFn]
    exact e₀.sum_comp (fun v => budget (tag v))
  have hp' (q : ℕ) : (ts.filter (positivePrefix q)).length =
      ((Finset.univ : Finset V).filter fun v => positivePrefix q (tag v) = true).card := by
    rw [length_filter_ofFn]
    exact card_filter_equiv e₀ (fun v => positivePrefix q (tag v) = true)
  have ht : allowedTypes ts := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · simpa only [hlen, hsum'] using hsum
    · rw [hp']
      exact hp 0 (by decide)
    · rw [hp']
      exact hp 1 (by decide)
    · rw [hp']
      exact hp 2 (by decide)
  refine ⟨ts, orientationBits R', e, hsorted, hget, rfl, ?_⟩
  apply records_complete ts (orientationBits R')
  · simpa only [hlen] using hn
  · exact hsorted
  · exact ht
  · simp [orientationBits]
  · intro i
    rw [outCount_orientation_eq_card R' hR', hget]
    have hc := card_filter_equiv e (fun v => R (e i) v)
    exact hc ▸ hb (e i)

end ThreeBoundQ2

#print axioms ThreeBoundQ2.exists_sorted_numbering
#print axioms ThreeBoundQ2.outCount_orientation_eq_card
#print axioms ThreeBoundQ2.typed_tournament_covered


