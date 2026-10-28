-- Prove2me | Definitions.Def_BS2_b3ba934b_GlobalAccounting
-- name    : BS2_b3ba934b_GlobalAccounting
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T04:25:01.084578+00:00
-- url     : https://prove2.me/theorems/e109e634-5063-4d22-8fbd-6dd8ed90293b
-- title:
--   Sensitivity separation: GlobalAccounting (complete source module)
-- statement:
--   Complete Lean source module `GlobalAccounting` from the two verified sensitivity separation proofs. The module supplies the definitions, auxiliary lemmas, and exact finite certificates used by its dependent modules. All original declarations and proof bodies are retained; only local import module paths are changed for Prove2Me. The final campaign goals are published separately as theorems with submitted solutions.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/GlobalAccounting.lean; original SHA-256 8368f847d33d41b253e3289693d4dc50d871ab3b4b05626890fae7d30bb69fc4; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

/- Actual coordinate accounting: incoming arcs are deduplicated to child
positions, external arcs have residual multiplicity, and histograms are
derived identities. -/
import Definitions.Def_BS2_b3ba934b_GradedPositiveBoundary
import Definitions.Def_BS2_b3ba934b_ResidualCaps
import Definitions.Def_BS2_b3ba934b_PrefixGreedy
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Ring

set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option linter.unusedSectionVars false

namespace ThreeBoundAccounting
open OAI.Paper320 ThreeBoundWitness ThreeBoundProfiles ThreeBoundPositive
open scoped Classical BigOperators
noncomputable section
variable {V I K : Type} [Fintype V] [Fintype I] [Fintype K]

def hits (R : V → V → Prop) (ell : V → V → Bool) (G : Finset V) (w : V) : Finset Bool :=
  (G.filter fun v => R v w).image fun v => ell v w

def incoming (R : V → V → Prop) (G : Finset V) (w : V) : ℕ :=
  (G.filter fun v => R v w).card

theorem hits_card_le_incoming (R : V → V → Prop) (ell : V → V → Bool)
    (G : Finset V) (w : V) : (hits R ell G w).card ≤ incoming R G w :=
  Finset.card_image_le

theorem hits_card_le_two (R : V → V → Prop) (ell : V → V → Bool)
    (G : Finset V) (w : V) : (hits R ell G w).card ≤ 2 := by
  exact (Finset.card_le_card (Finset.subset_univ _)).trans_eq (by decide)

theorem hits_card_le_capped (R : V → V → Prop) (ell : V → V → Bool)
    (G : Finset V) (w : V) : (hits R ell G w).card ≤ min 2 (incoming R G w) :=
  le_min (hits_card_le_two R ell G w) (hits_card_le_incoming R ell G w)

theorem mem_hits (R : V → V → Prop) (ell : V → V → Bool)
    (G : Finset V) (w : V) (c : Bool) :
    c ∈ hits R ell G w ↔ ∃ v ∈ G, R v w ∧ ell v w = c := by
  simp only [hits, Finset.mem_image, Finset.mem_filter]
  constructor
  · rintro ⟨v,⟨hv,hR⟩,hc⟩
    exact ⟨v,hv,hR,hc⟩
  · rintro ⟨v,hv,hR,hc⟩
    exact ⟨v,⟨hv,hR⟩,hc⟩

def hist (H : Finset V) (tag : V → K) (inc : V → ℕ) (k : K) (h : ℕ) : ℕ :=
  (H.filter fun v => tag v = k ∧ min 2 (inc v) = h).card

def typeCount (H : Finset V) (tag : V → K) (k : K) : ℕ :=
  (H.filter fun v => tag v = k).card

theorem sum_grouped (H : Finset V) (tag : V → K) (f : K → ℕ) :
    (∑ v ∈ H, f (tag v)) = ∑ k, typeCount H tag k*f k := by
  classical
  simpa [typeCount, Finset.sum_const, nsmul_eq_mul] using
    (Finset.sum_fiberwise' H tag f).symm

theorem histogram_partition (H : Finset V) (tag : V → K) (inc : V → ℕ) (k : K) :
    hist H tag inc k 0+hist H tag inc k 1+hist H tag inc k 2 = typeCount H tag k := by
  let g : V → Fin 3 := fun v => ⟨min 2 (inc v),by omega⟩
  have hh := Finset.sum_card_fiberwise_eq_card_filter
    (H.filter fun v => tag v = k) (Finset.univ : Finset (Fin 3)) g
  simp only [Finset.mem_univ, Finset.filter_true] at hh
  rw [Fin.sum_univ_succ,Fin.sum_univ_succ,Fin.sum_univ_succ] at hh
  simpa [hist,typeCount,g,Finset.filter_filter,Fin.ext_iff,Nat.add_assoc] using hh

theorem histogram_zero (H : Finset V) (tag : V → K) (inc : V → ℕ) (k : K) :
    hist H tag inc k 0 = typeCount H tag k-hist H tag inc k 1-hist H tag inc k 2 := by
  have h := histogram_partition H tag inc k
  omega

theorem histogram_sum (H : Finset V) (tag : V → K) (inc : V → ℕ)
    (cost : K → ℕ → ℕ) :
    (∑ v ∈ H, cost (tag v) (min 2 (inc v))) =
      ∑ k, (hist H tag inc k 0*cost k 0+
        hist H tag inc k 1*cost k 1+hist H tag inc k 2*cost k 2) := by
  classical
  let g : V → K × Fin 3 := fun v => (tag v,⟨min 2 (inc v),by omega⟩)
  let f : K × Fin 3 → ℕ := fun z => cost z.1 z.2.val
  have hh := sum_grouped H g f
  rw [Fintype.sum_prod_type] at hh
  have hc : ∀ k,
      (∑ b : Fin 3, typeCount H g (k,b)*f (k,b)) =
      hist H tag inc k 0*cost k 0+hist H tag inc k 1*cost k 1+
        hist H tag inc k 2*cost k 2 := by
    intro k
    rw [Fin.sum_univ_succ,Fin.sum_univ_succ,Fin.sum_univ_succ]
    simp [typeCount,hist,g,f,Prod.ext_iff,Fin.ext_iff,Nat.add_assoc]
  simpa only [g,f,hc] using hh

theorem histogram_weighted_bound (H : Finset V) (tag : V → K) (inc : V → ℕ)
    (sets : V → Finset I) (cost : K → ℕ → ℕ)
    (hcost : ∀ v ∈ H, (sets v).card ≤ cost (tag v) (min 2 (inc v))) :
    (H.biUnion sets).card ≤
      ∑ k, ((typeCount H tag k-hist H tag inc k 1-hist H tag inc k 2)*cost k 0+
        hist H tag inc k 1*cost k 1+hist H tag inc k 2*cost k 2) := by
  calc
    _ ≤ ∑ v ∈ H, (sets v).card := Finset.card_biUnion_le
    _ ≤ ∑ v ∈ H, cost (tag v) (min 2 (inc v)) := Finset.sum_le_sum hcost
    _ = _ := by rw [histogram_sum]; simp only [← histogram_zero]

theorem histogram_delta_identity (count one two c₀ c₁ c₂ : ℕ)
    (hc : one+two ≤ count) (h₁ : c₀ ≤ c₁) (h₂ : c₀ ≤ c₂) :
    (count-one-two)*c₀+one*c₁+two*c₂ =
      count*c₀+one*(c₁-c₀)+two*(c₂-c₀) := by
  have ec : count-one-two+one+two = count := by omega
  have e₁ : c₁ = (c₁-c₀)+c₀ := (Nat.sub_add_cancel h₁).symm
  have e₂ : c₂ = (c₂-c₀)+c₀ := (Nat.sub_add_cancel h₂).symm
  calc
    _ = (count-one-two+one+two)*c₀+one*(c₁-c₀)+two*(c₂-c₀) := by
      conv_lhs => rw [e₁,e₂]
      ring
    _ = _ := by rw [ec]

theorem histogram_delta_bound (H : Finset V) (tag : V → K) (inc : V → ℕ)
    (sets : V → Finset I) (cost : K → ℕ → ℕ)
    (hcost : ∀ v ∈ H, (sets v).card ≤ cost (tag v) (min 2 (inc v)))
    (h₁ : ∀ k, cost k 0 ≤ cost k 1) (h₂ : ∀ k, cost k 0 ≤ cost k 2) :
    (H.biUnion sets).card ≤ ∑ k,
      (typeCount H tag k*cost k 0+hist H tag inc k 1*(cost k 1-cost k 0)+
        hist H tag inc k 2*(cost k 2-cost k 0)) := by
  apply (histogram_weighted_bound H tag inc sets cost hcost).trans_eq
  apply Finset.sum_congr rfl
  intro k _
  apply histogram_delta_identity
  · have h := histogram_partition H tag inc k
    omega
  · exact h₁ k
  · exact h₂ k

variable {L : Type} [Preorder L]

def externalHeads (S : Stage L I V) (F : L → (I → Bool) → Bool) (j : L)
    (x : ((V × Bool) × I) → Bool) (H : Finset V) (v : V) : Finset V :=
  failed S F j x v \ H

theorem failed_inter_high (S : Stage L I V) (F : L → (I → Bool) → Bool) (j : L)
    (x : ((V × Bool) × I) → Bool) (H : Finset V)
    (hH : ∀ w ∈ H, ∀ c : Bool, F (S.guard j) (child x w c) = true) (v : V) :
    failed S F j x v ∩ H = H.filter (S.Adj v) := by
  ext w
  simp only [Finset.mem_inter,failed,Finset.mem_filter,Finset.mem_univ,true_and]
  constructor
  · exact fun h => ⟨h.2,h.1.1⟩
  · exact fun h => ⟨⟨h.2,hH w h.1 (S.label v w)⟩,h.1⟩

theorem externalHeads_card (S : Stage L I V) (F : L → (I → Bool) → Bool) (j : L)
    (x : ((V × Bool) × I) → Bool) (H : Finset V)
    (hH : ∀ w ∈ H, ∀ c : Bool, F (S.guard j) (child x w c) = true) (v : V) :
    (externalHeads S F j x H v).card =
      (failed S F j x v).card-(H.filter (S.Adj v)).card := by
  unfold externalHeads
  have hh := Finset.card_sdiff_add_card_inter (failed S F j x v) H
  rw [failed_inter_high S F j x H hH v] at hh
  omega

def externalBits (S : Stage L I V) (F : L → (I → Bool) → Bool) (j : L)
    (x : ((V × Bool) × I) → Bool) (G H : Finset V) : Finset ((V × Bool) × I) :=
  G.biUnion fun v => (externalHeads S F j x H v).biUnion fun w =>
    liftBits w (S.label v w) (flipsTo (F (S.guard j)) false (child x w (S.label v w)))

theorem externalBits_card_le (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (i j : L) (x : ((V × Bool) × I) → Bool) (G H : Finset V)
    (hH : ∀ w ∈ H, ∀ c : Bool, F (S.guard j) (child x w c) = true)
    (hweak : ∀ v ∈ G, ∀ w ∈ failed S F j x v,
      F (S.guard i) (child x w (S.label v w)) = true)
    (s : ℕ) (hs : BBound F (S.guard j) (S.guard i) s) :
    (externalBits S F j x G H).card ≤
      (∑ v ∈ G, ((failed S F j x v).card-(H.filter (S.Adj v)).card))*s := by
  unfold externalBits
  calc
    _ ≤ ∑ v ∈ G, ((externalHeads S F j x H v).biUnion fun w =>
        liftBits w (S.label v w)
          (flipsTo (F (S.guard j)) false (child x w (S.label v w)))).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ v ∈ G, (externalHeads S F j x H v).card*s := by
      apply Finset.sum_le_sum
      intro v hv
      calc
        _ ≤ ∑ w ∈ externalHeads S F j x H v,
            (liftBits w (S.label v w)
              (flipsTo (F (S.guard j)) false (child x w (S.label v w)))).card :=
          Finset.card_biUnion_le
        _ ≤ ∑ _w ∈ externalHeads S F j x H v, s := by
          apply Finset.sum_le_sum
          intro w hw
          rw [card_liftBits]
          exact hs _ (hweak v hv w (Finset.mem_sdiff.mp hw).1)
        _ = _ := by simp [Finset.sum_const,nsmul_eq_mul]
    _ = _ := by simp only [externalHeads_card S F j x H hH,Finset.sum_mul]

theorem union_cover_bound (U high negative external : Finset I) (h n e : ℕ)
    (hcover : U ⊆ high ∪ negative ∪ external)
    (hh : high.card ≤ h) (hn : negative.card ≤ n) (he : external.card ≤ e) :
    U.card ≤ h+n+e := by
  calc
    _ ≤ (high ∪ negative ∪ external).card := Finset.card_le_card hcover
    _ ≤ (high ∪ negative).card+external.card := Finset.card_union_le _ _
    _ ≤ high.card+negative.card+external.card :=
      Nat.add_le_add_right (Finset.card_union_le _ _) _
    _ ≤ _ := Nat.add_le_add (Nat.add_le_add hh hn) he

end
end ThreeBoundAccounting

#print axioms ThreeBoundAccounting.histogram_weighted_bound
#print axioms ThreeBoundAccounting.externalBits_card_le


