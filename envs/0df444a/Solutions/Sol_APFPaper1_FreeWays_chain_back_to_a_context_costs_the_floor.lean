-- Prove2me | solution 1 for APFPaper1.FreeWays.chain_back_to_a_context_costs_the_floor
-- status  : ACCEPTED   (prove)
-- author  : @FiniteUniverse
-- created : 2026-11-17T04:26:37.696633+00:00
-- url     : https://prove2.me/submissions/e8e72075-9c04-4249-8d40-6c190fb8425f

import Definitions.Def_APFPaper1_free_ways_under_the_per_realignment_floor_Vocabulary
/-
APF Foundation Ledger — theorem node DRAFT (Claude seat, session EthanBrooke-01WrrBvv, 2026-11-16; not
 gated, not reviewed, not released, not built on the build machine)
name: APFPaper1_free_ways_under_the_per_realignment_floor
title: Under the Supplement's protocol laws with the per-realignment floor, no chain of free ways, through any contexts, leads from one alignment of a context to a different one; free reach between two contexts that can go both ways is a renaming; reaching the other side after a free return costs the floor; and three supplied models show what the laws leave open
inputs_revision: 2026-11-14.1 (the occupant statement is NOT installed)
mathlib_rev: 0df444a360eaa60ab8c11dca51a86af692955474
source: the author, 2026-11-16 08:55 HST: "Yes", to digging at option B (between two contexts) of
 TEE_UP_where_turns_between_could_come_from_2026-11-16.
 Consulted before writing. Paper 1 Supplement v9.28: 1833-1850 (structural alignment), 1852-1854 (the
 spin-1/2 example: "Moving between them is a Bloch-sphere rotation; the realignment cost ... records
 what the substrate pays for the move"), 1887-1898 (realignment cost; protocol axioms P1 to P4, "stated
 here as the hypotheses they are"; P4, the per-realignment floor, a positive lower bound on cost "for
 every admissible protocol connecting distinct admissible alignments"), 1903-1913 (its lemma), 1915-1917 ("Connectivity is not
 asserted": the connectivity hypothesis CH is named and not adopted), 1674-1676 (the transition floor is
 "a separate named hypothesis"), 2091-2096 ("A reversible process may transport or transform an already
 supported distinction without adding a new ledger entry"), 3197-3219 (typed process fragments; the
 finite APF process category), 7107 (two native models: the laws do not decide CH), 7307-7310 (C2, C3:
 "you cannot almost-move something"). Paper 5 Supplement v7.33: 1408-1430 (held and record categories),
 1919-1922 (the class transition "books a positive floor"). Paper 0 v6.3.2: 3220-3228. Codebank:
 apf/class_transition.py (check_T_realignment_floor_is_epsilon_star: "The named reading treats a
 realignment as creation of a new resolved structure and release of the old one"), apf/_module_manifest.py
 v24.3.397 (the collapse triad: "FREE while coherent/held").
standing: ORDINARY MATHEMATICS ON SUPPLIED DATA. The relation Conn ("some way connects this place to that
 one at this cost"), the contexts and their alignments are supplied. The three laws are HYPOTHESES here,
 as they are in the Supplement. None is a declared input.
consumes_inputs: none.
fidelity:
 (a) The Supplement states P2 and P3 for the protocols of ONE context, and P2 only "if the concatenation
     remains admissible". Here Concat is asked of ways through other contexts as well, and of every
     pair of ways that meet. That extension is this file's hypothesis.
 (b) Floor is P4 as the Supplement words it: two alignments of a context are distinct when they differ
     at all. The codebank's named reading is narrower (a realignment makes a new resolved structure).
     On that reading Floor here asks more than P4 does. Which is meant is the author's call.
 (c) A place is a context together with one of its alignments. Whether a way from a context back to
     itself through another context is a protocol of the first context is a reading (the author's
     ruling of 2026-11-12 tests such a word against the budget of the context it starts in).
statement:
 - (free_way_in_a_context_moves_nothing) under Floor, a free way within a context joins an alignment
   only to itself.
 - (chain_back_to_a_context_costs_the_floor) under Identity, Concat and Floor, a chain of ways from one
   alignment of a context to a different one costs at least that context's floor in total, however
   many legs and whatever contexts it passes through.
 - (no_free_chain_between_two_alignments) so no chain of free ways does it.
 - (free_round_trip_returns) what is reached for free from an alignment returns for free only to it.
 - (free_reach_is_single_valued_when_it_can_return) if an alignment reaches a place for free, that place
   reaches for free no other alignment of the same context.
 - (free_turn_is_a_renaming, free_reach_follows_the_renaming) if free ways lead from every alignment of
   one context to an alignment of another and back, the two maps are inverse to each other, and free
   reach lands exactly where the map says.
 - (reaching_the_other_side_costs_the_floor) if a place can come back to an alignment for free, then
   every way from that alignment to a different alignment of the same context costs the floor.
 - (priced_ways_meet_the_laws) a supplied model: every two places are joined at one price, both ways
   round, and the three laws hold. The laws price moving; they do not forbid it.
 - (all_free_ways_fail_the_floor) a supplied model: every way is free. Identity and Concat hold; Floor
   fails wherever a context has two alignments.
 - (side_keeping_ways_meet_the_laws) a supplied model: contexts without end, two alignments each; free
   ways lead from every context to every other and keep the side; every way that turns a side over is
   priced. The three laws hold. So free ways between contexts are consistent with the floor, as long
   as none of their chains turns a side over.
reading: under the floor as the Supplement words it, whatever a free way changes is not an alignment of
 the context it returns to. Free ways can still lead between contexts. They carry each alignment to
 one alignment and back.
not_claimed: that any of the three laws holds of the physical data; that the Supplement means Floor as
 worded here and not the codebank's named reading; that any model here is a physical context. No lane.
 No claim that the transfer is forced, that the carrier gap is closed or narrowed, or that Born is
 derived.
axioms: within propext, Classical.choice, Quot.sound. No sorry.
-/
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

set_option autoImplicit false

namespace APFPaper1.FreeWays

universe u v



section Laws
variable {Ctx : Type u} {Al : Ctx → Type v}











variable {Conn : Place Al → Place Al → ℝ → Prop} {eps : Ctx → ℝ}

/-- A chain of free ways is a chain of total cost nothing. -/
theorem FreeChain.toChain_p2mProof {p r : Place Al} (h : FreeChain Conn p r) : Chain Conn p r 0 := by
  induction h with
  | nil p => exact Chain.nil p
  | cons h _ ih =>
    have h2 := Chain.cons h ih
    rwa [add_zero] at h2

/-- One chain of free ways after another is a chain of free ways. -/
theorem FreeChain.append {p q r : Place Al} (h1 : FreeChain Conn p q) (h2 : FreeChain Conn q r) :
    FreeChain Conn p r := by
  induction h1 with
  | nil p => exact h2
  | cons h _ ih => exact FreeChain.cons h (ih h2)

/-- A chain is a way, at no more than the sum of its legs. -/
theorem chain_is_a_way_p2mProof (hId : Identity Conn) (hC : Concat Conn) {p r : Place Al} {s : ℝ}
    (h : Chain Conn p r s) : ∃ c, c ≤ s ∧ Conn p r c := by
  induction h with
  | nil p => exact ⟨0, le_refl _, hId p⟩
  | cons hpq _ ih =>
    obtain ⟨c1, hc1, h1⟩ := ih
    obtain ⟨c2, hc2, h2⟩ := hC _ _ _ _ _ hpq h1
    exact ⟨c2, by linarith, h2⟩

/-- Under the floor, a free way within a context joins an alignment only to itself. -/
theorem free_way_in_a_context_moves_nothing_p2mProof (hF : Floor Conn eps) {g : Ctx} {a b : Al g}
    (h : Conn ⟨g, a⟩ ⟨g, b⟩ 0) : a = b := by
  by_contra hne
  have h1 := hF.2 g a b 0 hne h
  have h2 := hF.1 g
  linarith

/-- A chain of ways from one alignment of a context to a different one costs at least that context's
floor in total, however many legs it has and whatever contexts it passes through. -/
theorem chain_back_to_a_context_costs_the_floor_p2mProof (hId : Identity Conn) (hC : Concat Conn)
    (hF : Floor Conn eps) {g : Ctx} {a b : Al g} {s : ℝ}
    (h : Chain Conn ⟨g, a⟩ ⟨g, b⟩ s) (hne : a ≠ b) : eps g ≤ s := by
  obtain ⟨c, hc, hw⟩ := chain_is_a_way_p2mProof hId hC h
  have := hF.2 g a b c hne hw
  linarith

/-- No chain of free ways leads from one alignment of a context to a different one. -/
theorem no_free_chain_between_two_alignments_p2mProof (hId : Identity Conn) (hC : Concat Conn)
    (hF : Floor Conn eps) {g : Ctx} {a b : Al g}
    (h : FreeChain Conn ⟨g, a⟩ ⟨g, b⟩) : a = b := by
  by_contra hne
  have h1 := chain_back_to_a_context_costs_the_floor_p2mProof hId hC hF h.toChain_p2mProof hne
  have h2 := hF.1 g
  linarith

/-- What is reached for free from an alignment returns for free only to that alignment. -/
theorem free_round_trip_returns_p2mProof (hId : Identity Conn) (hC : Concat Conn) (hF : Floor Conn eps)
    {g : Ctx} {a b : Al g} {q : Place Al}
    (h1 : FreeChain Conn ⟨g, a⟩ q) (h2 : FreeChain Conn q ⟨g, b⟩) : a = b :=
  no_free_chain_between_two_alignments_p2mProof hId hC hF (h1.append h2)

/-- If an alignment reaches a place for free, that place reaches for free no other alignment of the
same context: free reach into a context lands on one alignment only, when that one can come back. -/
theorem free_reach_is_single_valued_when_it_can_return_p2mProof (hId : Identity Conn) (hC : Concat Conn)
    (hF : Floor Conn eps) {p : Place Al} {h : Ctx} {b b' : Al h}
    (hback : FreeChain Conn ⟨h, b⟩ p) (h2 : FreeChain Conn p ⟨h, b'⟩) : b = b' :=
  no_free_chain_between_two_alignments_p2mProof hId hC hF (hback.append h2)

/-- If free ways lead from every alignment of one context to an alignment of another, and back, the two
maps are inverse to each other: the free turn is a renaming. -/
theorem free_turn_is_a_renaming_p2mProof (hId : Identity Conn) (hC : Concat Conn) (hF : Floor Conn eps)
    {g h : Ctx} (T : Al g → Al h) (S : Al h → Al g)
    (hT : ∀ a, FreeChain Conn ⟨g, a⟩ ⟨h, T a⟩) (hS : ∀ b, FreeChain Conn ⟨h, b⟩ ⟨g, S b⟩) :
    (∀ a, S (T a) = a) ∧ (∀ b, T (S b) = b) :=
  ⟨fun a => (free_round_trip_returns_p2mProof hId hC hF (hT a) (hS (T a))).symm,
    fun b => (free_round_trip_returns_p2mProof hId hC hF (hS b) (hT (S b))).symm⟩

/-- And free reach lands exactly where the renaming says: no free way lands on another alignment. -/
theorem free_reach_follows_the_renaming_p2mProof (hId : Identity Conn) (hC : Concat Conn)
    (hF : Floor Conn eps) {g h : Ctx} (T : Al g → Al h) (S : Al h → Al g)
    (hT : ∀ a, FreeChain Conn ⟨g, a⟩ ⟨h, T a⟩) (hS : ∀ b, FreeChain Conn ⟨h, b⟩ ⟨g, S b⟩)
    {a : Al g} {b : Al h} (hab : FreeChain Conn ⟨g, a⟩ ⟨h, b⟩) : b = T a := by
  have hST := (free_turn_is_a_renaming_p2mProof hId hC hF T S hT hS).1 a
  have hback : FreeChain Conn ⟨h, T a⟩ ⟨g, a⟩ := by
    have := hS (T a)
    rwa [hST] at this
  exact (free_reach_is_single_valued_when_it_can_return_p2mProof hId hC hF hback hab).symm

/-- If a place can come back to an alignment for free, every way from that alignment on to a different
alignment of the place's context costs that context's floor. -/
theorem reaching_the_other_side_costs_the_floor_p2mProof (hId : Identity Conn) (hC : Concat Conn)
    (hF : Floor Conn eps) {p : Place Al} {h : Ctx} {b b' : Al h} {c : ℝ}
    (hback : FreeChain Conn ⟨h, b⟩ p) (hgo : Conn p ⟨h, b'⟩ c) (hne : b ≠ b') : eps h ≤ c := by
  have h1 : Chain Conn p ⟨h, b'⟩ (c + 0) := Chain.cons hgo (Chain.nil _)
  have h2 : ∀ {x y : Place Al}, FreeChain Conn x y → ∀ {z : Place Al} {s : ℝ}, Chain Conn y z s →
      Chain Conn x z s := by
    intro x y hxy
    induction hxy with
    | nil p => intro z s hz; exact hz
    | cons hw _ ih =>
      intro z s hz
      have h3 := Chain.cons hw (ih hz)
      rwa [zero_add] at h3
  have h4 := chain_back_to_a_context_costs_the_floor_p2mProof hId hC hF (h2 hback h1) hne
  linarith

end Laws

/-! ### Three supplied models -/

section Models
variable {Ctx : Type u} {Al : Ctx → Type v}



/-- The priced model meets the three laws, and joins every two places both ways round. The laws price
moving; they do not forbid it. -/
theorem priced_ways_meet_the_laws_p2mProof (e : ℝ) (he : 0 < e) :
    Identity (PricedConn (Al := Al) e) ∧ Concat (PricedConn (Al := Al) e) ∧
      Floor (PricedConn (Al := Al) e) (fun _ => e) ∧
      ∀ p q : Place Al, PricedConn e p q e ∧ PricedConn e q p e := by
  refine ⟨fun p => Or.inl ⟨rfl, rfl⟩, ?_, ⟨fun _ => he, ?_⟩, fun p q => ⟨Or.inr rfl, Or.inr rfl⟩⟩
  · intro p q r c c' h1 h2
    rcases h1 with ⟨hpq, hc⟩ | hc
    · subst hpq
      exact ⟨c', by linarith, h2⟩
    · rcases h2 with ⟨hqr, hc'⟩ | hc'
      · subst hqr
        exact ⟨c, by linarith, Or.inr hc⟩
      · exact ⟨e, by linarith, Or.inr rfl⟩
  · intro g a b c hne h
    rcases h with ⟨hab, _⟩ | hc
    · exact absurd (eq_of_heq (Sigma.mk.inj hab).2) hne
    · exact le_of_eq hc.symm



/-- With every way free, Identity and Concat hold, and the floor fails wherever a context has two
alignments. -/
theorem all_free_ways_fail_the_floor_p2mProof :
    Identity (FreeConn (Al := Al)) ∧ Concat (FreeConn (Al := Al)) ∧
      ((∃ (g : Ctx) (a b : Al g), a ≠ b) → ∀ eps : Ctx → ℝ, ¬ Floor (FreeConn (Al := Al)) eps) := by
  refine ⟨fun _ => rfl, ?_, ?_⟩
  · intro p q r c c' h1 h2
    refine ⟨0, ?_, rfl⟩
    rw [show c = 0 from h1, show c' = 0 from h2]
    norm_num
  · rintro ⟨g, a, b, hne⟩ eps hF
    have h1 := hF.2 g a b 0 hne rfl
    have h2 := hF.1 g
    linarith

end Models



/-- The side-keeping model meets the three laws; free ways lead from every context to every other and
keep the side; and every way that turns a side over, within a context or across contexts, costs the
price. -/
theorem side_keeping_ways_meet_the_laws_p2mProof (e : ℝ) (he : 0 < e) :
    Identity (SideKeepingConn e) ∧ Concat (SideKeepingConn e) ∧
      Floor (SideKeepingConn e) (fun _ => e) ∧
      (∀ (m n : ℤ) (b : Bool), SideKeepingConn e ⟨m, b⟩ ⟨n, b⟩ 0) ∧
      (∀ (m n : ℤ) (b : Bool) (c : ℝ), SideKeepingConn e ⟨m, b⟩ ⟨n, !b⟩ c → c = e) := by
  refine ⟨fun p => Or.inl ⟨rfl, rfl⟩, ?_, ⟨fun _ => he, ?_⟩, fun m n b => Or.inl ⟨rfl, rfl⟩, ?_⟩
  · intro p q r c c' h1 h2
    rcases h1 with ⟨hpq, hc⟩ | hc
    · rcases h2 with ⟨hqr, hc'⟩ | hc'
      · exact ⟨0, by rw [hc, hc']; norm_num, Or.inl ⟨hqr.trans hpq, rfl⟩⟩
      · exact ⟨e, by rw [hc, hc']; norm_num, Or.inr rfl⟩
    · rcases h2 with ⟨_, hc'⟩ | hc'
      · exact ⟨e, by rw [hc, hc']; norm_num, Or.inr rfl⟩
      · exact ⟨e, by rw [hc, hc']; linarith, Or.inr rfl⟩
  · intro g a b c hne h
    rcases h with ⟨hab, _⟩ | hc
    · exact absurd hab.symm hne
    · exact le_of_eq hc.symm
  · intro m n b c h
    rcases h with ⟨hb, _⟩ | hc
    · have hb' : (!b) = b := hb
      cases b <;> simp at hb'
    · exact hc

/-- In the side-keeping model there are free ways from each context to every other, yet no chain of
free ways turns a side over. -/
theorem side_keeping_free_chains_keep_the_side (e : ℝ) (he : 0 < e) (n : ℤ) (b b' : Bool)
    (h : FreeChain (SideKeepingConn e) ⟨n, b⟩ ⟨n, b'⟩) : b = b' := by
  obtain ⟨hId, hC, hF, _, _⟩ := side_keeping_ways_meet_the_laws_p2mProof e he
  exact no_free_chain_between_two_alignments_p2mProof hId hC hF h

end APFPaper1.FreeWays


universe apfNative_u apfNative_v
theorem solution :
∀ {Ctx : Type apfNative_u} {Al : Ctx → Type apfNative_v}
  {Conn :
    @APFPaper1.FreeWays.Place.{apfNative_u, apfNative_v} Ctx Al →
      @APFPaper1.FreeWays.Place.{apfNative_u, apfNative_v} Ctx Al → Real → Prop}
  {eps : Ctx → Real} (hId : @APFPaper1.FreeWays.Identity.{apfNative_u, apfNative_v} Ctx Al Conn)
  (hC : @APFPaper1.FreeWays.Concat.{apfNative_u, apfNative_v} Ctx Al Conn)
  (hF : @APFPaper1.FreeWays.Floor.{apfNative_u, apfNative_v} Ctx Al Conn eps) {g : Ctx} {a b : Al g} {s : Real}
  (h :
    @APFPaper1.FreeWays.Chain.{apfNative_u, apfNative_v} Ctx Al Conn (@Sigma.mk.{apfNative_u, apfNative_v} Ctx Al g a)
      (@Sigma.mk.{apfNative_u, apfNative_v} Ctx Al g b) s)
  (hne : @Ne.{apfNative_v + 1} (Al g) a b), @LE.le.{0} Real Real.instLE (eps g) s := by
  exact @APFPaper1.FreeWays.chain_back_to_a_context_costs_the_floor_p2mProof
