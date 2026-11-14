-- Prove2me | Definitions.Def_APFB06_bridge_independence_eight_Vocabulary
-- name    : APFB06_bridge_independence_eight_Vocabulary
-- status  : Definition
-- author  : @FiniteUniverse
-- created : 2026-11-14T05:59:55.78594+00:00
-- url     : https://prove2.me/theorems/acf0bbaf-cf50-45ed-8625-fcbf9adf6074
-- title:
--   Model vocabulary — The eight declared Lean forms do not force the endpoint bridge in a supplied world
-- statement:
--   Data, predicates and immediate constructor helpers for this reviewed model. Its substantive results are published as separate proved theorem nodes.
--
--   The eight declared Lean forms do not force the endpoint bridge in a supplied world. All world data and EightHold conjuncts were read: two Boolean states, one erasing fragment, bill 1, capacity 2, trivial sufficiency/use, singleton A2 domain; B05 is vacuous because nothing is support-novel. Boundaries: Model statements concern these Lean forms only, not intended physical inputs or later hold/occupant readings. Both marks are the same mark; no distinct-pair independence is established.
--
--   This is conditional reference mathematics. The supplied model and its hypotheses are not adopted Foundation inputs, and this node does not establish K1, K3 or K4 closure.
-- source:
--   Theorems/Thm_APFB06_bridge_independence_eight.lean; Sib v44 / pullbacks v1, SHA-256 f05774e4c018ed87df667ce8326f34fa64d1f438295e13d2eaf71f23a1dea11c. Paper 1 Supplement v9.28:1313-1322,1761-1766,1774-1885,2624-2625,2777-2782,7101; Paper 5 Supplement v7.33:3034-3075 (remaining K1-K6 physical obligations); Frozen pullbacks/MANIFEST.txt and Notes passes1-6, hypothesis ledger, joint-class and held-relation ruling records; Actual codebank delta_calculus.py:165-188,236-300; continuation_calculus.py:76-140; quantum_frontend_closure.py:494-565,864-921

/-
APF Foundation Ledger — theorem node DRAFT (Claude seat, session EthanBrooke-01WrrBvv, 2026-11-13; not
 gated, not reviewed, not released, not built on the build box)
name: APFB06_bridge_independence_eight
title: The eight declared forms hold on a small supplied world in which the endpoint bridge fails
inputs_revision: 2026-10-04.1
mathlib_rev: 0df444a360eaa60ab8c11dca51a86af692955474
source: the eight declared-input definition nodes, unchanged. The construction and the proof of the eight
 follow Def_APFPaper5_Worlds_TwoObjects and APFPaper5.Worlds.eight_hold_of_two_objects (session
 EthanBrooke-01WrrBvu), with processes taken to be continuation words so that execution and the Regulation
 vocabulary are available. Thm_APFB06_occupant_regulation (the bridge `hbridge`).
consumes_inputs: none as hypotheses. The eight declared forms are PROVED of supplied data. This certifies
 nothing about the physical inputs.
world: one context; raw states true and false; one fragment, which runs from true to false and from nowhere
 else; every word bills 1, capacity 2. The protocols are the one-fragment word. One record; one raw
 distinction (the identity); record data as in the two-object worlds. The mark reads the raw value. The
 alignment has carrier the class of true and carries the mark as a distinction on the B01 quotient. B06 is
 the instance on this data with that alignment as the actual joint alignment and with joint class the PROPOSED
 extensional one (Def_APFB06_ExtensionalJoint) on record data under which, as in the two-object worlds, every
 protocol serves every task. So the bridge fails at the extensional joint class too.
statement: (eight_hold) all eight declared forms hold on this data, B06 being the instance just described.
 (mark_bound, mark_is_carried, null_in_budget) the mark is the carried distinction, read on the quotient,
 and the empty word is within budget. (J_never_saves) every run of every protocol of the joint class ends
 where the mark reads false. (not_hbridge, not_some_run) the bridge of APFB06.occupant_jointly_held, and the
 weaker form asking only for some run, both fail. (jointly_holdable) the mark is nevertheless jointly
 holdable at the raw state true, by the empty response; (bridge_free_route_applies) the same through
 APFB06.occupant_jointly_held_of_binding. (refuted_statement_is_the_frozen_bridge) the statement refuted
 is the frozen theorem's `hbridge` at this data.
reading: the eight declared forms, as encoded, do not decide where a protocol of the joint class ends.
not_claimed: independence from the physical inputs as the author means them; anything about record data that
 carries a law (here `sufficient` is True throughout, as in the two-object worlds); that this world is a physical
 context; that the source's joint class may contain a protocol that destroys what the alignment carries.
-/
import Definitions.Def_APFPaper5_Worlds_TwoObjects
import Definitions.Def_APFPaper1_Regulation
import Definitions.Def_APFB06_ExtensionalJoint
import Theorems.Thm_APFB06_occupant_jointly_held
import Theorems.Thm_APFB06_occupant_jointly_held_of_binding
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

set_option autoImplicit false
open APFPaper1.Continuation

namespace APFB06.BridgeWorld

abbrev Frag : Unit → Unit → Type := fun _ _ => Unit
abbrev Raw : Unit → Type := fun _ => Bool
abbrev Res : Unit → Type := fun _ => Unit
abbrev Dist : Type := APFPaper5.Worlds.Dist

def step : (g h : Unit) → Frag g h → Raw g → Raw h → Prop := fun _ _ _ x y => x = true ∧ y = false
def resource : (g : Unit) → WordFrom Frag g → Res g := fun _ _ => ()
def calibration : (g : Unit) → Res g → NNReal := fun _ _ => 1
def C : Unit → NNReal := fun _ => 2
def reads : (h : Unit) → Raw h → Unit → Bool := fun _ y _ => y

abbrev K : (g : Unit) → Raw g → WordFrom Frag g → Prop := Cont step resource calibration C

/-- The one-fragment word. -/
def one (g : Unit) : WordFrom Frag g := ⟨g, Word.cons (g := g) (h := g) (k := g) () (Word.nil g)⟩

theorem budget (g : Unit) (w : WordFrom Frag g) : calibration g (resource g w) ≤ C g :=
  show (1 : NNReal) ≤ 2 from one_le_two

theorem one_runs : Executes step (one ()).2 true false := ⟨false, ⟨rfl, rfl⟩, rfl⟩

theorem one_only_from_true_to_false (x : Raw ()) (y : Raw (one ()).1)
    (h : Executes step (one ()).2 x y) : x = true ∧ y = false := by
  obtain ⟨y', ⟨hx, hy'⟩, hnil⟩ := h
  have hyy : y' = y := hnil
  exact ⟨hx, hyy ▸ hy'⟩

theorem profile_ne : K () true ≠ K () false := by
  intro h
  have h1 : K () true (one ()) := ⟨⟨false, one_runs⟩, budget _ _⟩
  have h2 : K () false (one ()) := Eq.mp (congrFun h (one ())) h1
  obtain ⟨⟨y, hy⟩, _⟩ := h2
  exact Bool.noConfusion (one_only_from_true_to_false false y hy).1

theorem profile_inj (a b : Bool) (h : K () a = K () b) : a = b := by
  cases a <;> cases b
  · rfl
  · exact absurd h.symm profile_ne
  · exact absurd h profile_ne
  · rfl

/-- The mark as a distinction on the B01 quotient. -/
def markD : APFB01.PhysicalState (K ()) → Bool := Quot.lift (fun x : Bool => x) profile_inj

def D : (g : Unit) → Set (APFB01.PhysicalState (K g) → Bool) := fun _ => Set.univ

def markTask : APFB06.Task (K ()) (D ()) := ⟨markD, Set.mem_univ _⟩

def align : APFB06.OriginalAlignment (K ()) (D ()) where
  carrier := APFB01.physicalClass (K ()) true
  carried := {markTask}
  active := by
    intro d hd
    rw [Finset.mem_singleton] at hd
    subst hd
    rfl

/-- The protocols: the one-fragment word. -/
def protocols : (g : Unit) → Set (WordFrom Frag g) := fun g => {one g}

def proto0 : {p // p ∈ protocols ()} := ⟨one (), rfl⟩

def maint (g : Unit) (_ : {p // p ∈ protocols g}) : Set Unit := Set.univ

/-- Record data for B06's tasks, as in the two-object worlds: no law, every protocol serves every task. -/
def suffT (g : Unit) (_ : {p // p ∈ protocols g}) (_ : Set Unit) (_ : APFB06.Task (K g) (D g)) : Prop :=
  True
def usesT (g : Unit) (_ : {p // p ∈ protocols g}) (_ : APFB06.Task (K g) (D g)) (_ : Set Unit) : Prop :=
  True

/-- The joint class: the PROPOSED extensional one (Def_APFB06_ExtensionalJoint) on that record data. -/
def J : (g : Unit) → Finset (APFB06.Task (K g) (D g)) → Set {p // p ∈ protocols g} :=
  fun g => APFB06.extensionalJoint (maint g) (suffT g) (usesT g)



def actualJoint : Set (Sigma fun g => APFB06.OriginalAlignment (K g) (D g)) := {⟨(), align⟩}

def wholeRes (g : Unit) (p : {p // p ∈ protocols g}) : Res g := resource g p.val
def suff (g : Unit) (_ : {p // p ∈ protocols g}) (_ : Set Unit) (_ : Dist) : Prop := True
def uses (g : Unit) (_ : {p // p ∈ protocols g}) (_ : Dist) (_ : Set Unit) : Prop := True

/-- The eight declared forms on the supplied data; B06 is the instance with the alignment `align`. -/
def EightHold : Prop :=
  APF_B01_DeclaredInput (K ())
      (fun (f : APFB01.PhysicalState (K ()) → Prop) (x : Bool) => f (APFB01.physicalClass (K ()) x))
      (fun (f : APFB01.PhysicalState (K ()) → Prop) (x : Bool) => f (APFB01.physicalClass (K ()) x))
      (fun (f : APFB01.PhysicalState (K ()) → Prop) (x : Bool) => f (APFB01.physicalClass (K ()) x))
      (fun (f : APFB01.PhysicalState (K ()) → Prop) (x : Bool) => f (APFB01.physicalClass (K ()) x)) ∧
    APFB02.B02SourceMeaning (Context := Unit) (X := fun _ => Bool) (Q := fun g => WordFrom Frag g)
      (P := fun g => {p : WordFrom Frag g // p ∈ protocols g}) (Record := fun _ => Unit)
      K (fun _ d => d = id) maint suff uses ∧
    APFB03.B03TaskCost (Context := Unit) (D := fun _ => Dist)
      (P := fun g => {p : WordFrom Frag g // p ∈ protocols g})
      (R := fun _ => Unit) (Record := fun _ => Unit) wholeRes calibration maint suff uses ∧
    APFB04.B04FiniteCapacity (Context := Unit) (fun _ => (2 : ℝ)) ∧
    APFB05.MarginalFloor (Context := Unit) (D := fun _ => Dist)
      (P := fun g => {p : WordFrom Frag g // p ∈ protocols g})
      (R := fun _ => Unit) (Record := fun _ => Unit) wholeRes calibration maint suff uses
      (fun _ _ => True) (fun _ => 2) (fun _ => 1) ∧
    APFB06.AmendedB06_20260914 K D protocols J (fun g p => resource g p.val) calibration C
      actualJoint ∧
    APFB07a.A2Selection (Interface := Unit)
      (Configuration := fun _ => APFB01.PhysicalState (K ()))
      (fun _ s => s = APFB01.physicalClass (K ()) true) (fun _ _ => (1 : ℝ))
      (fun _ => APFB01.physicalClass (K ()) true) ∧
    APFB07b.BWUniqueMinimum (Interface := Unit)
      (Configuration := fun _ => APFB01.PhysicalState (K ()))
      (fun _ s => s = APFB01.physicalClass (K ()) true) (fun _ _ => (1 : ℝ))

























end APFB06.BridgeWorld


