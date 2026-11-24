-- Prove2me | Definitions.Def_Stallings_Folding
-- name    : Stallings_Folding
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T05:12:14.099328+00:00
-- url     : https://prove2.me/theorems/ae22ff67-d94f-4687-9434-4e061f3c617d
-- title:
--   Folding
-- statement:
--   Definitions and structural lemmas for Folding, from Arthur Freitas Ramos (Arthur742Ramos/stallings-folding; see pinned Apache-2.0 LICENSE and PROVENANCE.md)'s pinned Verified Stallings folding for finitely generated subgroups of F2 development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Arthur742Ramos/stallings-folding/blob/117dde0a8415d3da1787e15ad22a6223a744432d/Stallings/Folding.lean

import Definitions.Def_Stallings_InverseAutomaton
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Finset.Max
import Theorems.Thm_Stallings_InverseAutomaton_membershipTest_eq_true_iff
attribute [local simp] Stallings.InverseAutomaton.membershipTest_eq_true_iff


set_option autoImplicit true
namespace Stallings
structure InverseMultigraph (V : Type*) where
  edges : V → Letter → Finset (V)
  inverse_edges : ∀ (v : V) (x : Letter) (w : V),
    w ∈ edges v x ↔ v ∈ edges w (letterInv x)
def IsFoldCongruence {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V] (G : InverseMultigraph V)
    (r : V → V → Bool) : Prop :=
  (∀ v, r v v = true) ∧
  (∀ v w, r v w = true → r w v = true) ∧
  (∀ u v w, r u v = true → r v w = true → r u w = true) ∧
  (∀ v w x u t, r v w = true → u ∈ G.edges v x → t ∈ G.edges w x → r u t = true)
instance foldCongruenceDecidable {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V] (G : InverseMultigraph V)
    (r : V → V → Bool) : Decidable (IsFoldCongruence G r) := by
  unfold IsFoldCongruence
  infer_instance
def foldRel {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V] (G : InverseMultigraph V) (v w : V) : Prop :=
  ∀ r : V → V → Bool, IsFoldCongruence G r → r v w = true
instance foldRelDecidable {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V] (G : InverseMultigraph V) (v w : V) :
    Decidable (foldRel G v w) := by
  unfold foldRel
  infer_instance
namespace foldRel
variable {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V] (G : InverseMultigraph V)
theorem refl (v : V) : foldRel G v v := by
  intro r hr
  exact hr.1 v
theorem symm {v w : V} (h : foldRel G v w) : foldRel G w v := by
  intro r hr
  exact hr.2.1 v w (h r hr)
theorem trans {u v w : V} (huv : foldRel G u v) (hvw : foldRel G v w) :
    foldRel G u w := by
  intro r hr
  exact hr.2.2.1 u v w (huv r hr) (hvw r hr)
theorem edge_congr {v w u t : V} {x : Letter}
    (hvw : foldRel G v w) (hu : u ∈ G.edges v x) (ht : t ∈ G.edges w x) :
    foldRel G u t := by
  intro r hr
  exact hr.2.2.2 v w x u t (hvw r hr) hu ht
end foldRel
def foldRep {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V] (G : InverseMultigraph V) (v : V) : V :=
  ((Finset.univ : Finset (V)).filter fun w => foldRel G w v).min'
    ⟨v, Finset.mem_filter.mpr ⟨Finset.mem_univ _, foldRel.refl G v⟩⟩
theorem foldRep_rel {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V] (G : InverseMultigraph V) (v : V) :
    foldRel G (foldRep G v) v := by
  exact (Finset.mem_filter.mp
    (Finset.min'_mem ((Finset.univ : Finset (V)).filter fun w => foldRel G w v) _)).2
theorem foldRep_eq_of_rel {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V] (G : InverseMultigraph V) {v w : V}
    (h : foldRel G v w) : foldRep G v = foldRep G w := by
  have hsets :
      ((Finset.univ : Finset (V)).filter fun z => foldRel G z v) =
      ((Finset.univ : Finset (V)).filter fun z => foldRel G z w) := by
    ext z
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro hz
      exact foldRel.trans G hz h
    · intro hz
      exact foldRel.trans G hz (foldRel.symm G h)
  simp only [foldRep, hsets]
theorem foldRep_idem {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V] (G : InverseMultigraph V) (v : V) :
    foldRep G (foldRep G v) = foldRep G v :=
  foldRep_eq_of_rel G (foldRep_rel G v)
def foldTargets {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V] (G : InverseMultigraph V) (v : V) (x : Letter) :
    Finset (V) :=
  (Finset.univ : Finset (V)).filter fun t => ∃ u, foldRel G u v ∧ t ∈ G.edges u x
theorem foldTargets_pair {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V] (G : InverseMultigraph V) (v : V)
    (x : Letter) {u t : V} (hu : u ∈ foldTargets G v x)
    (ht : t ∈ foldTargets G v x) : foldRel G u t := by
  rcases Finset.mem_filter.mp hu with ⟨_, a, hav, hedgeA⟩
  rcases Finset.mem_filter.mp ht with ⟨_, b, hbv, hedgeB⟩
  exact foldRel.edge_congr G (foldRel.trans G hav (foldRel.symm G hbv)) hedgeA hedgeB
def foldedNextCore {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V] (G : InverseMultigraph V) (v : V) (x : Letter) :
    Option (V) :=
  if h : (foldTargets G v x).Nonempty then
    some (foldRep G ((foldTargets G v x).min' h))
  else none
def foldedNext {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V] (G : InverseMultigraph V) (v : V) (x : Letter) :
    Option (V) :=
  if v = foldRep G v then foldedNextCore G v x else none
def foldAutomaton {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V] (G : InverseMultigraph V) (base : V) :
    InverseAutomaton V where
  base := foldRep G base
  next := foldedNext G
  inverse_next := by
    intro v x w h
    have hv : v = foldRep G v := by
      unfold foldedNext at h
      split at h
      · assumption
      · simp at h
    have hcore : foldedNextCore G v x = some w := by
      change (if v = foldRep G v then foldedNextCore G v x else none) = some w at h
      rw [if_pos hv] at h
      exact h
    unfold foldedNextCore at hcore
    split_ifs at hcore with hne
    · simp only [Option.some.injEq] at hcore
      subst w
      let q := (foldTargets G v x).min' hne
      have hq : q ∈ foldTargets G v x := by
        exact Finset.min'_mem _ _
      rcases Finset.mem_filter.mp hq with ⟨_, u, huv, hedge⟩
      have hinv : u ∈ G.edges q (letterInv x) :=
        (G.inverse_edges u x q).mp hedge
      have huBack : u ∈ foldTargets G (foldRep G q) (letterInv x) := by
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_univ _, q, ?_, hinv⟩
        exact foldRel.symm G (foldRep_rel G q)
      have hqBack : (foldTargets G (foldRep G q) (letterInv x)).Nonempty :=
        ⟨u, huBack⟩
      have hminBack :
          foldRel G ((foldTargets G (foldRep G q) (letterInv x)).min' hqBack) u :=
        foldTargets_pair G (foldRep G q) (letterInv x)
          (Finset.min'_mem _ _) huBack
      have huv : foldRel G u v := huv
      have hbackRep :
          foldRep G ((foldTargets G (foldRep G q) (letterInv x)).min' hqBack) = v := by
        calc
          _ = foldRep G u := foldRep_eq_of_rel G hminBack
          _ = foldRep G v := foldRep_eq_of_rel G huv
          _ = v := hv.symm
      have hbackCore : foldedNextCore G (foldRep G q) (letterInv x) = some v := by
        unfold foldedNextCore
        rw [dif_pos hqBack]
        exact congrArg some hbackRep
      have hqCanonical : foldRep G q = foldRep G (foldRep G q) :=
        (foldRep_idem G q).symm
      change (if foldRep G q = foldRep G (foldRep G q) then
        foldedNextCore G (foldRep G q) (letterInv x) else none) = some v
      rw [if_pos hqCanonical]
      exact hbackCore
namespace InverseMultigraph
variable {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V] (G : InverseMultigraph V)
inductive Walk : V → Word → V → Prop where
  | nil (v : V) : Walk v [] v
  | cons {v u z : V} {x : Letter} {w : Word}
      (edge : u ∈ G.edges v x) (tail : Walk u w z) : Walk v (x :: w) z
def loopSubgroup (base : V) : Subgroup Free :=
  Subgroup.closure {g : Free | ∃ w : Word, wordEval w = g ∧ G.Walk base w base}
end InverseMultigraph
def CosetEquivalent (H : Subgroup Free) (g h : Free) : Prop := g * h⁻¹ ∈ H
namespace CosetEquivalent
end CosetEquivalent
def HasCosetPotential {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V] (G : InverseMultigraph V) (H : Subgroup Free)
    (potential : V → Free) : Prop :=
  ∀ {v : V} {x : Letter} {w : V}, w ∈ G.edges v x →
    CosetEquivalent H (potential w) (potential v * letterEval x)
noncomputable def cosetBool (H : Subgroup Free) (g h : Free) : Bool :=
  by
    classical
    exact if CosetEquivalent H g h then true else false
end Stallings


