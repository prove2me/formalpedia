-- Prove2me | Definitions.Def_Mazoit2013_PartialDecompositions
-- name    : Mazoit2013_PartialDecompositions
-- status  : Definition
-- author  : @lreyzin
-- created : 2026-11-13T23:13:58.941196+00:00
-- url     : https://prove2.me/theorems/cdc17eda-7024-49b8-a0d3-c19af6b6971e
-- title:
--   Partial tree decompositions and their flap families
-- statement:
--   A partial decomposition at threshold b is a finite tree decomposition with at least one bag of size at most b, whose larger bags are leaves with a unique small neighbor. Its flaps are the differences between large leaf bags and their neighbor bags. RealizableFlaps records families arising in this way, and partialFamilies is the finite collection of all such families. Components outside S and star bags S union C are also defined. The explicit small-neighbor condition is included in this formal interface.
-- source:
--   Mazoit, A simple proof of the tree-width duality theorem, https://arxiv.org/pdf/1309.2266, p. 2, partial decompositions and star decompositions.

import Definitions.Def_SeymourThomas1993_Brambles
import Definitions.Def_RobertsonSeymour1986_GM5_TreewidthLE
import Mathlib.Combinatorics.SimpleGraph.Star
open RobertsonSeymour1986.GM5 StableMSR.Recovery.Havens
namespace StableMSR.Recovery.PartialDecompositions
variable {V : Type} [Fintype V] [DecidableEq V]
noncomputable def components (G : SimpleGraph V) (S : Finset V) : Finset (Finset V) :=
  by classical exact Finset.univ.filter (IsFlap G S)
@[simp] lemma mem_components {G : SimpleGraph V} {S C : Finset V} :
    C ∈ components G S ↔ IsFlap G S C := by classical simp [components]
def starBag (G : SimpleGraph V) (S : Finset V) : Option ↥(components G S) → Finset V
  | none => S
  | some C => S ∪ C.val
def IsPartial {T : Type} (G : SimpleGraph V) (b : ℕ)
    (tree : SimpleGraph T) (bags : T → Finset V) : Prop :=
  IsTreeDecomposition G tree bags ∧
  (∃ t, (bags t).card ≤ b) ∧
  ∀ t, b < (bags t).card → ∃ u, tree.Adj t u ∧ (bags u).card ≤ b ∧
    ∀ v, tree.Adj t v → v = u
noncomputable def flaps {T : Type} (b : ℕ) (tree : SimpleGraph T)
    (bags : T → Finset V) : Finset (Finset V) := by
  classical
  exact Finset.univ.filter (fun C => ∃ t u, b < (bags t).card ∧ tree.Adj t u ∧ C = bags t \ bags u)
@[simp] lemma mem_flaps {T : Type} {b : ℕ} {tree : SimpleGraph T}
    {bags : T → Finset V} {C : Finset V} :
    C ∈ flaps b tree bags ↔ ∃ t u, b < (bags t).card ∧ tree.Adj t u ∧ C = bags t \ bags u := by
  classical
  simp [flaps]
def RealizableFlaps (G : SimpleGraph V) (b : ℕ) (d : Finset (Finset V)) : Prop :=
  ∃ (T : Type) (_ : Fintype T) (tree : SimpleGraph T) (bags : T → Finset V),
    IsPartial G b tree bags ∧ flaps b tree bags = d
noncomputable def partialFamilies (G : SimpleGraph V) (b : ℕ) : Finset (Finset (Finset V)) := by
  classical exact Finset.univ.filter (RealizableFlaps G b)
@[simp] lemma mem_partialFamilies {G : SimpleGraph V} {b : ℕ} {d : Finset (Finset V)} :
    d ∈ partialFamilies G b ↔ RealizableFlaps G b d := by
  classical simp [partialFamilies]
end StableMSR.Recovery.PartialDecompositions


