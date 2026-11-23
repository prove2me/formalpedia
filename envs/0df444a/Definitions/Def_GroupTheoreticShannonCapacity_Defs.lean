-- Prove2me | Definitions.Def_GroupTheoreticShannonCapacity_Defs
-- name    : GroupTheoreticShannonCapacity_Defs
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-23T07:24:59.683819+00:00
-- url     : https://prove2.me/theorems/42b8fe29-1077-4005-9df3-12bd98851646
-- title:
--   Defs
-- statement:
--   Definitions and structural lemmas for Defs, from jzuiddam/GroupTheoreticShannonCapacity contributors (see pinned LICENSE and source headers)'s pinned Shannon capacity limits from lattice packings development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/jzuiddam/GroupTheoreticShannonCapacity/blob/b3293c2c912c08768684ea560f3a59afe59920b1/GroupTheoreticShannonCapacity/Defs.lean

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.ZMod.ValMinAbs
import Mathlib.Tactic.Ring
set_option autoImplicit true
namespace GroupTheoreticShannonCapacity
def strongPower (G : SimpleGraph V) (n : ℕ) : SimpleGraph (Fin n → V) where
  Adj f g := f ≠ g ∧ ∀ i, f i = g i ∨ G.Adj (f i) (g i)
  symm := ⟨by
    intro f g ⟨hne, h⟩
    refine ⟨hne.symm, fun i => ?_⟩
    cases h i with
    | inl heq => left; exact heq.symm
    | inr hadj => right; exact hadj.symm⟩
  loopless := ⟨by intro f ⟨hne, _⟩; exact hne rfl⟩
def distMod (p : ℕ) [NeZero p] (u v : ZMod p) : ℕ :=
  let d := ((u - v).val : ℕ)
  min d (p - d)
theorem distMod_eq_valMinAbs_natAbs (p : ℕ) [NeZero p] (u v : ZMod p) :
    distMod p u v = (u - v).valMinAbs.natAbs :=
  (ZMod.valMinAbs_natAbs_eq_min (u - v)).symm
theorem distMod_comm (p : ℕ) [NeZero p] (u v : ZMod p) : distMod p u v = distMod p v u := by
  simp only [distMod_eq_valMinAbs_natAbs, show v - u = -(u - v) by ring]
  exact (ZMod.natAbs_valMinAbs_neg (u - v)).symm
def fractionGraph (p q : ℕ) [hp : NeZero p] : SimpleGraph (ZMod p) where
  Adj u v := u ≠ v ∧ distMod p u v < q
  symm := ⟨by
    intro u v ⟨hne, hdist⟩
    exact ⟨hne.symm, distMod_comm p u v ▸ hdist⟩⟩
  loopless := ⟨by intro x ⟨h, _⟩; exact h rfl⟩
notation "E[" p "/" q "]" => fractionGraph p q
end GroupTheoreticShannonCapacity


