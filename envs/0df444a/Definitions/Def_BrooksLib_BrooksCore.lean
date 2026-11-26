-- Prove2me | Definitions.Def_BrooksLib_BrooksCore
-- name    : BrooksLib_BrooksCore
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T02:31:13.746449+00:00
-- url     : https://prove2.me/theorems/16a693ba-b720-4ad8-8209-fffa3cda6612
-- title:
--   Brooks Core
-- statement:
--   Definitions and structural lemmas for Brooks Core, from Juan Pablo Traverso Gianini (jtraverso/brooks; see pinned Apache-2.0 LICENSE and source headers)'s pinned Erdos-Rubin-Taylor degree-choosability, block-cut trees, and Brooks' theorem development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/jtraverso/brooks/blob/b99e6f500256586626396de9c2d6fd4d96119d60/BrooksLib/BrooksCore.lean

module
public import Definitions.Def_BrooksLib_Greedy
set_option autoImplicit true
@[expose] public section
@[expose] public section
open SimpleGraph Finset
namespace BrooksTheorem
namespace Aux
variable {V : Type*}
def restr (H : SimpleGraph V) (S : Set V) : SimpleGraph V where
  Adj u v := H.Adj u v ∧ u ∈ S ∧ v ∈ S
  symm := ⟨fun _ _ ⟨h, hu, hv⟩ => ⟨h.symm, hv, hu⟩⟩
  loopless := ⟨fun u h => H.loopless.irrefl u h.1⟩
variable [Fintype V]
open Classical in
/-- The set of ordered adjacent pairs. -/
noncomputable def pairs (H : SimpleGraph V) : Finset (V × V) :=
  univ.filter (fun p => H.Adj p.1 p.2)
noncomputable def mu (H : SimpleGraph V) : ℕ := (pairs H).card
def IHyp (k : ℕ) (H : SimpleGraph V) : Prop :=
  ∀ H' : SimpleGraph V, mu H' < mu H → (∀ v, (nb H' v).card ≤ k) → H'.CliqueFree (k + 1) →
    ∃ f : V → Fin k, Proper H' f
end Aux
end BrooksTheorem


