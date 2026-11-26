-- Prove2me | Definitions.Def_MurtySimon_Bound
-- name    : MurtySimon_Bound
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T22:57:19.541455+00:00
-- url     : https://prove2.me/theorems/c3b5a0bc-c4b6-4d61-8bbf-fbf14ba8cf95
-- title:
--   Bound
-- statement:
--   Definitions and structural lemmas for Bound, from Juan Pablo Traverso Gianini (jtraverso/murty-simon-conjecture; see pinned Apache-2.0 LICENSE and source headers)'s pinned The Murty-Simon conjecture on diameter-2-critical graphs development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/jtraverso/murty-simon-conjecture/blob/adadd2fbd0ba9e9c71faadd105f357f7b12a814f/MurtySimon/Bound.lean

module
public import Definitions.Def_MurtySimon_Components
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace MurtySimon
open Finset SimpleGraph
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
noncomputable section
def Covered (M : Finset (Sym2 V)) (x : V) : Prop := ∃ y, s(x, y) ∈ M
def mate (M : Finset (Sym2 V)) (x : V) : V := if h : ∃ y, s(x, y) ∈ M then h.choose else x
variable {M : Finset (Sym2 V)}
variable (G M) in
/-- The noncritical non-edges. -/
def Nc : Finset (Sym2 V) := univ.filter fun f => f ∈ Gᶜ.edgeSet ∧ ¬ IsCrit G f
variable (G M) in
/-- `(x, y)` is a switch exit: `xy` is a noncritical non-edge, `x` is covered and `x*y` is a
vertex of `𝓘'`. -/
def IsExit (p : V × V) : Prop :=
  s(p.1, p.2) ∈ Gᶜ.edgeSet ∧ ¬ IsCrit G s(p.1, p.2) ∧ Covered M p.1 ∧
    s(mate M p.1, p.2) ∈ Lt G M ∪ Rt G
variable (G M) in
/-- The set of switch exits. -/
def exits : Finset (V × V) := univ.filter (IsExit G M)
variable (G M) in
/-- The component of `𝓘'` to which a switch exit belongs. -/
def compOf (p : V × V) : (aux G M).ConnectedComponent :=
  (aux G M).connectedComponentMk s(mate M p.1, p.2)
variable (M) in
/-- The weight of a switch exit: `2` for a safe exit, `1` otherwise. -/
def wt (p : V × V) : ℕ := if Covered M p.2 then 1 else 2
def compWt (C : (aux G M).ConnectedComponent) : ℕ :=
  ∑ p ∈ (exits G M).filter (fun p => compOf G M p = C), wt M p
def Recovers (p : V × V) (ℓ : Sym2 V) : Prop :=
  s(mate M p.1, p.2) = ℓ ∨
    ∃ z u, s(mate M p.1, p.2) = s(z, p.2) ∧ IsMid G z p.2 u ∧ ℓ = s(u, p.2)
section Lopsided
variable (hM : IsEdgeMatching G M) {C : (aux G M).ConnectedComponent}
  (hC : cA G M C = cB G M C + 1)
include hM hC
end Lopsided
end
end MurtySimon


