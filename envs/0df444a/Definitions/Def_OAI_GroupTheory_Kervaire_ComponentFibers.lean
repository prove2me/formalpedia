-- Prove2me | Definitions.Def_OAI_GroupTheory_Kervaire_ComponentFibers
-- name    : OAI_GroupTheory_Kervaire_ComponentFibers
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T15:04:40.428514+00:00
-- url     : https://prove2.me/theorems/9cf3f716-217d-442b-bbd1-daa68dc159c0
-- title:
--   Restricting a permutation to a component
-- statement:
--   These notions belong to a formal proof of the Kervaire conjecture in its unimodular form. For a group $A$ and an element $w$ of the free product $A*\langle t\rangle$ whose exponent sum in $t$ is $\pm1$, the natural map from $A$ to $(A*\langle t\rangle)/\langle\!\langle w\rangle\!\rangle$ is injective, so adjoining one generator and one such relation never kills a nontrivial group. The proof writes $w$ with unit $t$-exponents and represents elements of the normal closure by planar ribbon diagrams. These are pairs of permutations of darts satisfying an Euler equation, whose disks read off copies of the relator. A capping induction removes cancelling pairs of darts. Its key rigidity step at relator corners is proved analytically, with the fractional spectral phase of unitary operators over the group von Neumann algebra of $A$, which is subadditive under a trace.
--
--   1. **Fibre.** For an equivalence relation $r$ on $D$ and a class $c$, the subtype of darts in $c$.
--   2. **Restricted permutation.** If the cycles of $\sigma$ refine $r$, the permutation of the fibre of $c$ induced by $\sigma$.
--
--   Cycle counts add up over the fibres. For an involution $\theta$, the number of cycles is determined by the number of fixed points $f$:
--   $$
--   c(\theta)=\frac{|D|+f}2 .
--   $$
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/GroupTheory/Kervaire/ComponentFibers.lean

-- Generated from openai/math@1581d4c lean/OAI/GroupTheory/Kervaire/ComponentFibers.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the Kervaire mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_Kervaire
import Definitions.Def_OAI_GroupTheory_Kervaire_Reductions
import Definitions.Def_OAI_GroupTheory_Kervaire_PermutationCycles
import Definitions.Def_OAI_GroupTheory_Kervaire_Components
import Definitions.Def_OAI_GroupTheory_Kervaire_Suppression

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

noncomputable section

namespace KervaireRibbon

section
open Equiv Equiv.Perm
open scoped Classical
variable {D : Type*} [Fintype D] [DecidableEq D]

abbrev Fiber (r : Setoid D) (c : Quotient r) := {d : D // Quotient.mk r d = c}

def fiberPerm (σ : Equiv.Perm D) (r : Setoid D) (h : SameCycle.setoid σ ≤ r) (c : Quotient r) :
    Equiv.Perm (Fiber r c) :=
  σ.subtypePerm (fun d ↦ by
    have he : Quotient.mk r (σ d) = Quotient.mk r d := Quotient.sound (h SameCycle.rfl.apply_left)
    exact he ▸ Iff.rfl)

omit [DecidableEq D] in
lemma card_fiber_sum (r : Setoid D) :
    (∑ c : Quotient r, Fintype.card (Fiber r c)) = Fintype.card D := by
  simpa only [Fintype.card_sigma] using Fintype.card_congr (Equiv.sigmaFiberEquiv (Quotient.mk r))

lemma classes_top {B : Type*} [Fintype B] [Nonempty B] : classes (⊤ : Setoid B) = 1 := by
  let _ : Subsingleton (Quotient (⊤ : Setoid B)) := Quotient.subsingleton_iff.mpr rfl
  exact Fintype.card_eq_one_iff.mpr ⟨Quotient.mk _ (Classical.arbitrary B),fun _ ↦ Subsingleton.elim _ _⟩

end

section
open Equiv Equiv.Perm
open scoped Classical
variable {D : Type*} [Fintype D] [DecidableEq D]

omit [DecidableEq D] in
lemma sameCycle_involution (θ : Perm D) (hθ : ∀ d, θ (θ d) = d) (x y : D) :
    θ.SameCycle x y ↔ y = x ∨ y = θ x := by
  constructor
  · intro h
    obtain ⟨n,rfl⟩ := h.exists_nat_pow_eq
    induction n with
    | zero => exact Or.inl rfl
    | succ n ih =>
      rw [pow_succ',mul_apply]
      rcases ih SameCycle.rfl.pow_right with h | h
      · exact Or.inr (congrArg θ h)
      · exact Or.inl ((congrArg θ h).trans (hθ x))
  · rintro (rfl|rfl)
    · exact SameCycle.rfl
    · exact SameCycle.rfl.apply_right

omit [DecidableEq D] in
lemma card_fiber_involution (θ : Perm D) (hθ : ∀ d, θ (θ d) = d)
    (hne : ∀ d, θ d ≠ d) (c : Cycles θ) : Fintype.card (Fiber (SameCycle.setoid θ) c) = 2 := by
  let d := c.out
  have hd : Quotient.mk (SameCycle.setoid θ) d = c := c.out_eq
  have ht : Quotient.mk (SameCycle.setoid θ) (θ d) = c :=
    (Quotient.sound SameCycle.rfl.apply_left).trans hd
  let f : Bool → Fiber (SameCycle.setoid θ) c := fun b ↦ if b then ⟨θ d,ht⟩ else ⟨d,hd⟩
  have hf : Function.Bijective f := by
    constructor
    · intro a b hab
      have hab' := congrArg Subtype.val hab
      cases a <;> cases b <;> simp only [f,Bool.false_eq_true,ite_false,ite_true] at hab' ⊢
      · exact (hne d hab'.symm).elim
      · exact (hne d hab').elim
    · intro x
      have hx : θ.SameCycle d x.val := Quotient.exact (hd.trans x.property.symm)
      rcases (sameCycle_involution θ hθ _ _).mp hx with he | he
      · exact ⟨false,Subtype.ext he.symm⟩
      · exact ⟨true,Subtype.ext he.symm⟩
  exact (Fintype.card_congr (Equiv.ofBijective f hf)).symm.trans Fintype.card_bool

omit [DecidableEq D] in
lemma numCycles_involution (θ : Perm D) (hθ : ∀ d, θ (θ d) = d)
    (hne : ∀ d, θ d ≠ d) : 2 * numCycles θ = Fintype.card D := by
  have hh := card_fiber_sum (SameCycle.setoid θ)
  simp only [card_fiber_involution θ hθ hne,Finset.sum_const,Finset.card_univ,nsmul_eq_mul] at hh
  change 2 * Fintype.card (Cycles θ) = _
  simpa only [Cycles,Nat.mul_comm,Nat.cast_id] using hh

end

open Equiv Equiv.Perm
open scoped Classical
variable {D : Type*} [Fintype D] [DecidableEq D]

end KervaireRibbon

end

end OAI


