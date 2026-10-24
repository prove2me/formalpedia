-- Prove2me | Definitions.Def_PricingWithTips3DM_721c81b0ef1f027963cd70b6
-- name    : PricingWithTips3DM_721c81b0ef1f027963cd70b6
-- status  : Definition
-- author  : @qmaai2907271020
-- created : 2026-10-22T20:27:22.886002+00:00
-- url     : https://prove2.me/theorems/c6a78884-49ae-40f3-8931-6813602fab0e
-- title:
--   PricingWithTips 3DM dependency: CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.VerifierInput.Semantics.Helpers
-- statement:
--   A private, kernel-checked dependency module used by the formal NP-hardness proof for three-dimensional matching and Theorems 4.1 and 4.2 of arXiv:2507.10872.
-- source:
--   https://github.com/tanktechnology/CLRS-Lean

import Definitions.Def_PricingWithTips3DM_86c15828cc3b010c237f3dae
import Definitions.Def_PricingWithTips3DM_064f078de20caee0ad4073b8
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false

/-!
# Verifier-input arm semantic helpers

This layer states the exact pure predicate checked by one candidate
certificate-length arm and connects it to the arm's flat wire list.
-/

namespace CLRS.Chapter34.Turing.CookLevin

noncomputable section

/-- The stack bits have the verifier-input shape for the selected certificate
length: no earlier separator, one separator, and the fixed public suffix. -/
def VerifierInputArmMatches {Γ : Type} {L : Language Γ}
    (W : VerifierWitness L) (H : Nat) (x : List Γ)
    (bits : StackBits W.machine.tm H W.machine.tm.k₀) (length : Nat) : Prop :=
  ∃ hfit : length + 1 + x.length ≤ H,
    bits.height ⟨length + 1 + x.length, by omega⟩ = true ∧
    (∀ i : Fin length,
      bits.cell ⟨i.val, by omega⟩ (verifierInputCode W none) = false) ∧
    bits.cell ⟨length, by omega⟩ (verifierInputCode W none) = true ∧
    ∀ i : Fin x.length,
      bits.cell ⟨length + 1 + i.val, by omega⟩
        (verifierInputCode W (some (x.get i))) = true

namespace VerifierInput

def inputArmWires {Γ : Type} {L : Language Γ}
    (W : VerifierWitness L) (H : Nat) (x : List Γ)
    (stack : StackWires W.machine.tm H W.machine.tm.k₀)
    (separatorNots : Fin H → CircuitBuilder.Wire) (length : Nat)
    (hfit : length + 1 + x.length ≤ H) : List CircuitBuilder.Wire :=
  [stack.height ⟨length + 1 + x.length, by omega⟩] ++
  List.ofFn (fun i : Fin length => separatorNots ⟨i.val, by omega⟩) ++
  [stack.cell ⟨length, by omega⟩ (verifierInputCode W none)] ++
  List.ofFn (fun i : Fin x.length =>
    stack.cell ⟨length + 1 + i.val, by omega⟩
      (verifierInputCode W (some (x.get i))))

@[simp] theorem inputArmWires_length {Γ : Type} {L : Language Γ}
    (W : VerifierWitness L) (H : Nat) (x : List Γ)
    (stack : StackWires W.machine.tm H W.machine.tm.k₀)
    (separatorNots : Fin H → CircuitBuilder.Wire) (length : Nat)
    (hfit : length + 1 + x.length ≤ H) :
    (inputArmWires W H x stack separatorNots length hfit).length =
      length + x.length + 2 := by
  simp [inputArmWires, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

theorem inputArmWires_valid {Γ : Type} {L : Language Γ}
    (W : VerifierWitness L) (H : Nat) (x : List Γ)
    (base : CircuitBuilder)
    (stack : StackWires W.machine.tm H W.machine.tm.k₀)
    (hstack : stack.ValidIn base)
    (separatorNots : Fin H → CircuitBuilder.Wire)
    (hseparatorNots : ∀ cell, base.WireValid (separatorNots cell))
    (length : Nat) (hfit : length + 1 + x.length ≤ H) :
    ∀ wire ∈ inputArmWires W H x stack separatorNots length hfit,
      base.WireValid wire := by
  intro wire hwire
  simp only [inputArmWires, List.mem_append, List.mem_singleton,
    List.mem_ofFn] at hwire
  rcases hwire with ((hheight | hnots) | hseparator) | hfixed
  · subst wire; exact hstack.height _
  · rcases hnots with ⟨i, rfl⟩; exact hseparatorNots _
  · subst wire; exact hstack.cell _ _
  · rcases hfixed with ⟨i, rfl⟩; exact hstack.cell _ _

theorem inputArmWires_all_eq_true_iff {Γ : Type} {L : Language Γ}
    (W : VerifierWitness L) (H : Nat) (x : List Γ)
    (base : CircuitBuilder) (inputs : Nat → Bool)
    (stack : StackWires W.machine.tm H W.machine.tm.k₀)
    (separatorNots : Fin H → CircuitBuilder.Wire)
    (hseparatorEval : ∀ cell,
      base.evalWire inputs (separatorNots cell) =
        !(base.evalWire inputs
          (stack.cell cell (verifierInputCode W none))))
    (length : Nat) (hfit : length + 1 + x.length ≤ H) :
    (inputArmWires W H x stack separatorNots length hfit).all
        (fun wire => base.evalWire inputs wire) = true ↔
      VerifierInputArmMatches W H x (evalStackBits base inputs stack) length := by
  rw [List.all_eq_true]
  constructor
  · intro hall
    refine ⟨hfit, ?_, ?_, ?_, ?_⟩
    · exact hall _ (by simp [inputArmWires])
    intro i
    have hi := hall (separatorNots ⟨i.val, by omega⟩)
      (by simp [inputArmWires])
    rw [hseparatorEval] at hi
    change base.evalWire inputs
      (stack.cell ⟨i.val, by omega⟩ (verifierInputCode W none)) = false
    simpa only [Bool.not_eq_true'] using hi
    · exact hall _ (by simp [inputArmWires])
    · intro i
      exact hall _ (by simp [inputArmWires])
  · rintro ⟨_, hheight, hprefix, hseparator, hfixed⟩ wire hwire
    simp only [inputArmWires, List.mem_append, List.mem_singleton,
      List.mem_ofFn] at hwire
    rcases hwire with ((rfl | ⟨i, rfl⟩) | rfl) | ⟨i, rfl⟩
    · exact hheight
    · rw [hseparatorEval]
      have hi := hprefix i
      change base.evalWire inputs
        (stack.cell ⟨i.val, by omega⟩ (verifierInputCode W none)) = false at hi
      simp [hi]
    · exact hseparator
    · exact hfixed i

end VerifierInput

end

end CLRS.Chapter34.Turing.CookLevin


