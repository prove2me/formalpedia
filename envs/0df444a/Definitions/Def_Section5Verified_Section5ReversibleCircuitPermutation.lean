-- Prove2me | Definitions.Def_Section5Verified_Section5ReversibleCircuitPermutation
-- name    : Section5Verified_Section5ReversibleCircuitPermutation
-- status  : Definition
-- author  : @stockfish-soup
-- created : 2026-11-26T19:41:04.994636+00:00
-- url     : https://prove2.me/theorems/f884758f-530a-4f58-b8fb-e0d4bc9bf458
-- title:
--   Section5ReversibleCircuitPermutation — verified interface
-- statement:
--   Finite register types, encodings, and structural interfaces used by the Section 5 supporting constructions. The included identities are required to make these definitions importable with their verified semantics.
-- source:
--   Supporting formalization for https://arxiv.org/html/2609.40331v3, Section 5; original source Solutions.Section5ReversibleCircuitPermutation; mechanically extracted with exact Lean declaration spans.

import Definitions.Def_QAlgorithms_Defs_Classical
import Definitions.Def_QuantumLTF_Membership_gatesRev
import Definitions.Def_Section5Verified_Section5ReversibleBooleanCompiler
import Mathlib
section
set_option autoImplicit false

open QAlgorithms QuantumLTF.Membership

/-! Every circuit over the published NOT/CNOT/Toffoli gate set acts as an exact
permutation of basis strings, including inputs with arbitrary workspace bits. -/

noncomputable def section5_embedded_basis_perm {k m : ℕ} (e : Fin k ↪ Fin m)
    (f : Equiv.Perm (Qubits k)) : Equiv.Perm (Qubits m) where
  toFun x := section5_replace_wires e x (f (x ∘ e))
  invFun x := section5_replace_wires e x (f.symm (x ∘ e))
  left_inv x := by
    dsimp only
    have hon : section5_replace_wires e x (f (x ∘ e)) ∘ e=f (x ∘ e) := by
      funext i
      exact section5_replace_wires_on e x _ i
    funext j
    by_cases hj : j ∈ Set.range e
    · obtain ⟨i,rfl⟩ := hj
      rw [section5_replace_wires_on,hon,Equiv.symm_apply_apply]
      rfl
    · rw [section5_replace_wires_off e _ _ j hj,section5_replace_wires_off e x _ j hj]
  right_inv x := by
    dsimp only
    have hon : section5_replace_wires e x (f.symm (x ∘ e)) ∘ e=f.symm (x ∘ e) := by
      funext i
      exact section5_replace_wires_on e x _ i
    funext j
    by_cases hj : j ∈ Set.range e
    · obtain ⟨i,rfl⟩ := hj
      rw [section5_replace_wires_on,hon,Equiv.apply_symm_apply]
      rfl
    · rw [section5_replace_wires_off e _ _ j hj,section5_replace_wires_off e x _ j hj]









end


