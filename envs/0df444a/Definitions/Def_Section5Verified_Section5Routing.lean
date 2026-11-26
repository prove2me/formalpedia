-- Prove2me | Definitions.Def_Section5Verified_Section5Routing
-- name    : Section5Verified_Section5Routing
-- status  : Definition
-- author  : @stockfish-soup
-- created : 2026-11-26T19:38:21.58358+00:00
-- url     : https://prove2.me/theorems/b04bbee9-01ef-59e9-a3bd-4587093572d4
-- title:
--   Section5Routing — verified interface
-- statement:
--   Constructs actual two-qubit SWAP circuits for arbitrary embedded wire permutations, with at most one gate per embedded wire. Constructs the full outcome-dependent particle compaction family with at most 2*K*s gates per outcome, fixing all other wires and requiring no ancillas or oracle queries. Proves 2*K*(Nat.clog 2 n+1) <= (6/log 2)*K*log(n+1) for n>=1, establishing the required O(K log(n+1)) routing bound.
-- source:
--   Supporting formalization for https://arxiv.org/html/2609.40331v3, Section 5; original source Solutions.Section5Routing; mechanically extracted with exact Lean declaration spans.

import Definitions.Def_QuantumLTF_Membership_Supplement_symBand54
import Definitions.Def_QuantumLTF_Membership_gates12
import Mathlib
section
set_option autoImplicit false

open QAlgorithms QuantumLTF.Membership QuantumLTF.Membership.Supplement

/-! Explicit swap circuits for the outcome-dependent compaction in Theorem 5.4. -/

 theorem _root_.Section5UploadPrivate.Section5Routing.section5_routing_permutation_unitary {α : Type*} [Fintype α] [DecidableEq α]
    (e : Equiv.Perm α) :
    (fun y z => if y=e z then (1:ℂ) else 0) ∈ Matrix.unitaryGroup α ℂ := by
  classical
  apply Matrix.mem_unitaryGroup_iff.mpr
  ext y z
  change (∑ u : α, (if y=e u then (1:ℂ) else 0)*
    star (if z=e u then (1:ℂ) else 0)) = if y=z then 1 else 0
  rw [Finset.sum_eq_single (e.symm y)]
  · simp [eq_comm]
  · intro u hu hne
    have hh : y ≠ e u := by
      intro h
      exact hne (by rw [h,e.symm_apply_apply])
    rw [if_neg hh,zero_mul]
  · simp





def section5_swap_two : Equiv.Perm (Qubits 2) where
  toFun z := ![z 1,z 0]
  invFun z := ![z 1,z 0]
  left_inv z := by ext i; fin_cases i <;> simp
  right_inv z := by ext i; fin_cases i <;> simp

noncomputable def section5_swap_gate {m : ℕ} (i j : Fin m) (h : i ≠ j) : GateApp gates12 m where
  gate := ⟨2,fun y z => if y=section5_swap_two z then 1 else 0⟩
  mem := ⟨Section5UploadPrivate.Section5Routing.section5_routing_permutation_unitary section5_swap_two,by norm_num,by norm_num⟩
  wires := ⟨Fin.cons i (fun _ : Fin 1 => j), Fin.cons_injective_iff.mpr
    ⟨by rintro ⟨a,ha⟩; exact h ha.symm,fun _ _ _ => Subsingleton.elim _ _⟩⟩











def section5_particle_wire_permutation (K s : ℕ) (σ : Equiv.Perm (Fin (2*K))) :
    Equiv.Perm (Fin (2*K*s)) :=
  finProdFinEquiv.symm.trans ((Equiv.prodCongr σ (Equiv.refl (Fin s))).trans finProdFinEquiv)













end


