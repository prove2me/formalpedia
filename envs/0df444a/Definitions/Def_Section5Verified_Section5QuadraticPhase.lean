-- Prove2me | Definitions.Def_Section5Verified_Section5QuadraticPhase
-- name    : Section5Verified_Section5QuadraticPhase
-- status  : Definition
-- author  : @stockfish-soup
-- created : 2026-11-26T19:38:10.491587+00:00
-- url     : https://prove2.me/theorems/4fdb73de-b2fe-4069-889b-51ca97925cd9
-- title:
--   Section5QuadraticPhase — verified interface
-- statement:
--   Explicit one- and two-qubit phase gates implement the mission's centered discrete position-square evolution exactly, with q^2+q+1 gates and no ancillas for q>0.
-- source:
--   Supporting formalization for https://arxiv.org/html/2609.40331v3, Section 5; original source Solutions.Section5QuadraticPhase; mechanically extracted with exact Lean declaration spans.

import Definitions.Def_QuantumLTF_Example_HermiteModel
import Definitions.Def_QuantumLTF_Membership_gates12
import Mathlib
section
set_option autoImplicit false

open QAlgorithms QuantumLTF.Membership

/-!
Quadratic phase circuits used in Jain--Iyer--Somma--Bao--Jordan,
Efficient Quantum Hermite Transform, arXiv:2510.04929, Section 3.1.
The arbitrary one- and two-qubit gate model permits exact phase angles.
-/

noncomputable def section5_phase (t : ℝ) : ℂ := Complex.exp ((t:ℂ)*Complex.I)





theorem section5_phase_star (t : ℝ) : section5_phase t*star (section5_phase t) = 1 := by
  change Complex.exp ((t:ℂ)*Complex.I)*starRingEnd ℂ (Complex.exp ((t:ℂ)*Complex.I)) = 1
  rw [← Complex.exp_conj, ← Complex.exp_add]
  simp

theorem section5_diagonal_phase_unitary {α : Type*} [Fintype α] [DecidableEq α]
    (t : α → ℝ) : Matrix.diagonal (fun z => section5_phase (t z)) ∈ Matrix.unitaryGroup α ℂ := by
  apply Matrix.mem_unitaryGroup_iff.mpr
  change Matrix.diagonal (fun z => section5_phase (t z)) *
    (Matrix.diagonal (fun z => section5_phase (t z))).conjTranspose = 1
  rw [Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal]
  ext y z
  by_cases h : y = z
  · subst z
    simp only [Matrix.diagonal_apply_eq, Matrix.one_apply_eq, Pi.star_apply]
    change section5_phase (t y)*star (section5_phase (t y)) = 1
    exact section5_phase_star _
  · simp [h]



noncomputable def section5_single_phase_gate {n : ℕ} (i : Fin n) (t : ℝ) : GateApp gates12 n where
  gate := ⟨1, Matrix.diagonal (fun z : Qubits 1 => section5_phase (if z 0 then t else 0))⟩
  mem := ⟨section5_diagonal_phase_unitary _, by norm_num, by norm_num⟩
  wires := ⟨fun _ => i, fun _ _ _ => Subsingleton.elim _ _⟩

noncomputable def section5_pair_phase_gate {n : ℕ} (i j : Fin n) (h : i ≠ j) (t : ℝ) :
    GateApp gates12 n where
  gate := ⟨2, Matrix.diagonal (fun z : Qubits 2 => section5_phase (if z 0 && z 1 then t else 0))⟩
  mem := ⟨section5_diagonal_phase_unitary _, by norm_num, by norm_num⟩
  wires := ⟨Fin.cons i (fun _ : Fin 1 => j), Fin.cons_injective_iff.mpr
    ⟨by rintro ⟨a,ha⟩; exact h ha.symm, fun _ _ _ => Subsingleton.elim _ _⟩⟩





noncomputable def section5_monomial_phase_gate {n : ℕ} (i j : Fin n) (t : ℝ) : GateApp gates12 n :=
  if h : i = j then section5_single_phase_gate i t else section5_pair_phase_gate i j h t





noncomputable def section5_quadratic_phase_circuit (n : ℕ) (a : Fin n → ℝ) (t : ℝ) :
    Circuit gates12 n :=
  (Finset.univ : Finset (Fin n×Fin n)).toList.map (fun p =>
    section5_monomial_phase_gate p.1 p.2 (t*a p.1*a p.2))







noncomputable def section5_linear_phase_circuit (n : ℕ) (a : Fin n → ℝ) (t : ℝ) :
    Circuit gates12 n :=
  (Finset.univ : Finset (Fin n)).toList.map (fun i => section5_single_phase_gate i (t*a i))





noncomputable def section5_global_phase_gate {n : ℕ} (hn : 0 < n) (t : ℝ) : GateApp gates12 n where
  gate := ⟨1, Matrix.diagonal (fun _ : Qubits 1 => section5_phase t)⟩
  mem := ⟨section5_diagonal_phase_unitary _, by norm_num, by norm_num⟩
  wires := ⟨fun _ => ⟨0,hn⟩, fun _ _ _ => Subsingleton.elim _ _⟩





noncomputable def section5_centered_quadratic_circuit (n : ℕ) (hn : 0 < n)
    (a : Fin n → ℝ) (c t : ℝ) : Circuit gates12 n :=
  section5_quadratic_phase_circuit n a t ++ section5_linear_phase_circuit n a (-2*t*c) ++
    [section5_global_phase_gate hn (t*c^2)]











end


