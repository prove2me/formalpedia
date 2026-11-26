-- Prove2me | Definitions.Def_Section5Verified_Section5OscillatorFactors
-- name    : Section5Verified_Section5OscillatorFactors
-- status  : Definition
-- author  : @stockfish-soup
-- created : 2026-11-26T19:42:37.117046+00:00
-- url     : https://prove2.me/theorems/f489523f-ecc0-5fbc-b9dc-c2f480dedac9
-- title:
--   Section5OscillatorFactors — verified interface
-- statement:
--   Finite register types, encodings, and structural interfaces used by the Section 5 supporting constructions. The included identities are required to make these definitions importable with their verified semantics.
-- source:
--   Supporting formalization for https://arxiv.org/html/2609.40331v3, Section 5; original source Solutions.Section5OscillatorFactors; mechanically extracted with exact Lean declaration spans.

import Definitions.Def_QAlgorithms_Defs_Fourier
import Definitions.Def_QuantumLTF_Example_HermiteModel
import Definitions.Def_QuantumLTF_Membership_Supplement_thm49_primitives
import Definitions.Def_QuantumLTF_Membership_gates12
import Definitions.Def_Section5Verified_Section5FourierCircuit
import Definitions.Def_Section5Verified_Section5QuadraticPhase
import Mathlib
section
set_option autoImplicit false

open QAlgorithms QuantumLTF.Membership Thm49Primitives

/-! Exact circuits for the position and momentum chirps in the discrete oscillator
factorization. Their approximation to oscillator evolution is a separate analytic
claim and is not asserted by these circuit identities. -/

def section5_elementary_adjoint {n : ℕ} (c : Circuit gates12 n) : Circuit gates12 n :=
  (c.map Thm49Primitives.GateApp.adj).reverse









noncomputable def section5_position_chirp (q : ℕ) (t : ℝ) : Matrix (Qubits q) (Qubits q) ℂ :=
  Matrix.diagonal (fun z => section5_phase (t*QuantumLTF.Example.scalarGrid z^2))

noncomputable def section5_momentum_chirp (q : ℕ) (t : ℝ) : Matrix (Qubits q) (Qubits q) ℂ :=
  star (section5_centered_fourier q)*section5_position_chirp q t*section5_centered_fourier q



noncomputable def section5_oscillator_chirps (q : ℕ) (a b : ℝ) :
    Matrix (Qubits q) (Qubits q) ℂ :=
  section5_momentum_chirp q a*section5_position_chirp q b*section5_momentum_chirp q a





end


