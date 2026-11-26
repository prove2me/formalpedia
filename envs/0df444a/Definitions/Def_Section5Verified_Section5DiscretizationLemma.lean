-- Prove2me | Definitions.Def_Section5Verified_Section5DiscretizationLemma
-- name    : Section5Verified_Section5DiscretizationLemma
-- status  : Definition
-- author  : @stockfish-soup
-- created : 2026-11-26T19:57:23.027016+00:00
-- url     : https://prove2.me/theorems/b9723521-7f46-58d2-a582-6f7cdf116fe2
-- title:
--   Section5DiscretizationLemma — verified interface
-- statement:
--   Finite register types, encodings, and structural interfaces used by the Section 5 supporting constructions. The included identities are required to make these definitions importable with their verified semantics.
-- source:
--   Supporting formalization for https://arxiv.org/html/2609.40331v3, Section 5; original source Solutions.Section5DiscretizationLemma; mechanically extracted with exact Lean declaration spans.

import Definitions.Def_QAlgorithms_Defs_Basic
import Definitions.Def_QAlgorithms_Defs_Gates
import Definitions.Def_QuantumLTF_Example_HermiteModel
import Definitions.Def_QuantumLTF_Example_qex
import Definitions.Def_QuantumLTF_Membership_Supplement_band1D53
import Definitions.Def_QuantumLTF_Membership_Supplement_bandKet
import Definitions.Def_QuantumLTF_Membership_Supplement_bandWeight
import Definitions.Def_QuantumLTF_Membership_Supplement_hermCoeff
import Definitions.Def_QuantumLTF_Membership_Supplement_projDist
import Definitions.Def_QuantumLTF_Membership_flatReg
import Definitions.Def_QuantumLTF_Membership_splitReg
import Definitions.Def_Section5Verified_Section5ExamplePhase
import Definitions.Def_Section5Verified_Section5GridPhaseMatchesQEX
import Definitions.Def_Section5Verified_Section5PhysicalHermiteGrid
import Mathlib
section
set_option autoImplicit false

open QAlgorithms QuantumLTF.Example QuantumLTF.Membership QuantumLTF.Membership.Supplement

/-! Lemma 5.1 for the exact QEX phase input and the public discrete Hermite kets. -/

noncomputable def section5_flatten_isometry (n q : ℕ) :
    EuclideanSpace ℂ (Fin n → Qubits q) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Qubits (n*q)) :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (section5_register_equiv n q)

noncomputable def section5_flat_hermite_tensor (n q D : ℕ) (a : Fin n → Fin D) :
    EuclideanSpace ℂ (Qubits (n*q)) :=
  section5_flatten_isometry n q (section5_discrete_hermite_tensor n q D a)



noncomputable def section5_qex_phase_input {n : ℕ} (w : EuclideanSpace ℝ (Fin n)) (q : ℕ) :
    EuclideanSpace ℂ (Qubits (n*q)) :=
  WithLp.toLp 2 (fun x => (ltf w 0 (gridPoint x) : ℂ)*section5_grid_amplitude x)









end


