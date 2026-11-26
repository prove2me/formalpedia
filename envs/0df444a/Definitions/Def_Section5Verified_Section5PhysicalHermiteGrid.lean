-- Prove2me | Definitions.Def_Section5Verified_Section5PhysicalHermiteGrid
-- name    : Section5Verified_Section5PhysicalHermiteGrid
-- status  : Definition
-- author  : @stockfish-soup
-- created : 2026-11-26T19:56:19.302807+00:00
-- url     : https://prove2.me/theorems/aa633a69-d080-45c5-8fa6-f2a3cfec2be6
-- title:
--   Section5PhysicalHermiteGrid — verified interface
-- statement:
--   Finite register types, encodings, and structural interfaces used by the Section 5 supporting constructions. The included identities are required to make these definitions importable with their verified semantics.
-- source:
--   Supporting formalization for https://arxiv.org/html/2609.40331v3, Section 5; original source Solutions.Section5PhysicalHermiteGrid; mechanically extracted with exact Lean declaration spans.

import Definitions.Def_QAlgorithms_Defs_Basic
import Definitions.Def_QuantumLTF_Example_HermiteModel
import Definitions.Def_QuantumLTF_Membership_Supplement_band1D53
import Definitions.Def_QuantumLTF_Membership_Supplement_bandKet
import Definitions.Def_QuantumLTF_Membership_Supplement_bandWeight
import Definitions.Def_QuantumLTF_Membership_Supplement_hermCoeff
import Definitions.Def_QuantumLTF_Membership_Supplement_projDist
import Definitions.Def_QuantumLTF_Membership_flatReg
import Definitions.Def_QuantumLTF_Membership_splitReg
import Definitions.Def_Section5Verified_Section5FiniteCoefficientTransfer
import Mathlib
section
set_option autoImplicit false

open MeasureTheory QAlgorithms QuantumLTF.Example Aux_w_53_hermite

/-! Matching the exact physical Hermite grid normalization and bit convention. -/











noncomputable def section5_bit_grid_equiv (n q : ℕ) :
    (Fin n → Qubits q) ≃ (Fin n → Fin (2^q)) :=
  Equiv.piCongrRight (fun _ : Fin n => bitsEquivFin q)

noncomputable def section5_grid_bit_isometry (n q : ℕ) :
    EuclideanSpace ℂ (Fin n → Fin (2^q)) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin n → Qubits q) :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (section5_bit_grid_equiv n q).symm

noncomputable def section5_discrete_hermite_tensor (n q D : ℕ) (a : Fin n → Fin D) :
    EuclideanSpace ℂ (Fin n → Qubits q) :=
  WithLp.toLp 2 (fun z => ∏ i, discreteHermiteKet q (a i) (z i))



noncomputable def section5_bit_phase_state {n : ℕ} (w : EuclideanSpace ℝ (Fin n)) (q : ℕ) :
    EuclideanSpace ℂ (Fin n → Qubits q) :=
  section5_grid_bit_isometry n q (section5_finite_phase_state w (2^q))



end


