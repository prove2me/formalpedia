-- Prove2me | Definitions.Def_Section5Verified_Section5GaussianProbabilityTransfer
-- name    : Section5Verified_Section5GaussianProbabilityTransfer
-- status  : Definition
-- author  : @stockfish-soup
-- created : 2026-11-26T19:50:07.256854+00:00
-- url     : https://prove2.me/theorems/14e6afdd-4d99-4f39-a536-daaa6317a628
-- title:
--   Section5GaussianProbabilityTransfer — verified interface
-- statement:
--   Finite register types, encodings, and structural interfaces used by the Section 5 supporting constructions. The included identities are required to make these definitions importable with their verified semantics.
-- source:
--   Supporting formalization for https://arxiv.org/html/2609.40331v3, Section 5; original source Solutions.Section5GaussianProbabilityTransfer; mechanically extracted with exact Lean declaration spans.

import Definitions.Def_QAlgorithms_Defs_Basic
import Definitions.Def_QuantumLTF_Example_HermiteModel
import Definitions.Def_QuantumLTF_Membership_Supplement_band1D53
import Definitions.Def_QuantumLTF_Membership_Supplement_bandKet
import Definitions.Def_QuantumLTF_Membership_Supplement_bandWeight
import Definitions.Def_QuantumLTF_Membership_Supplement_hermCoeff
import Definitions.Def_QuantumLTF_Membership_Supplement_projDist
import Definitions.Def_QuantumLTF_Membership_flatReg
import Definitions.Def_QuantumLTF_Membership_splitReg
import Definitions.Def_Section5Verified_Section5GaussianSampling
import Mathlib
section
set_option autoImplicit false

open MeasureTheory

/-! Normalized discretized Gaussian probabilities compared to the continuous Gaussian. -/

noncomputable def section5_normalized_sampled_gaussian (n M : ℕ) (hM : 0 < M) :
    Lp ℂ 2 (Measure.pi (fun _ : Fin n => (volume : Measure ℝ))) :=
  NormedSpace.normalize ((section5_sampled_gaussian_memLp n M hM).toLp
    (section5_sampled_gaussian_amplitude n M))





end


