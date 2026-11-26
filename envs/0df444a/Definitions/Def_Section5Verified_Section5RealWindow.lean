-- Prove2me | Definitions.Def_Section5Verified_Section5RealWindow
-- name    : Section5Verified_Section5RealWindow
-- status  : Definition
-- author  : @stockfish-soup
-- created : 2026-11-26T19:42:37.776012+00:00
-- url     : https://prove2.me/theorems/a46fe2a2-2113-4189-b24b-9a8be0c2c034
-- title:
--   Section5RealWindow — verified interface
-- statement:
--   Finite register types, encodings, and structural interfaces used by the Section 5 supporting constructions. The included identities are required to make these definitions importable with their verified semantics.
-- source:
--   Supporting formalization for https://arxiv.org/html/2609.40331v3, Section 5; original source Solutions.Section5RealWindow; mechanically extracted with exact Lean declaration spans.

import Definitions.Def_QAlgorithms_Defs_Basic
import Definitions.Def_QuantumLTF_Example_HermiteModel
import Definitions.Def_QuantumLTF_Membership_Supplement_band1D53
import Definitions.Def_QuantumLTF_Membership_Supplement_bandKet
import Definitions.Def_QuantumLTF_Membership_Supplement_bandWeight
import Definitions.Def_QuantumLTF_Membership_Supplement_hermCoeff
import Definitions.Def_QuantumLTF_Membership_Supplement_projDist
import Definitions.Def_QuantumLTF_Membership_flatReg
import Definitions.Def_QuantumLTF_Membership_splitReg
import Definitions.Def_Section5Verified_Section5SignedWindow
import Mathlib
section
set_option autoImplicit false

open MeasureTheory ProbabilityTheory QuantumLTF.Membership QuantumLTF.Example

/-! A bounded signed window of the lattice integer gives a precision-independent
Gaussian coordinate approximation. -/

noncomputable def section5_real_window (P H : ℤ) (δ x : ℝ) : ℝ :=
  δ*(section5_window_truncate P H ⌊x/δ⌋ : ℝ)



noncomputable def section5_real_window_vec {n : ℕ} (P H : ℤ) (δ : ℝ)
    (x : EuclideanSpace ℝ (Fin n)) : EuclideanSpace ℝ (Fin n) :=
  WithLp.toLp 2 (fun i => section5_real_window P H δ (x i))





end


