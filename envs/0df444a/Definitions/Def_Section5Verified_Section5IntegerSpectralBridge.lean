-- Prove2me | Definitions.Def_Section5Verified_Section5IntegerSpectralBridge
-- name    : Section5Verified_Section5IntegerSpectralBridge
-- status  : Definition
-- author  : @stockfish-soup
-- created : 2026-11-26T19:42:12.997999+00:00
-- url     : https://prove2.me/theorems/763dad02-b2f2-41c2-95ec-e212bda70c34
-- title:
--   Section5IntegerSpectralBridge — verified interface
-- statement:
--   Finite register types, encodings, and structural interfaces used by the Section 5 supporting constructions. The included identities are required to make these definitions importable with their verified semantics.
-- source:
--   Supporting formalization for https://arxiv.org/html/2609.40331v3, Section 5; original source Solutions.Section5IntegerSpectralBridge; mechanically extracted with exact Lean declaration spans.

import Definitions.Def_QAlgorithms_Defs_Basic
import Definitions.Def_QAlgorithms_Defs_Circuit
import Definitions.Def_QAlgorithms_Defs_Classical
import Definitions.Def_QAlgorithms_Defs_Gates
import Definitions.Def_QuantumLTF_Example_HermiteModel
import Definitions.Def_QuantumLTF_Example_qex
import Definitions.Def_QuantumLTF_Membership_Supplement_band1D53
import Definitions.Def_QuantumLTF_Membership_Supplement_bandKet
import Definitions.Def_QuantumLTF_Membership_Supplement_bandWeight
import Definitions.Def_QuantumLTF_Membership_Supplement_bitonicTrace54
import Definitions.Def_QuantumLTF_Membership_Supplement_hermCoeff
import Definitions.Def_QuantumLTF_Membership_Supplement_lcgSym54ArithV2
import Definitions.Def_QuantumLTF_Membership_Supplement_projDist
import Definitions.Def_QuantumLTF_Membership_Supplement_symBand54
import Definitions.Def_QuantumLTF_Membership_Supplement_thm410_router_blocks
import Definitions.Def_QuantumLTF_Membership_Supplement_thm49_primitives
import Definitions.Def_QuantumLTF_Membership_disagree
import Definitions.Def_QuantumLTF_Membership_flatReg
import Definitions.Def_QuantumLTF_Membership_fpVal
import Definitions.Def_QuantumLTF_Membership_gates12
import Definitions.Def_QuantumLTF_Membership_gatesRev
import Definitions.Def_QuantumLTF_Membership_ltf
import Definitions.Def_QuantumLTF_Membership_readFp
import Definitions.Def_QuantumLTF_Membership_splitReg
import Definitions.Def_Section5Verified_Section5IntegerMatrixBounds
import Definitions.Def_Section5Verified_Section5RationalReconstruction
import Mathlib
section
set_option autoImplicit false

open ContinuousLinearMap InnerProductSpace

/-! Exact semantics for the integer circuit's dyadically scaled matrix powers.
Column maximization uses integer sums of squares; no eigenvector or square root
is part of the algorithm. -/



def Section5IntegerMatrix.toRational {n : ℕ} (A : Section5IntegerMatrix n) :
    Section5RationalMatrix n :=
  ⟨fun i j => (A.re i j:ℚ),fun i j => (A.im i j:ℚ)⟩







noncomputable def Section5IntegerMatrix.operator {n : ℕ} (A : Section5IntegerMatrix n) :
    EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n) := A.toRational.operator



noncomputable def Section5IntegerMatrix.dyadicOperator {n : ℕ}
    (A : Section5IntegerMatrix n) (q : ℕ) :
    EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n) :=
  ((2:ℂ)^q)⁻¹ • A.operator





def Section5IntegerMatrix.columnScore {n : ℕ} (A : Section5IntegerMatrix n) (j : Fin n) : ℤ :=
  ∑ i : Fin n,((A.re i j)^2+(A.im i j)^2)











def Section5IntegerMatrix.realCandidateAt {n : ℕ} (A : Section5IntegerMatrix n)
    (j : Fin n) : Fin n → ℤ :=
  if (∑ i : Fin n,(A.im i j)^2) ≤ ∑ i : Fin n,(A.re i j)^2 then
    fun i => A.re i j else fun i => A.im i j







end


