-- Prove2me | Definitions.Def_Section5Verified_Section5RationalReconstruction
-- name    : Section5Verified_Section5RationalReconstruction
-- status  : Definition
-- author  : @stockfish-soup
-- created : 2026-11-26T19:37:49.73419+00:00
-- url     : https://prove2.me/theorems/57d138e6-c121-5639-92c9-519646090eca
-- title:
--   Section5RationalReconstruction — verified interface
-- statement:
--   Finite register types, encodings, and structural interfaces used by the Section 5 supporting constructions. The included identities are required to make these definitions importable with their verified semantics.
-- source:
--   Supporting formalization for https://arxiv.org/html/2609.40331v3, Section 5; original source Solutions.Section5RationalReconstruction; mechanically extracted with exact Lean declaration spans.

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
import Mathlib
section
set_option autoImplicit false

open ContinuousLinearMap InnerProductSpace

/-! Computable rational-complex matrix powers and column selection, together with
their exact complex-operator semantics. No eigenvector oracle is used. -/

structure Section5RationalMatrix (n : ℕ) where
  re : Matrix (Fin n) (Fin n) ℚ
  im : Matrix (Fin n) (Fin n) ℚ

def Section5RationalMatrix.mul {n : ℕ} (A B : Section5RationalMatrix n) : Section5RationalMatrix n :=
  ⟨A.re*B.re-A.im*B.im,A.re*B.im+A.im*B.re⟩

def Section5RationalMatrix.one (n : ℕ) : Section5RationalMatrix n := ⟨1,0⟩

def Section5RationalMatrix.power {n : ℕ} (A : Section5RationalMatrix n) : ℕ → Section5RationalMatrix n
  | 0 => .one n
  | k+1 => (A.power k).mul A

noncomputable def Section5RationalMatrix.toComplex {n : ℕ} (A : Section5RationalMatrix n) :
    Matrix (Fin n) (Fin n) ℂ := fun i j => (A.re i j:ℂ)+(A.im i j:ℂ)*Complex.I

noncomputable def Section5RationalMatrix.operator {n : ℕ} (A : Section5RationalMatrix n) :
    EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n) :=
  (Matrix.toEuclideanLin A.toComplex).toContinuousLinearMap













def Section5RationalMatrix.columnScore {n : ℕ} (A : Section5RationalMatrix n) (j : Fin n) : ℚ :=
  ∑ i : Fin n,((A.re i j)^2+(A.im i j)^2)

def section5_max_index_fold {I : Type*} (score : I → ℚ) (l : List I) (j : I) : I :=
  l.foldl (fun b i => if score b < score i then i else b) j



def Section5RationalMatrix.bestColumn {n : ℕ} (A : Section5RationalMatrix n) (hn : 1 ≤ n) : Fin n :=
  section5_max_index_fold A.columnScore (List.finRange n) ⟨0,by omega⟩







def Section5RationalMatrix.realCandidate {n : ℕ} (A : Section5RationalMatrix n) (hn : 1 ≤ n) :
    Fin n → ℚ :=
  let j := A.bestColumn hn
  if (∑ i : Fin n,(A.im i j)^2) ≤ ∑ i : Fin n,(A.re i j)^2 then
    fun i => A.re i j else fun i => A.im i j





end


