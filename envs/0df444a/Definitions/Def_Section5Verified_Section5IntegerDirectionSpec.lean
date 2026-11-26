-- Prove2me | Definitions.Def_Section5Verified_Section5IntegerDirectionSpec
-- name    : Section5Verified_Section5IntegerDirectionSpec
-- status  : Definition
-- author  : @stockfish-soup
-- created : 2026-11-26T19:53:04.8571+00:00
-- url     : https://prove2.me/theorems/7d92a00f-6cff-41af-a49b-b4faf82480db
-- title:
--   Section5IntegerDirectionSpec — verified interface
-- statement:
--   Finite register types, encodings, and structural interfaces used by the Section 5 supporting constructions. The included identities are required to make these definitions importable with their verified semantics.
-- source:
--   Supporting formalization for https://arxiv.org/html/2609.40331v3, Section 5; original source Solutions.Section5IntegerDirectionSpec; mechanically extracted with exact Lean declaration spans.

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
import Definitions.Def_Section5Verified_Section5CanonicalPoweredDecoder
import Definitions.Def_Section5Verified_Section5DecoderLayout
import Definitions.Def_Section5Verified_Section5ExactMatrixPowerCircuit
import Definitions.Def_Section5Verified_Section5IntegerMatrixBounds
import Definitions.Def_Section5Verified_Section5IntegerSpectralBridge
import Definitions.Def_Section5Verified_Section5PhaseRecovery
import Mathlib
section
set_option autoImplicit false

open QAlgorithms QuantumLTF.Membership Thm49Primitives InnerProductSpace

namespace Section5DecoderLayout

/-- The basis-state guarantee for an acquired dyadic matrix. All other
registers start clean; no premise supplies a selected column or eigenvector. -/
def DirectionSpec (N K b f q : ℕ) (ε : ℝ) (circ : Circuit gatesRev (width N K b f)) : Prop :=
  ∀ z : Qubits (width N K b f), Clean (N:=N) (K:=K) (b:=b) (f:=f) z →
    (∀ s : Fin (K+1), 0 < s.val → ∀ i e,
      z (matrix (N:=N) (K:=K) (b:=b) (f:=f) s i e)=false) →
    let M := section5_signed_matrix_read (n:=N+1) (matrix (N:=N) (K:=K) (b:=b) (f:=f) 0) z
    IsSelfAdjoint (M.dyadicOperator q) →
    ∀ w : EuclideanSpace ℝ (Fin (N+1)), ‖w‖=1 →
      ‖M.dyadicOperator q-rankOne ℂ (section5_complexify w) (section5_complexify w)‖ ≤ ε/2000 →
      ∃ z' : Qubits (width N K b f), act circ.unitary (ket z)=ket z' ∧
        let v : EuclideanSpace ℝ (Fin (N+1)) := WithLp.toLp 2 fun i => readFp
          (⟨fun e => output N K b f i e.rev,
            fun _ _ h => Fin.rev_injective ((output N K b f i).injective h)⟩) f z'
        v ≠ 0 ∧ (‖NormedSpace.normalize v-w‖ ≤ ε/6 ∨ ‖NormedSpace.normalize v+w‖ ≤ ε/6)



end Section5DecoderLayout

end


