-- Prove2me | Definitions.Def_OAI_InformationTheory_AmplitudeDamping_CapacityConverse
-- name    : OAI_InformationTheory_AmplitudeDamping_CapacityConverse
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T21:24:38.717732+00:00
-- url     : https://prove2.me/theorems/9b1904ac-e12f-4f2b-a44f-92093450f584
-- title:
--   The uniform ensemble of the codewords of a quantum code
-- statement:
--   Fix a number $n\ge0$ of channel uses. States on $n$ qubits are $2^n\times2^n$ density matrices (positive semidefinite, trace one) indexed by bit strings in $\{0,1\}^n$. A code $C$ for $n$ uses consists of a number $M\ge1$ of messages, encoding density matrices $\rho_0,\dots,\rho_{M-1}$, and a decoding POVM $D_0,\dots,D_{M-1}$ (positive semidefinite matrices with $\sum_m D_m=I$). An ensemble consists of finitely many density matrices together with nonnegative weights summing to $1$.
--
--   The file defines a single object, the **code ensemble** of $C$: the ensemble whose signals are the $M$ codeword states $\rho_0,\dots,\rho_{M-1}$, each taken with the uniform weight
--
--   $$w_m=\frac1M,\qquad m=0,\dots,M-1 .$$
--
--   The decoding POVM of $C$ plays no role in it.
--
--   This construction links the operational notion of a code with the Holevo quantity, which is a supremum over ensembles: in the converse half of the capacity theorem, the Holevo value of the code ensemble, which never exceeds the Holevo quantity of the channel, controls how many messages a code with small average error can carry.
--
--   **Formalization Note** `codeEnsemble C : Ensemble n` has `size := C.messages`, constant weight `(C.messages : ℝ)⁻¹` and `signal := C.encoding`; the weight conditions are discharged from `C.messages_pos`, and the state condition is `C.encoding_state`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/InformationTheory/AmplitudeDamping/CapacityConverse.lean

-- Generated from openai/math@1581d4c lean/OAI/InformationTheory/AmplitudeDamping/CapacityConverse.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the AmplitudeDamping mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_AmplitudeDamping
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_Channel
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_MatrixDifferentiation
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_LogDetConvexity
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_LogDetEntropy
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_Pinching
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_GramMatrices
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_ScalarDeficit
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_ThermalEntropy
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_OutputConvexity
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_TensorEntropy
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_PureRecursion
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_StateEntropy
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_EntropyContinuity
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_BlockFactors
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_Naimark
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_HolevoInformation
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_OutputEntropy
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_EnsembleBounds
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_PhaseStates
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_PhaseProducts

namespace OAI

noncomputable section

section
open scoped BigOperators ComplexOrder MatrixOrder
open Matrix Filter
namespace GAD

def codeEnsemble {n : ℕ} (C : Code n) : Ensemble n where
  size := C.messages
  weight := fun _ ↦ (C.messages:ℝ)⁻¹
  weight_nonneg := fun _ ↦ by positivity
  weight_sum := by
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
    exact mul_inv_cancel₀ (by exact_mod_cast C.messages_pos.ne')
  signal := C.encoding
  signal_state := C.encoding_state

end GAD

end

open scoped BigOperators ComplexOrder MatrixOrder
open Matrix Filter
namespace GAD

end GAD

end

end OAI


