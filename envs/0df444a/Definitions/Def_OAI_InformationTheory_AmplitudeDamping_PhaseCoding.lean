-- Prove2me | Definitions.Def_OAI_InformationTheory_AmplitudeDamping_PhaseCoding
-- name    : OAI_InformationTheory_AmplitudeDamping_PhaseCoding
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T21:58:14.850256+00:00
-- url     : https://prove2.me/theorems/e8f0809d-b18a-4724-b60b-10515f384d4c
-- title:
--   Phase-flip unitaries and the eigenvalue weights of the averaged phase output
-- statement:
--   Let $\gamma,\nu,p\in\mathbb{R}$; in applications $\gamma,\nu\in[0,1]$ are the damping and environment parameters of the generalized amplitude-damping channel and $p\in[0,1]$ is the excitation probability of the input signals. The file defines:
--
--   1. **Sign unitary.** For a bit $s\in\{0,1\}$, the diagonal $2\times2$ unitary
--   $$Z^{s}=\begin{pmatrix}1&0\\0&(-1)^{s}\end{pmatrix},$$
--   that is, the identity for $s=0$ and the Pauli phase flip $Z=\operatorname{diag}(1,-1)$ for $s=1$.
--
--   2. **Mean phase weights.** The two-point weight vector
--   $$\mu_{\gamma,\nu,p}(0)=1-\eta,\qquad\mu_{\gamma,\nu,p}(1)=\eta,\qquad\eta=(1-\gamma)p+\gamma\nu .$$
--
--   The phase signals are the pure qubit states with amplitudes $(\sqrt{1-p},\pm\sqrt p)$ in the basis $|0\rangle,|1\rangle$. They are exchanged by $Z$, so the corresponding channel outputs are conjugate to each other by $Z^{s}$ and share a single spectrum. Averaging the two signals with equal weights and applying the single-qubit channel yields the diagonal state $\operatorname{diag}(1-\eta,\eta)$, whose eigenvalue distribution is $\mu_{\gamma,\nu,p}$; its entropy is the binary entropy $h(\eta)=-\eta\log\eta-(1-\eta)\log(1-\eta)$, the first term of the single-letter objective of the capacity formula. These objects let the phase-coding scheme be analysed with typical subspaces of product states.
--
--   **Formalization Note** `signUnitary s : Matrix.unitaryGroup (Fin 2) ℂ` is `diagonal (fun b ↦ if b = 0 ∨ s = 0 then 1 else -1)`, with unitarity checked by cases. `meanPhaseWeights γ ν p : Fin 2 → ℝ` carries no hypotheses on its parameters.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/InformationTheory/AmplitudeDamping/PhaseCoding.lean

-- Generated from openai/math@1581d4c lean/OAI/InformationTheory/AmplitudeDamping/PhaseCoding.lean by skeleton subtraction
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
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_CapacityConverse
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_SequentialMatrices
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_TypicalSets
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_TypicalProjectors
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_SequentialDecoder

namespace OAI

noncomputable section

universe u_1

section
open scoped BigOperators ComplexOrder MatrixOrder
open Matrix
namespace GAD

def signUnitary (s : Fin 2) : Matrix.unitaryGroup (Fin 2) ℂ :=
  ⟨Matrix.diagonal (fun b ↦ if b=0 ∨ s=0 then 1 else -1), by
    constructor <;> ext i j <;> fin_cases i <;> fin_cases j <;> fin_cases s <;>
      simp [Matrix.mul_apply,Fin.sum_univ_two,Matrix.star_apply]⟩

def meanPhaseWeights (γ ν p : ℝ) (b : Fin 2) : ℝ :=
  if b=0 then 1-((1-γ)*p+γ*ν) else (1-γ)*p+γ*ν

end GAD

end

open scoped BigOperators ComplexOrder MatrixOrder
open Matrix
namespace GAD

end GAD

end

end OAI


