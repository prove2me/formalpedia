-- Prove2me | Definitions.Def_OAI_InformationTheory_AmplitudeDamping_CodingAsymptotics
-- name    : OAI_InformationTheory_AmplitudeDamping_CodingAsymptotics
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T22:01:59.703425+00:00
-- url     : https://prove2.me/theorems/5ae61d77-6a8d-427e-93e2-1410bbfb341f
-- title:
--   The one-message code and the message count $\lceil e^{nr}\rceil$
-- statement:
--   Codes for $n$ uses of a qubit channel are as in the capacity problem: a number $M\ge1$ of messages, encoding density matrices $\rho_0,\dots,\rho_{M-1}$ on $(\mathbb{C}^2)^{\otimes n}$, and a decoding POVM $D_0,\dots,D_{M-1}$ (positive semidefinite, summing to the identity). The file defines:
--
--   1. **Trivial code.** For every $n$, the code with a single message ($M=1$), encoded as the basis state $|0\cdots0\rangle\langle0\cdots0|$ in which every qubit is in $|0\rangle$, and decoded by the one-element POVM $\{I\}$.
--
--   2. **Message count at rate $r$.** For $r\in\mathbb{R}$ and $n\in\mathbb{N}$,
--   $$M_r(n)=\bigl\lceil e^{nr}\bigr\rceil\in\mathbb{N},$$
--   the number of messages of a code of rate $r$, measured in nats per channel use.
--
--   For channel parameters in $[0,1]$ the trivial code decodes without error, which shows that rate $0$ is achievable, so the set of achievable rates is nonempty. The count $M_r(n)$ is always at least $1$, satisfies $M_r(n)\le2e^{nr}$ when $r\ge0$, and for $n\ge1$ corresponds to a rate of at least $r/\log2$ bits per use; the achievability argument uses codes with exactly $M_r(n)$ messages.
--
--   **Formalization Note** The encoding state of `trivialCode n` is `phaseState 0 (fun _ ↦ 0)`, the product phase signal with $p=0$, which is $|0\cdots0\rangle\langle0\cdots0|$; its validity as a state is `phaseState_state`. `codingMessages r n` is `⌈Real.exp (n * r)⌉₊`, the natural-number ceiling.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/InformationTheory/AmplitudeDamping/CodingAsymptotics.lean

-- Generated from openai/math@1581d4c lean/OAI/InformationTheory/AmplitudeDamping/CodingAsymptotics.lean by skeleton subtraction
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
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_PhaseCoding

namespace OAI

noncomputable section

section
open scoped BigOperators ComplexOrder MatrixOrder
open Matrix Filter
namespace GAD

def trivialCode (n : ℕ) : Code n where
  messages := 1
  messages_pos := by norm_num
  encoding := fun _ ↦ phaseState 0 (fun _ ↦ 0)
  encoding_state := fun _ ↦ phaseState_state (by norm_num) _
  decoding := fun _ ↦ 1
  decoding_pos := fun _ ↦ Matrix.PosSemidef.one
  decoding_sum := by simp

end GAD

end

open Filter
namespace GAD

def codingMessages (r : ℝ) (n : ℕ) : ℕ := ⌈Real.exp ((n:ℝ)*r)⌉₊

end GAD

end

end OAI


