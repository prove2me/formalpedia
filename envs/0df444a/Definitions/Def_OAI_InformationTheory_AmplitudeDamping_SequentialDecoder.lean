-- Prove2me | Definitions.Def_OAI_InformationTheory_AmplitudeDamping_SequentialDecoder
-- name    : OAI_InformationTheory_AmplitudeDamping_SequentialDecoder
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T21:54:19.349984+00:00
-- url     : https://prove2.me/theorems/72e6f4a2-24c6-4d49-a159-aab4a999469d
-- title:
--   The sequential decoding measurement built from a pre-projection and codeword tests
-- statement:
--   Let $\iota$ be a finite index set, $M\in\mathbb{N}$, and let $P$ and $Q_0,\dots,Q_{M-1}$ be square complex matrices in $\mathbb{C}^{\iota\times\iota}$. The file defines:
--
--   1. **Zero-padded test sequence.** The infinite sequence $(\tilde Q_k)_{k\ge0}$ with $\tilde Q_k=Q_k$ for $k<M$ and $\tilde Q_k=0$ for $k\ge M$.
--
--   2. **Sequential measurement.** For $m\in\{0,\dots,M-1\}$, with the rejection product $R_m=(I-\tilde Q_{m-1})\cdots(I-\tilde Q_0)$ (and $R_0=I$),
--   $$\Lambda_m=(R_mP)^{*}\,Q_m\,(R_mP) .$$
--
--   When $P$ and the $Q_m$ are orthogonal projections, $\Lambda_m=P(I-Q_0)\cdots(I-Q_{m-1})\,Q_m\,(I-Q_{m-1})\cdots(I-Q_0)P$ is the measurement operator of the decoder that first projects onto the range of $P$ (for instance a typical subspace) and then tests $Q_0,Q_1,\dots$ in order, announcing message $m$ at the first accepted test. In that case each $\Lambda_m$ is positive semidefinite and $\sum_m\Lambda_m=P-PR_M^{*}R_MP\preceq I$, so the family is a sub-measurement that can be completed to a POVM; this is the decoder used to prove that rates below the Holevo quantity are achievable.
--
--   **Formalization Note** `finiteProjectors Q k` is `if h : k < M then Q ⟨k, h⟩ else 0`, and `sequentialMeasurement P Q m` is `(rejectProduct (finiteProjectors Q) m * P)ᴴ * Q m * (rejectProduct (finiteProjectors Q) m * P)`, where `rejectProduct` is the recursively defined product $R_0=I$, $R_{k+1}=(I-\tilde Q_k)R_k$. No hypotheses on $P$ or the $Q_m$ are part of the definitions.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/InformationTheory/AmplitudeDamping/SequentialDecoder.lean

-- Generated from openai/math@1581d4c lean/OAI/InformationTheory/AmplitudeDamping/SequentialDecoder.lean by skeleton subtraction
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

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe u_1

noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder
open Matrix
namespace GAD
variable {ι : Type u_1} [Fintype ι] [DecidableEq ι]

def finiteProjectors {M : ℕ} (Q : Fin M → Matrix ι ι ℂ) (k : ℕ) : Matrix ι ι ℂ :=
  if h : k<M then Q ⟨k,h⟩ else 0

def sequentialMeasurement {M : ℕ} (P : Matrix ι ι ℂ) (Q : Fin M → Matrix ι ι ℂ)
    (m : Fin M) : Matrix ι ι ℂ :=
  (rejectProduct (finiteProjectors Q) m*P)ᴴ*Q m*(rejectProduct (finiteProjectors Q) m*P)

end GAD

end

end OAI


