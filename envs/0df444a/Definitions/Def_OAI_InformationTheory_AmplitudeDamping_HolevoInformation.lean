-- Prove2me | Definitions.Def_OAI_InformationTheory_AmplitudeDamping_HolevoInformation
-- name    : OAI_InformationTheory_AmplitudeDamping_HolevoInformation
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T21:14:50.348989+00:00
-- url     : https://prove2.me/theorems/89c445cd-81da-4700-8fd0-8d5e09f2cd94
-- title:
--   The error term of factor-based entropy continuity and uniform weights
-- statement:
--   1. **Factor error term.** For real numbers $\varepsilon,d$ and a natural number $D$,
--   $$E(\varepsilon,d,D)=\Bigl(\frac{d}{4\varepsilon}+\varepsilon\Bigr)\log D+\Bigl(1+\frac{d}{4\varepsilon}+\varepsilon\Bigr)\log2 .$$
--   It is affine in $d$, so $\sum_mw_m\,E(\varepsilon,d_m,D)=E\bigl(\varepsilon,\sum_mw_md_m,D\bigr)$ whenever $\sum_mw_m=1$, and it is nondecreasing in $d$ when $\varepsilon>0$ and $D\ge1$.
--   2. **Uniform weight.** For a finite set $\mathcal M$, $u_{\mathcal M}(m)=1/|\mathcal M|$ for every $m\in\mathcal M$. For nonempty $\mathcal M$ this is the uniform probability distribution, with Shannon entropy $\sum_m\eta(u_{\mathcal M}(m))=\log|\mathcal M|$, where $\eta(x)=-x\log x$.
--
--   The quantity $E(\varepsilon,\operatorname{mass}(X-Y),|\mathcal I|)$ is the right-hand side of the factor-based continuity bound for the von Neumann entropy $S$: for complex $\mathcal I\times\mathcal K$ matrices $X,Y$ with $\operatorname{mass}X=\operatorname{mass}Y=1$ (squared Frobenius norms) and $\mathcal I$ nonempty, $S(XX^*)-S(YY^*)\le E(\varepsilon,\operatorname{mass}(X-Y),|\mathcal I|)$ for every $\varepsilon>0$. With uniform weights it enters a Fano-type decoding bound: if $\mathcal I,\mathcal M$ are nonempty, $(A_m)_{m\in\mathcal M}$ are density matrices on $\mathbb{C}^{\mathcal I}$ and $(D_m)_{m\in\mathcal M}$ is a POVM on $\mathbb{C}^{\mathcal I}$, then for every $\varepsilon>0$
--   $$\log|\mathcal M|\le S\Bigl(\sum_m\tfrac{1}{|\mathcal M|}A_m\Bigr)-\sum_m\tfrac{1}{|\mathcal M|}S(A_m)+2\,E\bigl(\varepsilon,\,2(1-\bar p),\,|\mathcal I|\,|\mathcal M|\bigr),\qquad \bar p=\frac{1}{|\mathcal M|}\sum_m\operatorname{Re}\operatorname{tr}(D_mA_m),$$
--   which bounds the logarithm of the number of messages of a code by the Holevo quantity of its uniformly weighted code states plus an error term controlled by the average decoding error $1-\bar p$.
--
--   **Formalization Note** The names are `factorError ε d D`, with `D : ℕ` cast to a real number, and `uniformWeight μ m`, which ignores `m`. In Lean, division by zero gives $0$ (relevant only at $\varepsilon=0$) and `Real.log 0 = 0`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/InformationTheory/AmplitudeDamping/HolevoInformation.lean

-- Generated from openai/math@1581d4c lean/OAI/InformationTheory/AmplitudeDamping/HolevoInformation.lean by skeleton subtraction
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

namespace OAI

noncomputable section

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7

section
open scoped BigOperators ComplexOrder MatrixOrder
open Matrix
namespace GAD

def factorError (ε d : ℝ) (D : ℕ) : ℝ :=
  (d/(4*ε)+ε)*Real.log D+(1+d/(4*ε)+ε)*Real.log 2

variable {ι : Type u_2} {κ : Type u_3} {μ : Type u_4} [Fintype ι] [Fintype κ] [Fintype μ]
  [DecidableEq ι] [DecidableEq κ] [DecidableEq μ] [Nonempty ι] [Nonempty μ]

end GAD

end

open scoped BigOperators ComplexOrder MatrixOrder
open Matrix
namespace GAD
variable {ι : Type u_5} {μ : Type u_6} [Fintype ι] [Fintype μ] [DecidableEq ι] [DecidableEq μ]
  [Nonempty ι] [Nonempty μ]

def uniformWeight (μ : Type u_7) [Fintype μ] (_ : μ) : ℝ := (Fintype.card μ : ℝ)⁻¹

end GAD

end

end OAI


