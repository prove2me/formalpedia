-- Prove2me | Definitions.Def_OAI_InformationTheory_AmplitudeDamping_Naimark
-- name    : OAI_InformationTheory_AmplitudeDamping_Naimark
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T21:12:08.052752+00:00
-- url     : https://prove2.me/theorems/457e3c13-5f2a-48be-98b8-7e6ccb60cfc8
-- title:
--   Naimark isometry of a measurement and weighted concatenation of factor matrices
-- statement:
--   Let $\mathcal I$, $\mathcal K$ and $\mathcal M$ be finite index sets; $A^*$ is the conjugate transpose and $|m\rangle$ the standard basis vector of $\mathbb{C}^{\mathcal M}$.
--
--   1. **Naimark matrix.** Let $(D_m)_{m\in\mathcal M}$ be positive semidefinite complex $\mathcal I\times\mathcal I$ matrices, and let $F_m$ be the spectral factor of $D_m$: if $D_m=U_m\operatorname{diag}(\lambda^{(m)})U_m^*$ with $U_m$ unitary (orthonormal eigenvectors as columns) and eigenvalues $\lambda^{(m)}\ge0$, then $F_m=U_m\operatorname{diag}\bigl(\sqrt{\lambda^{(m)}}\bigr)$, so that $F_mF_m^*=D_m$. The Naimark matrix is the $(\mathcal I\times\mathcal M)\times\mathcal I$ matrix whose $m$-th block of rows is $F_m^*$:
--   $$V_{(i,m),j}=\overline{(F_m)_{ji}},\qquad\text{i.e.}\qquad Vx=\sum_{m\in\mathcal M}F_m^*x\otimes|m\rangle .$$
--   Hence $V^*V=\sum_mF_mF_m^*=\sum_mD_m$, and $V$ is an isometry whenever $\sum_mD_m=\mathbf 1$, that is, whenever $(D_m)$ is a POVM.
--   2. **Weighted concatenation.** For real weights $(w_m)_{m\in\mathcal M}$ and matrices $X_m\in\mathbb{C}^{\mathcal I\times\mathcal K}$, $\operatorname{cat}_w(X)$ is the $\mathcal I\times(\mathcal M\times\mathcal K)$ matrix
--   $$\operatorname{cat}_w(X)_{i,(m,k)}=\sqrt{w_m}\,(X_m)_{ik},$$
--   the side-by-side juxtaposition of the blocks $\sqrt{w_m}\,X_m$. For $w\ge0$ its Gram matrix is the mixture $\operatorname{cat}_w(X)\operatorname{cat}_w(X)^*=\sum_mw_m\,X_mX_m^*$.
--
--   For a POVM $(D_m)$ and density matrices $A_m$ with spectral factors $G_m$ ($G_mG_m^*=A_m$), the mass (squared Frobenius norm) of the $m$-th block of $VG_m$ is the success probability $\operatorname{Re}\operatorname{tr}(D_mA_m)$; so when decoding succeeds with high probability, the dilated factors $VG_m$ are close to factors supported in mutually orthogonal blocks. Weighted concatenation turns the mixture $\sum_mw_mA_m$ into a single Gram matrix, so that entropy continuity for factors applies to a whole ensemble. Together these yield a Fano-type inequality that bounds $\log|\mathcal M|$ by the Holevo quantity of the uniformly weighted ensemble $(A_m)$ plus an error term controlled by the average decoding error.
--
--   **Formalization Note** `naimark D hD` takes the positivity proofs `hD` in order to form the spectral factors `spectralFactor (hD m)`, so it depends on Mathlib's choice of eigenbases; `concatenate w X` uses `Real.sqrt`, which is $0$ at negative weights.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/InformationTheory/AmplitudeDamping/Naimark.lean

-- Generated from openai/math@1581d4c lean/OAI/InformationTheory/AmplitudeDamping/Naimark.lean by skeleton subtraction
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

namespace OAI

noncomputable section

universe u_1 u_2 u_3 u_4 u_5

section
open scoped BigOperators ComplexOrder MatrixOrder
open Matrix
namespace GAD
variable {ι : Type u_1} {μ : Type u_2} [Fintype ι] [Fintype μ] [DecidableEq ι] [DecidableEq μ]

def naimark (D : μ → Matrix ι ι ℂ) (hD : ∀ m, (D m).PosSemidef) : Matrix (ι × μ) ι ℂ :=
  fun im j ↦ star (spectralFactor (hD im.2) j im.1)

end GAD

end

open scoped BigOperators ComplexOrder MatrixOrder
open Matrix
namespace GAD
variable {ι : Type u_3} {κ : Type u_4} {μ : Type u_5} [Fintype ι] [Fintype κ] [Fintype μ]

def concatenate (w : μ → ℝ) (X : μ → Matrix ι κ ℂ) : Matrix ι (μ × κ) ℂ :=
  fun i mk ↦ (Real.sqrt (w mk.1):ℂ)*X mk.1 i mk.2

variable [DecidableEq ι] [DecidableEq κ] [DecidableEq μ]

end GAD

end

end OAI


