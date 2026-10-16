-- Prove2me | Definitions.Def_OAI_InformationTheory_AmplitudeDamping_PhaseStates
-- name    : OAI_InformationTheory_AmplitudeDamping_PhaseStates
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T21:21:26.350355+00:00
-- url     : https://prove2.me/theorems/087deb54-139c-46a5-b1dc-6942d86794ac
-- title:
--   Single-qubit channel output of a phase signal
-- statement:
--   Let $\gamma,\nu,p\in\mathbb{R}$ and let $s\in\{0,1\}$ be a sign bit. The phase signal is the qubit vector
--   $$\varphi_s(p)=\sqrt{1-p}\,|0\rangle+(-1)^s\sqrt{p}\,|1\rangle\in\mathbb{C}^2,$$
--   and the file defines its output under the single-qubit generalized amplitude-damping channel,
--   $$\Phi(\gamma,\nu,p,s)=\sum_{r=0}^{3}K_r\,\varphi_s(p)\varphi_s(p)^{*}K_r^{*},$$
--   where $K_0=\begin{pmatrix}\sqrt{1-\nu}&0\\0&\sqrt{1-\nu}\,\sqrt{1-\gamma}\end{pmatrix}$, $K_1=\begin{pmatrix}0&\sqrt{\gamma(1-\nu)}\\0&0\end{pmatrix}$, $K_2=\begin{pmatrix}\sqrt{\nu}\,\sqrt{1-\gamma}&0\\0&\sqrt{\nu}\end{pmatrix}$ and $K_3=\begin{pmatrix}0&0\\\sqrt{\gamma\nu}&0\end{pmatrix}$ are the Kraus operators of the channel (damping parameter $\gamma$, thermal parameter $\nu$) and $^*$ is the conjugate transpose. The file also proves that $\varphi_s(p)$ is a unit vector whenever $p\in[0,1]$, since $|\sqrt{1-p}|^2+|\sqrt p|^2=1$.
--
--   For $\gamma,\nu,p\in[0,1]$, with $q=(1-\gamma)p+\gamma\nu$, the output is the qubit density matrix
--   $$\Phi(\gamma,\nu,p,s)=\begin{pmatrix}1-q&(-1)^s\sqrt{1-\gamma}\sqrt{p(1-p)}\\ (-1)^s\sqrt{1-\gamma}\sqrt{p(1-p)}&q\end{pmatrix},$$
--   whose determinant is $v(\gamma,\nu,p)=\gamma\nu(1-\nu)+\gamma(1-\gamma)(p-\nu)^2$, so its entropy is $g(v(\gamma,\nu,p))$ with $g(u)=h\bigl(\tfrac{1+\sqrt{1-4u}}{2}\bigr)$, where $h(x)=-x\log x-(1-x)\log(1-x)$ is the binary entropy in nats. The equal mixture of the two outputs ($s=0,1$) is $\operatorname{diag}(1-q,q)$, of entropy $h(q)$. Thus the two phase signals with equal weights realize the single-qubit objective $h(q)-g(v(\gamma,\nu,p))$.
--
--   **Formalization Note** `phaseOutput γ ν p s` is `applyKraus (kraus γ ν) (pure (phaseSignal p s))`, where `phaseSignal` comes from the base definitions; the theorem `phaseSignal_mass` states `vecMass (phaseSignal p s) = 1` under `p ∈ Set.Icc 0 1`. `Real.sqrt` is $0$ on negative arguments.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/InformationTheory/AmplitudeDamping/PhaseStates.lean

-- Generated from openai/math@1581d4c lean/OAI/InformationTheory/AmplitudeDamping/PhaseStates.lean by skeleton subtraction
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

namespace OAI

noncomputable section

section
open scoped BigOperators ComplexOrder MatrixOrder
open Matrix
namespace GAD

end GAD

end

open scoped BigOperators ComplexOrder MatrixOrder
open Matrix
namespace GAD

def phaseOutput (γ ν p : ℝ) (s : Fin 2) : Matrix (Fin 2) (Fin 2) ℂ :=
  applyKraus (kraus γ ν) (pure (phaseSignal p s))

theorem phaseSignal_mass {p : ℝ} (hp : p ∈ Set.Icc (0:ℝ) 1) (s : Fin 2) :
    vecMass (phaseSignal p s) = 1 := by
  simp only [vecMass,Fin.sum_univ_two,phaseSignal,ite_true,show (1:Fin 2) ≠ 0 by decide,ite_false]
  split_ifs <;> simp [Complex.normSq_ofReal,Real.mul_self_sqrt hp.1,
    Real.mul_self_sqrt (sub_nonneg.mpr hp.2)]

end GAD

end

end OAI


