-- Prove2me | Definitions.Def_OAI_InformationTheory_AmplitudeDamping_OutputConvexity
-- name    : OAI_InformationTheory_AmplitudeDamping_OutputConvexity
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T20:58:15.302636+00:00
-- url     : https://prove2.me/theorems/a3f32ec4-dd66-4e26-89c2-828ed3c6a8e6
-- title:
--   The qubit entropy function $s\mapsto g(s^2)$ and its derivative
-- statement:
--   Let $h(x)=-x\log x-(1-x)\log(1-x)$ be the binary entropy in nats and
--   $$g(u)=h\Bigl(\frac{1+\sqrt{1-4u}}{2}\Bigr);$$
--   for $u\in[0,\tfrac14]$, $g(u)$ is the von Neumann entropy of any qubit density matrix of determinant $u$, whose eigenvalues are $\tfrac{1\pm\sqrt{1-4u}}{2}$. For real $s$ and $t$ the file defines:
--
--   1. **Radius.** $r(s)=\sqrt{1-4s^2}$.
--   2. **Log-ratio.** $L(t)=\log(1+t)-\log(1-t)$; for $|t|<1$ this is $2\operatorname{artanh}t$.
--   3. **Entropy in terms of the square root of the determinant.** $W(s)=g(s^2)=h\bigl(\tfrac{1+r(s)}{2}\bigr)$.
--   4. **Slope.**
--   $$\sigma(s)=\frac{2s}{r(s)}\,L\bigl(r(s)\bigr).$$
--
--   For $0<s<\tfrac12$ the function $W$ is differentiable with $W'(s)=\sigma(s)$, and $\sigma$ is differentiable with $\sigma'(s)=2\bigl(L(r(s))-2r(s)\bigr)/r(s)^3$, which is nonnegative because $L(t)\ge2t$ for $0\le t<1$. Hence $W$ is convex and nondecreasing on $[0,\tfrac12]$. Since $p\mapsto\sqrt{v(\gamma,\nu,p)}$ is convex on $[0,1]$ with values in $[0,\tfrac12]$, where $v(\gamma,\nu,p)=\gamma\nu(1-\nu)+\gamma(1-\gamma)(p-\nu)^2$, it follows that $p\mapsto g(v(\gamma,\nu,p))=W(\sqrt{v(\gamma,\nu,p)})$ is convex on $[0,1]$ for $\gamma,\nu\in[0,1]$. This convexity, used through Jensen's inequality, carries the per-qubit lower bound on output entropies of the generalized amplitude-damping channel from pure inputs to mixed inputs and to ensemble averages.
--
--   **Formalization Note** The names are `radius`, `logRatio`, `wootters` and `woottersSlope`. In Lean, `Real.sqrt` is $0$ on negative arguments and division by zero is $0$, so $r(s)=0$ and $\sigma(s)=0$ for $|s|\ge\tfrac12$; these boundary values are not used.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/InformationTheory/AmplitudeDamping/OutputConvexity.lean

-- Generated from openai/math@1581d4c lean/OAI/InformationTheory/AmplitudeDamping/OutputConvexity.lean by skeleton subtraction
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

namespace OAI

noncomputable section
open scoped BigOperators Matrix.Norms.Elementwise
open Matrix
open scoped BigOperators ComplexOrder MatrixOrder
open scoped Matrix.Norms.Elementwise ComplexOrder MatrixOrder
open Matrix Set
open scoped ComplexOrder MatrixOrder
open scoped BigOperators Topology
open Filter Set
open scoped BigOperators ComplexOrder MatrixOrder Topology
open scoped BigOperators ComplexOrder

open scoped BigOperators
open Set Filter Topology

namespace GAD

def radius (s : ℝ) : ℝ := Real.sqrt (1 - 4 * s ^ 2)
def logRatio (t : ℝ) : ℝ := Real.log (1 + t) - Real.log (1 - t)
def wootters (s : ℝ) : ℝ := g (s ^ 2)
def woottersSlope (s : ℝ) : ℝ := 2 * s / radius s * logRatio (radius s)

end GAD

end

end OAI


