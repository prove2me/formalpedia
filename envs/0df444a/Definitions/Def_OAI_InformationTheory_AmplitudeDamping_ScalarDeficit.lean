-- Prove2me | Definitions.Def_OAI_InformationTheory_AmplitudeDamping_ScalarDeficit
-- name    : OAI_InformationTheory_AmplitudeDamping_ScalarDeficit
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T20:56:38.483719+00:00
-- url     : https://prove2.me/theorems/1129ff00-14ee-4a61-aef7-1fe63f616fcf
-- title:
--   The scalar entropy deficit of a three-term spectrum and its logarithmic test function
-- statement:
--   Let $\eta(x)=-x\log x$ (natural logarithm, $\eta(0)=0$). For real numbers $x,y,z$ put $\sigma=x+y+z$.
--
--   1. **The two block eigenvalues.**
--   $$\lambda_\pm(x,y,z)=\frac{\sigma\pm\sqrt{\sigma^2-4yz}}{2}.$$
--   For $x,y,z\ge0$ these are the two nonnegative roots of $\lambda^2-\sigma\lambda+yz=0$, so $\lambda_++\lambda_-=x+y+z$ and $\lambda_+\lambda_-=yz$; they are the eigenvalues of the $2\times2$ matrix $\begin{pmatrix}x+y&\sqrt{xz}\\\sqrt{xz}&z\end{pmatrix}$.
--   2. **Scalar deficit.**
--   $$\Delta(x,y,z)=\eta(x)+\eta(y)+\eta(z)-\eta\bigl(\lambda_+(x,y,z)\bigr)-\eta\bigl(\lambda_-(x,y,z)\bigr).$$
--   3. **Signed five-point spectrum.** $\operatorname{spec}(x,y,z)=(x,\,y,\,z,\,\lambda_+,\,\lambda_-)\in\mathbb{R}^5$ with the sign vector $\epsilon=(1,1,1,-1,-1)$, so that $\Delta=\sum_{i=1}^{5}\epsilon_i\,\eta(\operatorname{spec}_i)$, and $\sum_i\epsilon_i\operatorname{spec}_i=0$ when $x,y,z\ge0$.
--   4. **Logarithmic test function.** For real $t$,
--   $$\delta(x,y,z,t)=\log\Bigl(1+\frac{x}{t}\Bigr)-\log\Bigl(1+\frac{t\,x}{(t+y)(t+z)}\Bigr),$$
--   which equals $\sum_{i=1}^{5}\epsilon_i\log(1+\operatorname{spec}_i/t)$ when $x,y,z\ge0$ and $t>0$.
--
--   The deficit is the scalar model of an entropy defect: for complex numbers $a,b,c$ with $|a|^2=x$, $|b|^2=y$, $|c|^2=z$, the Gram matrix of $\begin{pmatrix}a&b\\c&0\end{pmatrix}$ has eigenvalues $\lambda_\pm$, so $\Delta(x,y,z)$ is the sum of the entropies of the three entries minus the entropy of that Gram matrix. In general, for matrices $A,B,C$ of compatible shapes, $S(AA^*)+S(BB^*)+S(CC^*)-S(MM^*)\le\Delta(\operatorname{mass}A,\operatorname{mass}B,\operatorname{mass}C)$ with $M=\begin{pmatrix}A&B\\C&0\end{pmatrix}$, $S$ the von Neumann entropy and $\operatorname{mass}$ the squared Frobenius norm. The test function $\delta$ is the logarithmic counterpart used to verify such inequalities, and the file's companion results show that $\Delta$ is superadditive, positively homogeneous, nondecreasing in $y$ and $z$, and vanishes at $x=0$ (all for nonnegative arguments).
--
--   **Formalization Note** The names are `blockLambdaPlus`, `blockLambdaMinus`, `scalarDeficit`, `deficitSpectrum`, `deficitSigns` and `deficitLog`; $\eta$ is `Real.negMulLog`. `Real.sqrt` is $0$ on negative arguments, but for $x,y,z\ge0$ the discriminant is at least $(y-z)^2\ge0$; Lean's division by zero gives $0$, which only matters when $t=0$ or $(t+y)(t+z)=0$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/InformationTheory/AmplitudeDamping/ScalarDeficit.lean

-- Generated from openai/math@1581d4c lean/OAI/InformationTheory/AmplitudeDamping/ScalarDeficit.lean by skeleton subtraction
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

namespace OAI

universe u_1 u_2

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
open Matrix Set
namespace GAD

def blockLambdaPlus (x y z : ℝ) : ℝ :=
  ((x + y + z) + Real.sqrt ((x + y + z)^2 - 4*y*z)) / 2

def blockLambdaMinus (x y z : ℝ) : ℝ :=
  ((x + y + z) - Real.sqrt ((x + y + z)^2 - 4*y*z)) / 2

def scalarDeficit (x y z : ℝ) : ℝ :=
  Real.negMulLog x + Real.negMulLog y + Real.negMulLog z -
    Real.negMulLog (blockLambdaPlus x y z) - Real.negMulLog (blockLambdaMinus x y z)

def deficitSpectrum (x y z : ℝ) : Fin 5 → ℝ :=
  ![x, y, z, blockLambdaPlus x y z, blockLambdaMinus x y z]

def deficitSigns : Fin 5 → ℝ := ![1, 1, 1, -1, -1]

def deficitLog (x y z t : ℝ) : ℝ :=
  Real.log (1 + x/t) - Real.log (1 + t*x/((t+y)*(t+z)))

end GAD
open scoped BigOperators ComplexOrder
open Matrix Set
namespace GAD

end GAD

end

end OAI


