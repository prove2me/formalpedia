-- Prove2me | Definitions.Def_OAI_InformationTheory_AmplitudeDamping_LogDetEntropy
-- name    : OAI_InformationTheory_AmplitudeDamping_LogDetEntropy
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T20:53:07.750639+00:00
-- url     : https://prove2.me/theorems/b1e61971-6102-4ac9-a896-c60d77a8faf2
-- title:
--   An entropy primitive and the resolvent log-determinant $\log|\det(\mathbf{1}+rA)|$
-- statement:
--   Throughout, $\log$ is the natural logarithm with $\log 0=0$, and $\eta(x)=-x\log x$ (so $\eta(0)=0$).
--
--   1. **Entropy primitive.** For real numbers $a$ and $t$,
--   $$F_a(t)=(t+a)\log(t+a)-t\log t-a\log(t+1).$$
--   For every $a$, the function $t\mapsto F_a(t)$ is continuous on $[0,\infty)$, takes the value $F_a(0)=a\log a=-\eta(a)$ at $t=0$, and tends to $a$ as $t\to\infty$; for $a\ge0$ and $t>0$ its derivative is
--   $$F_a'(t)=\log\Bigl(1+\frac{a}{t}\Bigr)-\frac{a}{t+1}.$$
--   2. **Resolvent log-determinant.** For a finite index set $\mathcal I$, a real number $r$ and a complex $\mathcal I\times\mathcal I$ matrix $A$,
--   $$\operatorname{logDetShift}(r,A)=\log\bigl|\det(\mathbf 1+rA)\bigr|.$$
--   If $A$ is positive semidefinite with eigenvalues $\lambda_i$ and $r\ge0$, this equals $\sum_i\log(1+r\lambda_i)$.
--
--   The primitive converts inequalities between logarithms into inequalities between entropies: if real coefficients $c_i$ and numbers $a_i\ge0$ satisfy $\sum_ic_ia_i=0$ and $\sum_ic_i\log(1+a_i/t)\le0$ for every $t>0$, then $\sum_ic_i\,\eta(a_i)\le0$. Applied to eigenvalues through the resolvent log-determinant, this compares von Neumann entropies $S(A)=-\operatorname{tr}A\log A$ of positive semidefinite matrices of possibly different sizes: if $\operatorname{tr}A=\operatorname{tr}B$ and $\operatorname{logDetShift}(r,A)\le\operatorname{logDetShift}(r,B)$ for all $r>0$, then $S(A)\le S(B)$. A consequence is $S(AA^*)=S(A^*A)$ for every rectangular matrix $A$.
--
--   **Formalization Note** The names are `logEntropyPrimitive a t` and `logDetShift r A`. Lean's `Real.log` satisfies $\log 0=0$ and $\log x=\log|x|$ for $x<0$, so $F_a(t)$ is defined for all real $a,t$; the entropy in the comparison results is the project's `entropy`, the real part of the trace of $\eta(A)$ computed by the continuous functional calculus.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/InformationTheory/AmplitudeDamping/LogDetEntropy.lean

-- Generated from openai/math@1581d4c lean/OAI/InformationTheory/AmplitudeDamping/LogDetEntropy.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the AmplitudeDamping mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_AmplitudeDamping
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_Channel
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_MatrixDifferentiation
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_LogDetConvexity

namespace OAI

universe u_1 u_2 u_3 u_4 u_5

noncomputable section
open scoped BigOperators Matrix.Norms.Elementwise
open Matrix
open scoped BigOperators ComplexOrder MatrixOrder
open scoped Matrix.Norms.Elementwise ComplexOrder MatrixOrder
open Matrix Set
open scoped ComplexOrder MatrixOrder

open scoped BigOperators Topology
open Filter Set
namespace GAD

/-- A finite-spectrum primitive, continuous even at a zero eigenvalue. -/
def logEntropyPrimitive (a t : ℝ) : ℝ :=
  (t + a) * Real.log (t + a) - t * Real.log t - a * Real.log (t + 1)

end GAD

open scoped BigOperators ComplexOrder MatrixOrder Topology
open Matrix
namespace GAD
variable {ι : Type u_2} [Fintype ι] [DecidableEq ι]

def logDetShift (r : ℝ) (A : Matrix ι ι ℂ) : ℝ := Real.log ‖(1 + r • A).det‖

end GAD

end

end OAI


