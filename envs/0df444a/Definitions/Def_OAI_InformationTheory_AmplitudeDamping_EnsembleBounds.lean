-- Prove2me | Definitions.Def_OAI_InformationTheory_AmplitudeDamping_EnsembleBounds
-- name    : OAI_InformationTheory_AmplitudeDamping_EnsembleBounds
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T21:18:41.279641+00:00
-- url     : https://prove2.me/theorems/fe3073fb-e8c1-4d10-a824-af91448d0632
-- title:
--   One-bit marginals of a function on bit strings
-- statement:
--   Let $n\ge0$ and let $q:\{0,1\}^n\to\mathbb{R}$ be a real function on bit strings $i=(i_0,\dots,i_{n-1})$. For a site $j\in\{0,\dots,n-1\}$ the file defines
--   $$\pi_j(q)=\sum_{i\in\{0,1\}^n:\ i_j=1}q(i).$$
--   When $q$ is a probability distribution, $\pi_j(q)$ is the probability that the $j$-th bit equals $1$, i.e. the parameter of the $j$-th one-bit marginal of $q$; no positivity or normalization is assumed in the definition.
--
--   The marginals express subadditivity of entropy: for a probability distribution $q$ on $\{0,1\}^n$, $\sum_i\eta(q(i))\le\sum_jh(\pi_j(q))$, where $\eta(x)=-x\log x$ and $h$ is the binary entropy. Applied to diagonals of density matrices this gives $S(P)\le\sum_jh(\pi_j(P))$ for $n$-qubit density matrices, with $\pi_j(P)$ the $|1\rangle$-population of qubit $j$, and hence the output-entropy upper bound $S(\mathcal N_n(P))\le\sum_jh\bigl((1-\gamma)\pi_j(P)+\gamma\nu\bigr)$ for the generalized amplitude-damping channel with $\gamma,\nu\in[0,1]$. Together with the matching lower bound this bounds the Holevo quantity of every $n$-qubit ensemble by $n$ times the maximum of the single-qubit objective $h((1-\gamma)p+\gamma\nu)-g(v(\gamma,\nu,p))$ over $p\in[0,1]$, where $g(u)=h\bigl(\tfrac{1+\sqrt{1-4u}}{2}\bigr)$ and $v(\gamma,\nu,p)=\gamma\nu(1-\nu)+\gamma(1-\gamma)(p-\nu)^2$.
--
--   **Formalization Note** The name is `distPopulation q j` for `q : Basis n → ℝ`, where `Basis n = Fin n → Fin 2`. The Holevo bound mentioned is measured in nats.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/InformationTheory/AmplitudeDamping/EnsembleBounds.lean

-- Generated from openai/math@1581d4c lean/OAI/InformationTheory/AmplitudeDamping/EnsembleBounds.lean by skeleton subtraction
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

namespace OAI

noncomputable section

section
open scoped BigOperators
namespace GAD

def distPopulation {n : ℕ} (q : Basis n → ℝ) (j : Fin n) : ℝ :=
  ∑ i, if i j=1 then q i else 0

end GAD

end

open scoped BigOperators ComplexOrder MatrixOrder
open Matrix
namespace GAD

end GAD

end

end OAI


