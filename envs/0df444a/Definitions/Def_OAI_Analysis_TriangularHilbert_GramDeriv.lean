-- Prove2me | Definitions.Def_OAI_Analysis_TriangularHilbert_GramDeriv
-- name    : OAI_Analysis_TriangularHilbert_GramDeriv
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T23:34:06.63799+00:00
-- url     : https://prove2.me/theorems/197b9a3a-0fde-4e14-a567-db69f0589a19
-- title:
--   Gradient of the energy along Gram matrices and Gram regularization
-- statement:
--   For complex square matrices, $\operatorname{tr}_{\mathbb R}(A)=\operatorname{Re}\operatorname{tr}A$ and $\langle X,Y\rangle=\operatorname{Re}\operatorname{tr}(X^*Y)$. The matrix energy of $P\ge0$ is $E(P)=\operatorname{Re}\operatorname{tr}(P\sqrt P)=\operatorname{tr}P^{3/2}$, and $\mathrm{sylv}_A(X)=AX+XA$.
--
--   1. **Gram gradient.** For matrices $R$ and $P$, the linear functional
--   $$
--   \mathrm{gramGradientAt}(R,P)[D]=3\,\langle R\sqrt P,\ D\rangle
--   $$
--   is the derivative of $R\mapsto E(R^*R)$ at $R$ in direction $D$, when $P=R^*R$ is positive definite.
--   2. **Regularization.** $\mathrm{gramRegularization}(\eta,R)=R^*R+\eta^2I$, a positive definite perturbation of the Gram matrix for $\eta\ne0$ that reduces to $R^*R$ at $\eta=0$. It is used to extend derivative formulas to singular Gram matrices by a limit.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/TriangularHilbert/GramDeriv.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/TriangularHilbert/GramDeriv.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the TriangularHilbert mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_TriangularHilbert
import Definitions.Def_OAI_Analysis_TriangularHilbert_Gaussian
import Definitions.Def_OAI_Analysis_TriangularHilbert_MeshMass
import Definitions.Def_OAI_Analysis_TriangularHilbert_GaussianMoments
import Definitions.Def_OAI_Analysis_TriangularHilbert_SignedWindowScalar
import Definitions.Def_OAI_Analysis_TriangularHilbert_MatrixSupport
import Definitions.Def_OAI_Analysis_TriangularHilbert_Support
import Definitions.Def_OAI_Analysis_TriangularHilbert_WeightedGram
import Definitions.Def_OAI_Analysis_TriangularHilbert_WeightedStar
import Definitions.Def_OAI_Analysis_TriangularHilbert_GroupedGaussian
import Definitions.Def_OAI_Analysis_TriangularHilbert_HeatStar
import Definitions.Def_OAI_Analysis_TriangularHilbert_HeatCost
import Definitions.Def_OAI_Analysis_TriangularHilbert_NormBounds
import Definitions.Def_OAI_Analysis_TriangularHilbert_HeatInsert
import Definitions.Def_OAI_Analysis_TriangularHilbert_GaussianDom
import Definitions.Def_OAI_Analysis_TriangularHilbert_PlaneChart
import Definitions.Def_OAI_Analysis_TriangularHilbert_PlaneDom
import Definitions.Def_OAI_Analysis_TriangularHilbert_HeatBound

namespace OAI

universe uι uE uF

section

namespace TriangularHilbert.MatrixEnergy
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator ComplexOrder BigOperators Topology
open Filter MeasureTheory
noncomputable section
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

def gramGradientAt (R P : Matrix ι ι ℂ) : Matrix ι ι ℂ →L[ℝ] ℝ :=
  (3 : ℝ) • traceRealCLM.comp ((ContinuousLinearMap.mul ℝ _) ((R * CFC.sqrt P)ᴴ))

@[simp] lemma gramGradientAt_apply (R P D : Matrix ι ι ℂ) :
    gramGradientAt R P D = 3 * hsReal (R * CFC.sqrt P) D := rfl

def gramRegularization (η : ℝ) (R : Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  regularize (Rᴴ * R) (η^2)

@[simp] lemma gramRegularization_zero (R : Matrix ι ι ℂ) :
    gramRegularization 0 R = Rᴴ * R := by simp [gramRegularization, regularize]

end
end TriangularHilbert.MatrixEnergy
end

end OAI


