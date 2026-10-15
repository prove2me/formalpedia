-- Prove2me | Definitions.Def_OAI_Analysis_Unitarizability_FiniteSynthesis__DixmierAllDiscrete
-- name    : OAI_Analysis_Unitarizability_FiniteSynthesis__DixmierAllDiscrete
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T07:21:00.892691+00:00
-- url     : https://prove2.me/theorems/1801fce9-dc79-4f67-9f6f-5c297caad85b
-- title:
--   Synthesis operators of finite subfamilies and frame bounds for all small subfamilies
-- statement:
--   Let $I$ be an index set, $K$ a finite set and $v=(v_i)_{i\in I}$ a family in $\mathbb{C}^K$; inner products are conjugate-linear in the first argument. For a finite subset $J\subseteq I$, $\mathbb{C}^J$ denotes the Euclidean coordinate space on $J$ with standard basis $(e_i)_{i\in J}$.
--
--   1. **Synthesis operator.** The linear map $\Phi_J:\mathbb{C}^J\to\mathbb{C}^K$,
--   $$\Phi_J=\sum_{i\in J}v_i\,e_i^{*},\qquad\Phi_Jz=\sum_{i\in J}z_i\,v_i .$$
--   Its adjoint is the analysis operator, $(\Phi_J^*x)_i=\langle v_i,x\rangle$ for $x\in\mathbb{C}^K$ and $i\in J$; both formulas are recorded as lemmas.
--   2. **Frame bound for small subfamilies.** For $p\in\mathbb{N}$ and $b\in\mathbb{R}$, the family $v$ satisfies the bound $(p,b)$ if
--   $$\|\Phi_J\|\le b\qquad\text{for every finite }J\subseteq I\text{ with }|J|\le p .$$
--   The empty subfamily is included, so the condition forces $b\ge0$.
--
--   A frame bound says that any at most $p$ of the vectors behave like an orthonormal system up to the factor $b$: $\|\sum_{i\in J}z_iv_i\|\le b\|z\|$ and $\sum_{i\in J}|\langle v_i,x\rangle|^2\le b^2\|x\|^2$. In the construction each row and each column of a sparse mask activates only a few labels, and these subfamily bounds become operator-norm bounds for the masked operators; the development provides, for a finite index set with $n\ge2$ elements and a capacity $r\ge1$, families of unit vectors in $\mathbb{C}^{k}$, $k=\lceil2r\log(2n)\rceil_+$, satisfying the bound $(\min(2r,n),\,10)$.
--
--   **Formalization Note** `FiniteSynthesis.synthesis v J` is the sum over `i : J` of `InnerProductSpace.rankOne ℂ (v i) (EuclideanSpace.basisFun J ℂ i)`, with lemmas `synthesis_apply` and `synthesis_adjoint_apply`; `FrameBound v p b` is a `Prop` quantifying over all `J : Finset I` with `J.card ≤ p`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/Unitarizability/FiniteSynthesis.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Unitarizability/FiniteSynthesis.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the DixmierAllDiscrete mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_DixmierAllDiscrete
import Definitions.Def_OAI_Analysis_Unitarizability_KernelEnergy__DixmierAllDiscrete
import Definitions.Def_OAI_Analysis_Unitarizability_KernelObstruction__DixmierAllDiscrete
import Definitions.Def_OAI_Analysis_Unitarizability_Cocycle__DixmierAllDiscrete
import Definitions.Def_OAI_Analysis_Unitarizability_HilbertSum__DixmierAllDiscrete
import Definitions.Def_OAI_Analysis_Unitarizability_Triangular__DixmierAllDiscrete
import Definitions.Def_OAI_Analysis_Unitarizability_InvariantProjection__DixmierAllDiscrete
import Definitions.Def_OAI_Analysis_Unitarizability_SumObstruction__DixmierAllDiscrete
import Definitions.Def_OAI_Analysis_Unitarizability_SparseMask__DixmierAllDiscrete
import Definitions.Def_OAI_Analysis_Unitarizability_EndpointAssignment__DixmierAllDiscrete
import Definitions.Def_OAI_Analysis_Unitarizability_SparseSplitting__DixmierAllDiscrete
import Definitions.Def_OAI_Analysis_Unitarizability_Regular__DixmierAllDiscrete
import Definitions.Def_OAI_Analysis_Unitarizability_VectorMean__DixmierAllDiscrete
import Definitions.Def_OAI_Analysis_Unitarizability_FiniteSigns__DixmierAllDiscrete

namespace OAI

/-! Finite synthesis maps and their adjoints, with bounds for all small subfamilies. -/
noncomputable section
namespace Dixmier
namespace FiniteSynthesis
open scoped ComplexConjugate
variable {I K : Type*} [Fintype K]
local instance instDecidableEq_oAI : DecidableEq I := Classical.decEq I

def synthesis (v : I → EuclideanSpace ℂ K) (J : Finset I) :
    EuclideanSpace ℂ J →L[ℂ] EuclideanSpace ℂ K :=
  ∑ i : J, InnerProductSpace.rankOne ℂ (v i) (EuclideanSpace.basisFun J ℂ i)

@[simp] theorem synthesis_apply (v : I → EuclideanSpace ℂ K) (J : Finset I)
    (z : EuclideanSpace ℂ J) : synthesis v J z = ∑ i : J, z i • v i := by
  simp only [synthesis, _root_.sum_apply, InnerProductSpace.rankOne_apply, EuclideanSpace.basisFun_inner]

@[simp] theorem synthesis_adjoint_apply (v : I → EuclideanSpace ℂ K) (J : Finset I)
    (x : EuclideanSpace ℂ K) (i : J) : (synthesis v J).adjoint x i = inner ℂ (v i) x := by
  rw [← EuclideanSpace.basisFun_inner, ContinuousLinearMap.adjoint_inner_right]
  have h : synthesis v J (EuclideanSpace.basisFun J ℂ i) = v i := by
    simp [synthesis_apply, EuclideanSpace.basisFun_apply, PiLp.single_apply]
  rw [h]

/-- The synthesis operator bound on subfamily coordinate spaces,
including the empty subfamily. -/
def FrameBound (v : I → EuclideanSpace ℂ K) (p : ℕ) (b : ℝ) : Prop :=
  ∀ J : Finset I, J.card ≤ p → ‖synthesis v J‖ ≤ b

end FiniteSynthesis
end Dixmier

end

end OAI


