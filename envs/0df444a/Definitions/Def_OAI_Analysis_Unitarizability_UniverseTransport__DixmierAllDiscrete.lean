-- Prove2me | Definitions.Def_OAI_Analysis_Unitarizability_UniverseTransport__DixmierAllDiscrete
-- name    : OAI_Analysis_Unitarizability_UniverseTransport__DixmierAllDiscrete
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T07:37:58.466201+00:00
-- url     : https://prove2.me/theorems/be2cc68f-2f93-49ed-a851-cde3bc443955
-- title:
--   Pulling bounded functions back along a group isomorphism
-- statement:
--   Let $G$ and $Q$ be groups, each carrying the discrete topology, and let $e:G\to Q$ be a group isomorphism. Write $\ell^\infty(G)$ and $\ell^\infty(Q)$ for the spaces of bounded complex-valued functions on $G$ and on $Q$ (for the discrete topology every function is continuous). The **mean pullback** along $e$ is the $\mathbb{C}$-linear map
--   $$e^{*}:\ell^\infty(G)\to\ell^\infty(Q),\qquad (e^{*}f)(q)=f\bigl(e^{-1}(q)\bigr)\quad(q\in Q),$$
--   that is, $e^{*}f=f\circ e^{-1}$; the file records this evaluation formula as a simplification lemma.
--
--   Composing with $e^{*}$ transports means: if $m$ is a linear functional on $\ell^\infty(Q)$ with $m(\mathbf 1)=1$ that is positive and invariant under the left translations $(\lambda_qf)(x)=f(q^{-1}x)$, then $m\circ e^{*}$ has the same three properties on $\ell^\infty(G)$, because $e^{*}$ maps $\mathbf 1$ to $\mathbf 1$, preserves nonnegativity, and satisfies $e^{*}(\lambda_gf)=\lambda_{e(g)}(e^{*}f)$. Hence amenability is invariant under group isomorphisms. In the proof of the main theorem for all discrete groups this is used to replace a non-amenable group by an isomorphic copy in a larger type universe, in which the required Hilbert space can be built, without losing non-amenability.
--
--   **Formalization Note** Bounded functions are bounded continuous functions `G →ᵇ ℂ` for the discrete topology. The map is `meanPullback e`, defined by composing with `e.symm` and declared as a linear map only; `meanPullback_apply` is its evaluation formula. The groups $G$ and $Q$ may live in different universes.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/Unitarizability/UniverseTransport.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Unitarizability/UniverseTransport.lean by skeleton subtraction
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
import Definitions.Def_OAI_Analysis_Unitarizability_FiniteSynthesis__DixmierAllDiscrete
import Definitions.Def_OAI_Analysis_Unitarizability_SignMatrix__DixmierAllDiscrete
import Definitions.Def_OAI_Analysis_Unitarizability_Parameters__DixmierAllDiscrete
import Definitions.Def_OAI_Analysis_Unitarizability_FrameParameters__DixmierAllDiscrete
import Definitions.Def_OAI_Analysis_Unitarizability_ComplexFrames__DixmierAllDiscrete
import Definitions.Def_OAI_Analysis_Unitarizability_Frames__DixmierAllDiscrete
import Definitions.Def_OAI_Analysis_Unitarizability_Masked__DixmierAllDiscrete
import Definitions.Def_OAI_Analysis_Unitarizability_MaskAlgebra__DixmierAllDiscrete
import Definitions.Def_OAI_Analysis_Unitarizability_LocalBounds__DixmierAllDiscrete

namespace OAI

/-! Countability lets a group be represented in any universe.
Transport by group equivalences preserves the positive normalized invariant mean
and the bounded nonunitarizable witness. -/
noncomputable section
namespace Dixmier
universe u v w
open scoped BoundedContinuousFunction
variable {G : Type u} {Q : Type v} [Group G] [Group Q]
variable [TopologicalSpace G] [DiscreteTopology G]
variable [TopologicalSpace Q] [DiscreteTopology Q]

def meanPullback (e : G ≃* Q) : (G →ᵇ ℂ) →ₗ[ℂ] (Q →ᵇ ℂ) where
  toFun f := f.compContinuous ⟨e.symm, continuous_of_discreteTopology⟩
  map_add' f h := by ext q; rfl
  map_smul' z f := by ext q; rfl

omit [DiscreteTopology G] in
@[simp] theorem meanPullback_apply (e : G ≃* Q) (f : G →ᵇ ℂ) (q : Q) :
    meanPullback e f q = f (e.symm q) := rfl

end Dixmier

end

end OAI


