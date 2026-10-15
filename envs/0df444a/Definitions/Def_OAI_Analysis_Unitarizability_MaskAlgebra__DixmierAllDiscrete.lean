-- Prove2me | Definitions.Def_OAI_Analysis_Unitarizability_MaskAlgebra__DixmierAllDiscrete
-- name    : OAI_Analysis_Unitarizability_MaskAlgebra__DixmierAllDiscrete
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T07:33:05.200349+00:00
-- url     : https://prove2.me/theorems/6403d3c5-4542-4097-83b1-47828de69b02
-- title:
--   Constant and Boolean-oriented masked operators on $\ell^2(G;\mathbb{C}^K)$
-- statement:
--   Let $G$ be a group, $I$ and $K$ finite sets, and $\mathcal H=\ell^2(G;\mathbb{C}^K)$ the Hilbert space of square-summable functions $\xi:G\to\mathbb{C}^K$; the inner product $\langle\cdot,\cdot\rangle$ of $\mathbb{C}^K$ is conjugate-linear in its first argument. Fix vectors $v=(v_i)_{i\in I}$ in $\mathbb{C}^K$ and group elements $s=(s_i)_{i\in I}$. For a coefficient array $c:G\times I\to\mathbb{C}$ with $|c(x,i)|\le 1$ for all $x,i$, the masked operator of the project is
--   $$(M_{v,s,c}\,\xi)(x)=\sum_{i\in I}c(x,i)\,\langle v_i,\xi(xs_i)\rangle\,v_i\qquad(x\in G).$$
--   For a bit $b$ write $[b]\in\mathbb{C}$ for $1$ if $b$ is true and $0$ if $b$ is false. The file defines two special masked operators.
--
--   1. **Constant masked operator.** $A_{v,s}=M_{v,s,\mathbf 1}$, the masked operator whose coefficients all equal $1$:
--   $$(A_{v,s}\,\xi)(x)=\sum_{i\in I}\langle v_i,\xi(xs_i)\rangle\,v_i .$$
--   2. **Oriented masked operator.** For a Boolean mask $a:G\times I\to\{\mathrm{true},\mathrm{false}\}$, $T_{v,s,a}=M_{v,s,[a]}$ with coefficients $c(x,i)=[a(x,i)]$:
--   $$(T_{v,s,a}\,\xi)(x)=\sum_{i\in I:\ a(x,i)=\mathrm{true}}\langle v_i,\xi(xs_i)\rangle\,v_i .$$
--   The admissibility condition $\bigl|[a(x,i)]\bigr|\le 1$ needed to form this masked operator is recorded as a separate lemma.
--
--   Regard $(x,i)$ as an edge from $x$ to $xs_i$. The constant operator uses every edge and commutes with the left translations $(\lambda(g)\xi)(x)=\xi(g^{-1}x)$; its block at position $(1,g)$ is the collision kernel $\sum_{i:\,s_i=g}v_iv_i^{*}$, so for unit vectors $v_i$ its kernel energy is at least $|I|$. The oriented operator keeps the edges that the mask assigns to their row endpoint, and $A_{v,s}-T_{v,s,a}$ keeps the others. Conjugation by $\lambda(g)$ replaces the coefficients $c(x,i)$ by $c(g^{-1}x,i)$, so the coboundary $T_{v,s,a}-\lambda(g)T_{v,s,a}\lambda(g^{-1})$ is again a masked operator, with coefficients $[a(x,i)]-[a(g^{-1}x,i)]$. In the construction of non-unitarizable representations of non-amenable groups, these two operators, built on words of length $j+1$, are the stage operators $A_j$ and $T_j$.
--
--   **Formalization Note** `Masked.constant v s` and `Masked.oriented v s a` are `Masked.operator` with the coefficient arrays `fun _ _ => 1` and `fun x i => boolComplex (a x i)`. The mask is curried, `a : G → I → Bool`, and `bool_mask_norm` is the bound $\bigl|[a(x,i)]\bigr|\le 1$, which uses no group structure.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/Unitarizability/MaskAlgebra.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Unitarizability/MaskAlgebra.lean by skeleton subtraction
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

namespace OAI

/-! Sparse masks yield operator conjugation identities, and the
constant mask has a rank-one collision kernel. -/
noncomputable section
namespace Dixmier
namespace Masked
open Finset
open scoped ComplexConjugate
variable {G I K : Type*} [Group G] [Fintype I] [Fintype K]
local instance instDecidableEq_oAI_3 : DecidableEq G := Classical.decEq G
def constant (v : I → Fibre K) (s : I → G) : Space G K →L[ℂ] Space G K :=
  operator v s (fun _ _ => 1) (fun _ _ => by simp)

omit [Group G] [Fintype I] in
theorem bool_mask_norm (a : G → I → Bool) (x : G) (i : I) : ‖boolComplex (a x i)‖ ≤ 1 := by
  cases a x i <;> simp [boolComplex]

def oriented (v : I → Fibre K) (s : I → G) (a : G → I → Bool) : Space G K →L[ℂ] Space G K :=
  operator v s (fun x i => boolComplex (a x i)) (bool_mask_norm a)

end Masked
end Dixmier

end

end OAI


