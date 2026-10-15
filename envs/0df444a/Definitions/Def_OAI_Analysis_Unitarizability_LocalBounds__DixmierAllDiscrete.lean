-- Prove2me | Definitions.Def_OAI_Analysis_Unitarizability_LocalBounds__DixmierAllDiscrete
-- name    : OAI_Analysis_Unitarizability_LocalBounds__DixmierAllDiscrete
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T07:37:09.286726+00:00
-- url     : https://prove2.me/theorems/8727cb0f-3427-4270-9a82-fed5108a98c0
-- title:
--   Row- and column-localized coefficient arrays of a Boolean edge mask
-- statement:
--   Let $G$ be a group, $I$ a finite set of labels with group elements $s=(s_i)_{i\in I}$, and $a:G\times I\to\{\mathrm{true},\mathrm{false}\}$ a Boolean mask. As for the masked operators, $(x,i)$ is regarded as an edge from the row vertex $x$ to the column vertex $xs_i$, and for a bit $b$ we write $[b]\in\mathbb{C}$ for $1$ if $b$ is true and $0$ otherwise. The file defines two complex coefficient arrays on $G\times I$.
--
--   1. **Row mask at $x_0\in G$.**
--   $$c^{\mathrm{row}}_{x_0}(x,i)=\begin{cases}[a(x,i)], & x=x_0,\\ 0, & x\ne x_0,\end{cases}$$
--   which keeps only the row-assigned edges leaving the single vertex $x_0$.
--   2. **Column mask at $y_0\in G$.**
--   $$c^{\mathrm{col}}_{y_0}(x,i)=\begin{cases}1-[a(x,i)], & xs_i=y_0,\\ 0, & xs_i\ne y_0,\end{cases}$$
--   which keeps only the column-assigned edges arriving at the single vertex $y_0$.
--
--   The file also records that all these coefficients have modulus at most $1$: for all $x,i$ one has $|c^{\mathrm{row}}_{x_0}(x,i)|\le1$, $\bigl|1-[a(x,i)]\bigr|\le1$ and $|c^{\mathrm{col}}_{y_0}(x,i)|\le1$, so each array defines a masked operator.
--
--   These arrays localize the oriented operator $T$ (coefficients $[a]$) and the complementary operator $A-T$ (coefficients $1-[a]$, where $A$ is the constant masked operator): the row of $T$ at $x_0$ coincides with the row at $x_0$ of the masked operator with coefficients $c^{\mathrm{row}}_{x_0}$, and the column of $A-T$ at $y_0$ coincides with the column at $y_0$ of the masked operator with coefficients $c^{\mathrm{col}}_{y_0}$. When the mask has at most $r$ row-assigned edges at every row and at most $r$ column-assigned edges at every column, the localized arrays are supported on at most $r$ labels, and a bound $b$ on the synthesis operators of small subfamilies of the vectors $v_i$ yields the row and column estimates $\le b^2$ required by the direct-sum obstruction.
--
--   **Formalization Note** The arrays are `Masked.rowMask a x₀` and `Masked.columnMask a s y₀`, functions `G → I → ℂ`; the three modulus bounds are `rowMask_norm`, `complement_norm` and `columnMask_norm`. Only `columnMask` uses the group multiplication.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/Unitarizability/LocalBounds.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Unitarizability/LocalBounds.lean by skeleton subtraction
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

namespace OAI

/-! Individual block row and column bounds from the endpoint assignment. -/
noncomputable section
namespace Dixmier
namespace Masked
open Finset
variable {G I K : Type*} [Group G] [Fintype I] [Fintype K]
local instance instDecidableEq_oAI_5 : DecidableEq G := Classical.decEq G
def rowMask (a : G → I → Bool) (x₀ x : G) (i : I) : ℂ :=
  if x = x₀ then boolComplex (a x i) else 0

def columnMask (a : G → I → Bool) (s : I → G) (y₀ x : G) (i : I) : ℂ :=
  if x * s i = y₀ then 1 - boolComplex (a x i) else 0

omit [Group G] [Fintype I] in
theorem rowMask_norm (a : G → I → Bool) (x₀ x : G) (i : I) : ‖rowMask a x₀ x i‖ ≤ 1 := by
  unfold rowMask
  split_ifs
  · exact bool_mask_norm a x i
  · simp

omit [Group G] [Fintype I] in
theorem complement_norm (a : G → I → Bool) (x : G) (i : I) : ‖1 - boolComplex (a x i)‖ ≤ 1 := by
  cases a x i <;> simp [boolComplex]

omit [Fintype I] in
theorem columnMask_norm (a : G → I → Bool) (s : I → G) (y₀ x : G) (i : I) :
    ‖columnMask a s y₀ x i‖ ≤ 1 := by
  unfold columnMask
  split_ifs
  · exact complement_norm a x i
  · simp

end Masked
end Dixmier

end

end OAI


