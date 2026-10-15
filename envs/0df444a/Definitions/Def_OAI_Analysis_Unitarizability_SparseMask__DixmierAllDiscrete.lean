-- Prove2me | Definitions.Def_OAI_Analysis_Unitarizability_SparseMask__DixmierAllDiscrete
-- name    : OAI_Analysis_Unitarizability_SparseMask__DixmierAllDiscrete
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T07:09:25.879289+00:00
-- url     : https://prove2.me/theorems/775a25d8-f3b9-4c60-86e5-d735e1ccd833
-- title:
--   Row ones, column zeros and translation-difference sets of a Boolean edge mask
-- statement:
--   Let $G$ be a group, $I$ a finite set of labels and $s:I\to G$. Each pair $(x,i)\in G\times I$ is a labelled edge from the row vertex $x$ to the column vertex $xs_i$, so the edges arriving at a column $y$ are the pairs $(ys_i^{-1},i)$. A **mask** is a function $a:G\times I\to\{\mathrm{true},\mathrm{false}\}$; one reads $a(x,i)=\mathrm{true}$ as assigning the edge $(x,i)$ to its row endpoint and $\mathrm{false}$ as assigning it to its column endpoint. Labels are kept as elements of $I$ even when several values $s_i$ coincide. The file defines four finite subsets of $I$ and one scalar map.
--
--   1. **Row ones.** For $x\in G$, $\mathrm{Ones}_a(x)=\{i\in I:\ a(x,i)=\mathrm{true}\}$.
--   2. **Column zeros.** For $y\in G$, $\mathrm{Zeros}_{a,s}(y)=\{i\in I:\ a(ys_i^{-1},i)=\mathrm{false}\}$.
--   3. **Row difference.** For $g,x\in G$,
--   $$\Delta^{\mathrm{row}}_a(g,x)=\{i\in I:\ a(x,i)\neq a(g^{-1}x,i)\},$$
--   the labels at row $x$ where $a$ and its left translate $(x,i)\mapsto a(g^{-1}x,i)$ disagree.
--   4. **Column difference.** For $g,y\in G$,
--   $$\Delta^{\mathrm{col}}_{a,s}(g,y)=\{i\in I:\ a(ys_i^{-1},i)\neq a(g^{-1}ys_i^{-1},i)\}.$$
--   5. **Bits as scalars.** $[b]=1$ if $b=\mathrm{true}$ and $[b]=0$ if $b=\mathrm{false}$, as complex numbers; the file records $\bigl|[b]-[c]\bigr|\le1$ for all bits $b,c$.
--
--   A mask is sparse with capacity $r$ when $|\mathrm{Ones}_a(x)|\le r$ for every row $x$ and $|\mathrm{Zeros}_{a,s}(y)|\le r$ for every column $y$. A disagreement at row $x$ puts $i$ into $\mathrm{Ones}_a(x)\cup\mathrm{Ones}_a(g^{-1}x)$, and a disagreement at column $y$ puts $i$ into $\mathrm{Zeros}_{a,s}(y)\cup\mathrm{Zeros}_{a,s}(g^{-1}y)$, so sparsity bounds both difference sets by $\min(2r,|I|)$ uniformly in $g$. The difference sets are the row and column supports of the mask $[a(x,i)]-[a(g^{-1}x,i)]$, which describes the coboundary of an oriented masked operator under left translation; this is the combinatorial input for uniformly bounded coboundaries.
--
--   **Formalization Note** The mask is a curried function `a : G → I → Bool`; `rowOnes`, `columnZeros`, `rowDifference` and `columnDifference` are `Finset`s obtained by filtering `Finset.univ`, `boolComplex` is the bit-to-scalar map, and `difference_mask_norm` is the bound in item 5.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/Unitarizability/SparseMask.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Unitarizability/SparseMask.lean by skeleton subtraction
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

namespace OAI

/-! Finite support estimates for mask differences.
The label type is retained even when the products s_i collide. -/
namespace Dixmier

open Finset
variable {G I : Type*} [Group G] [Fintype I] [DecidableEq I]

noncomputable def rowOnes (a : G → I → Bool) (x : G) : Finset I :=
  univ.filter fun i => a x i = true

noncomputable def columnZeros (a : G → I → Bool) (s : I → G) (y : G) : Finset I :=
  univ.filter fun i => a (y * (s i)⁻¹) i = false

noncomputable def rowDifference (a : G → I → Bool) (g x : G) : Finset I :=
  univ.filter fun i => a x i ≠ a (g⁻¹ * x) i

noncomputable def columnDifference (a : G → I → Bool) (s : I → G)
    (g y : G) : Finset I :=
  univ.filter fun i => a (y * (s i)⁻¹) i ≠ a (g⁻¹ * (y * (s i)⁻¹)) i

def boolComplex (b : Bool) : ℂ := if b then 1 else 0

/-- The scalar difference mask has absolute value at most one. -/
theorem difference_mask_norm (b c : Bool) : ‖boolComplex b - boolComplex c‖ ≤ 1 := by
  cases b <;> cases c <;> simp [boolComplex]

end Dixmier

end OAI


