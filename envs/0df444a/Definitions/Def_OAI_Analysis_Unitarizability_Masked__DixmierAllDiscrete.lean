-- Prove2me | Definitions.Def_OAI_Analysis_Unitarizability_Masked__DixmierAllDiscrete
-- name    : OAI_Analysis_Unitarizability_Masked__DixmierAllDiscrete
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T07:32:13.074119+00:00
-- url     : https://prove2.me/theorems/733b7ede-7c88-441d-ac2d-fac1640e0f7a
-- title:
--   Masked rank-one convolution operators on $\ell^2(G;\mathbb{C}^K)$
-- statement:
--   Let $G$ be a group, $I$ and $K$ finite sets, and $\mathcal H=\ell^2(G;\mathbb{C}^K)$ the Hilbert space of square-summable $\mathbb{C}^K$-valued functions on $G$; inner products on $\mathbb{C}^K$ are conjugate-linear in the first argument. A masked operator is built from vectors $v_i\in\mathbb{C}^K$ and labels $s_i\in G$ for $i\in I$, and mask coefficients $c:G\times I\to\mathbb{C}$ with $|c(x,i)|\le1$ for all $x$ and $i$.
--
--   1. **Right shift.** For $s\in G$, the isometry $(\rho_s\xi)(x)=\xi(xs)$ of $\mathcal H$.
--   2. **Single-label term.** For $i\in I$, the bounded operator $M_i$ obtained by composing $\rho_{s_i}$ with the block-diagonal operator acting at each point $x$ by $c(x,i)\,v_iv_i^*$ (of norm at most $\|v_i\|^2$):
--   $$(M_i\xi)(x)=c(x,i)\,\langle v_i,\xi(xs_i)\rangle\,v_i .$$
--   3. **Masked operator.** $M_{v,s,c}=\sum_{i\in I}M_i$, that is
--   $$(M_{v,s,c}\,\xi)(x)=\sum_{i\in I}c(x,i)\,\langle v_i,\xi(xs_i)\rangle\,v_i .$$
--   4. **Row and column supports.** $\mathrm{Row}_c(x)=\{i\in I:\ c(x,i)\neq0\}$ and $\mathrm{Col}_{s,c}(y)=\{i\in I:\ c(ys_i^{-1},i)\neq0\}$, the labels of the active edges leaving row $x$ and arriving at column $y$.
--   5. **Edge energy.** For $\xi\in\mathcal H$ and $x\in G$,
--   $$\mathcal E_{v,s,c}(\xi)(x)=\sum_{i\in\mathrm{Row}_c(x)}\bigl|\langle v_i,\xi(xs_i)\rangle\bigr|^2 .$$
--
--   Masked operators are the building blocks of the construction: the constant mask $c\equiv1$ gives an operator commuting with left translations, Boolean masks give its sparse oriented parts, and the coboundary of an oriented part under left translation is again a masked operator. The module proves that if $b\ge0$ and the synthesis operators of the subfamilies $(v_i)_{i\in\mathrm{Row}_c(x)}$ and $(v_i)_{i\in\mathrm{Col}_{s,c}(y)}$ have norm at most $b$ for all $x$ and $y$, then $\|M_{v,s,c}\|\le b^2$; the edge energy is the intermediate quantity in that estimate. All labels stay separate, even when several $s_i$ coincide.
--
--   **Formalization Note** `Masked.Space G K` is `KernelObstruction.Space G K`. The definitions are `shift`, `term` (built from `HilbertSum.boundedSum` with bound `‖v i‖ * ‖v i‖`), `operator`, `rowSet`, `columnSet` and `edgeEnergy`, with evaluation lemmas `shift_apply`, `term_apply` and `operator_apply`; the bound $|c(x,i)|\le1$ is an explicit argument of `term` and `operator`, while `edgeEnergy` is defined for arbitrary coefficients.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/Unitarizability/Masked.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Unitarizability/Masked.lean by skeleton subtraction
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

namespace OAI

/-! Bounded masked operators. All labels remain separate, including
repeated values of the product list. -/
noncomputable section
namespace Dixmier
namespace Masked
open Finset
variable {G I K : Type*} [Group G] [Fintype I] [Fintype K]
local instance instDecidableEqComplex_oAI : DecidableEq ℂ := Classical.decEq ℂ
abbrev Space (G K : Type*) [Fintype K] : Type _ := KernelObstruction.Space G K
abbrev Fibre (K : Type*) [Fintype K] := EuclideanSpace ℂ K

def shift (s : G) : Space G K →L[ℂ] Space G K :=
  (KernelObstruction.reindexIsometry (K := K) (Equiv.mulRight s)).toContinuousLinearMap

@[simp] theorem shift_apply (s : G) (ξ : Space G K) (x : G) : shift s ξ x = ξ (x*s) := rfl

def term (v : I → Fibre K) (s : I → G) (c : G → I → ℂ)
    (hc : ∀ x i, ‖c x i‖ ≤ 1) (i : I) : Space G K →L[ℂ] Space G K :=
  (HilbertSum.boundedSum (κ := ‖v i‖ * ‖v i‖) (fun x => c x i • InnerProductSpace.rankOne ℂ (v i) (v i))
    (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (fun x => by
      rw [norm_smul, InnerProductSpace.norm_rankOne]
      exact (mul_le_mul_of_nonneg_right (hc x i) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).trans_eq (one_mul _))).comp
    (shift (s i))

def operator (v : I → Fibre K) (s : I → G) (c : G → I → ℂ)
    (hc : ∀ x i, ‖c x i‖ ≤ 1) : Space G K →L[ℂ] Space G K := ∑ i, term v s c hc i

omit [Fintype I] in
@[simp] theorem term_apply (v : I → Fibre K) (s : I → G) (c : G → I → ℂ)
    (hc : ∀ x i, ‖c x i‖ ≤ 1) (i : I) (ξ : Space G K) (x : G) :
    term v s c hc i ξ x = (c x i * inner ℂ (v i) (ξ (x*s i))) • v i := by
  change (c x i) • (InnerProductSpace.rankOne ℂ (v i) (v i) (ξ (x*s i))) = _
  rw [InnerProductSpace.rankOne_apply, smul_smul]

@[simp] theorem operator_apply (v : I → Fibre K) (s : I → G) (c : G → I → ℂ)
    (hc : ∀ x i, ‖c x i‖ ≤ 1) (ξ : Space G K) (x : G) :
    operator v s c hc ξ x = ∑ i, (c x i * inner ℂ (v i) (ξ (x*s i))) • v i := by
  simp only [operator, _root_.sum_apply, lp.coeFn_sum, Finset.sum_apply, term_apply]

def rowSet (c : G → I → ℂ) (x : G) : Finset I := univ.filter (fun i => c x i ≠ 0)
def columnSet (s : I → G) (c : G → I → ℂ) (y : G) : Finset I :=
  univ.filter (fun i => c (y*(s i)⁻¹) i ≠ 0)

def edgeEnergy (v : I → Fibre K) (s : I → G) (c : G → I → ℂ) (ξ : Space G K) (x : G) : ℝ :=
  ∑ i, if c x i ≠ 0 then ‖inner ℂ (v i) (ξ (x*s i))‖^2 else 0

end Masked
end Dixmier

end

end OAI


