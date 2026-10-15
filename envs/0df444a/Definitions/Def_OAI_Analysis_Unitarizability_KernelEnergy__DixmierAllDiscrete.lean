-- Prove2me | Definitions.Def_OAI_Analysis_Unitarizability_KernelEnergy__DixmierAllDiscrete
-- name    : OAI_Analysis_Unitarizability_KernelEnergy__DixmierAllDiscrete
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T07:01:38.716564+00:00
-- url     : https://prove2.me/theorems/a91c7fe1-07e9-4333-b25a-d96fdb60404d
-- title:
--   Rank-one coefficient matrices $vv^*$ and collision kernels of a labelled vector family
-- statement:
--   Let $K$ be a finite set and $\mathbb{C}^K$ the complex Euclidean space with inner product $\langle u,w\rangle=\sum_{a\in K}\overline{u_a}\,w_a$. A $K\times K$ matrix is represented by its array of entries, viewed as a vector of the Euclidean space $\mathbb{C}^{K\times K}$; the norm of this vector is the unnormalized Hilbert–Schmidt (Frobenius) norm $\|M\|_{\mathrm{HS}}=\bigl(\sum_{a,b\in K}|M_{ab}|^2\bigr)^{1/2}$.
--
--   1. **Rank-one coefficients.** For $v\in\mathbb{C}^K$, the entry array of the rank-one matrix $vv^*$:
--   $$(vv^*)_{ab}=v_a\,\overline{v_b}\qquad(a,b\in K).$$
--   The entry formula is recorded as a simp lemma.
--   2. **Collision kernel.** Let $I$ be a finite set of labels, $v=(v_i)_{i\in I}$ a family in $\mathbb{C}^K$ and $s:I\to G$ an arbitrary map into a set $G$. For $g\in G$,
--   $$W_{v,s}(g)=\sum_{i\in I:\ s_i=g}v_iv_i^*\ \in\mathbb{C}^{K\times K},$$
--   the sum of the rank-one matrices of all labels whose value is $g$. It is $0$ when no label takes the value $g$, and colliding labels ($s_i=s_j$ with $i\neq j$) contribute separate terms.
--
--   When $G$ is a group, $W_{v,s}(g)$ is exactly the $(1,g)$ block of the translation-invariant operator $(A\xi)(x)=\sum_{i\in I}\langle v_i,\xi(xs_i)\rangle\,v_i$ on $\ell^2(G;\mathbb{C}^K)$, i.e. its convolution kernel. Because $\langle v_iv_i^*,v_jv_j^*\rangle_{\mathrm{HS}}=|\langle v_i,v_j\rangle|^2\ge0$, rank-one terms never cancel: for unit vectors the module shows $|J|\le\|\sum_{i\in J}v_iv_i^*\|_{\mathrm{HS}}^2$ for every finite $J\subseteq I$, and hence $\sum_{g\in G}\|W_{v,s}(g)\|_{\mathrm{HS}}^2\ge|I|$. This lower bound on the kernel energy is what feeds the energy-growth hypothesis $\mathcal E(A_j)/k_j\to\infty$ of the direct-sum obstruction in the construction for non-amenable groups.
--
--   **Formalization Note** Entry arrays live in `EuclideanSpace ℂ (K × K)` and are built with `WithLp.toLp 2`; `rankOneCoefficients_apply` is the entry formula, and `kernelCoefficients v s g` sums over `Finset.univ` filtered by `s i = g`. No structure on $G$ is needed for these definitions.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/Unitarizability/KernelEnergy.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Unitarizability/KernelEnergy.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the DixmierAllDiscrete mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_DixmierAllDiscrete

namespace OAI

/-! Positive rank-one kernel energy. Matrices are represented by their entries
with the unnormalized Hilbert–Schmidt (Euclidean coefficient) norm. -/
noncomputable section
namespace Dixmier
attribute [local instance] Classical.propDecidable
open Finset
open scoped ComplexConjugate
variable {K I G : Type*} [Fintype K] [Fintype I]

def rankOneCoefficients (v : EuclideanSpace ℂ K) : EuclideanSpace ℂ (K × K) :=
  WithLp.toLp 2 (fun p => v p.1 * conj (v p.2))

omit [Fintype K] in
@[simp] theorem rankOneCoefficients_apply (v : EuclideanSpace ℂ K) (a b : K) :
    rankOneCoefficients v (a, b) = v a * conj (v b) := rfl

/-- Collision blocks are sums of the rank-one matrices with that label value. -/
def kernelCoefficients (v : I → EuclideanSpace ℂ K) (s : I → G) (g : G) :
    EuclideanSpace ℂ (K × K) :=
  ∑ i ∈ (Finset.univ.filter fun i => s i = g), rankOneCoefficients (v i)

end Dixmier

end

end OAI


