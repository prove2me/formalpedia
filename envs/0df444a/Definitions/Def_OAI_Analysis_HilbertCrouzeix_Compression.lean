-- Prove2me | Definitions.Def_OAI_Analysis_HilbertCrouzeix_Compression
-- name    : OAI_Analysis_HilbertCrouzeix_Compression
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-14T18:03:18.700524+00:00
-- url     : https://prove2.me/theorems/a963eaa7-e524-4a04-93ad-0f525e48b780
-- title:
--   Iterate spaces of an operator and elementary-tensor formulas for amplified operators
-- statement:
--   Let $H$ be a complex inner product space (completeness is not assumed) and let $m\in\mathbb{N}$. Write $\mathbb{C}^m$ for the Euclidean space with its standard inner product, $M_m(\mathbb{C})$ for the $m\times m$ complex matrices acting on $\mathbb{C}^m$ by matrix-vector multiplication, and
--   $$
--   \mathcal{H}_m(H)=\overline{H\otimes\mathbb{C}^m}
--   $$
--   for the amplification of $H$, that is, the completion of the algebraic tensor product $H\otimes\mathbb{C}^m$ with respect to the inner product determined by $\langle x\otimes v,y\otimes w\rangle=\langle x,y\rangle\langle v,w\rangle$. For a bounded operator $T$ on $H$ and $B\in M_m(\mathbb{C})$, $T\otimes B$ denotes the continuous extension to $\mathcal{H}_m(H)$ of the tensor product map $x\otimes v\mapsto Tx\otimes Bv$. For a subspace $E\subseteq H$, $\iota_E:\mathcal{H}_m(E)\to\mathcal{H}_m(H)$ is the linear isometry obtained by completing the tensor product of the inclusion $E\hookrightarrow H$ with the identity of $\mathbb{C}^m$. The module introduces the following.
--
--   1. **Iterate spaces.** For a bounded operator $A$ on $H$, natural numbers $q,d$ and vectors $x_1,\dots,x_q\in H$, the iterate space is the complex linear span
--   $$
--   \mathcal{K}_d(A;x_1,\dots,x_q)=\operatorname{span}_{\mathbb{C}}\{A^kx_j:\ 0\le k\le d,\ 1\le j\le q\}\subseteq H .
--   $$
--   It is spanned by at most $(d+1)q$ vectors and is therefore finite-dimensional; this fact is registered once and for all, so that every iterate space is automatically treated as a finite-dimensional subspace.
--
--   2. **The inclusion on elementary tensors.** For every subspace $E\subseteq H$, every $x\in E$ and every $v\in\mathbb{C}^m$,
--   $$
--   \iota_E(x\otimes v)=x\otimes v,
--   $$
--   where on the right $x$ is regarded as a vector of $H$.
--
--   3. **Amplified operators on elementary tensors.** For every bounded operator $T$ on $H$, $B\in M_m(\mathbb{C})$, $x\in H$ and $v\in\mathbb{C}^m$,
--   $$
--   (T\otimes B)(x\otimes v)=Tx\otimes Bv .
--   $$
--
--   These objects serve to reduce matrix polynomials $\sum_{k=0}^dA^k\otimes B_k$ in an operator $A$ to finite dimensions. Given a finite tensor $\xi=\sum_jx_j\otimes v_j$, the iterate space $E=\mathcal{K}_d(A;x_1,\dots,x_q)$ is a finite-dimensional subspace containing every vector $A^kx_j$ that the polynomial produces, so the computation can be carried out with the compression $P_EA|_E$ of $A$ to $E$ in place of $A$, and transported back to $\mathcal{H}_m(H)$ by $\iota_E$.
--
--   **Formalization Note** The iterate space is `iterateSpace A d x` with `x : Fin q → H` and powers indexed by `Fin (d + 1)`; its finite-dimensionality is the instance `iterateSpace_finiteDimensional`. The two formulas are the simp lemmas `tensorInclusion_tmul` and `tensorOp_tmul` about `tensorInclusion` and `tensorOp` from the shared definitions; a matrix acts on $\mathbb{C}^m$ through `Matrix.toEuclideanCLM`, and elementary tensors are viewed in the completion through its canonical embedding. The plumbing lemma `completion_coe_sum` states that this embedding commutes with finite sums.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/HilbertCrouzeix/Compression.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/HilbertCrouzeix/Compression.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the HilbertCrouzeix mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_HilbertCrouzeix
import Definitions.Def_OAI_Analysis_HilbertCrouzeix_NumericalRange

namespace OAI

noncomputable section

open Complex Set
open scoped TensorProduct Matrix.Norms.L2Operator Classical ComplexConjugate

namespace HilbertCrouzeix

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

section Elementary
omit [CompleteSpace H]

def iterateSpace {q : ℕ} (A : H →L[ℂ] H) (d : ℕ) (x : Fin q → H) : Submodule ℂ H :=
  Submodule.span ℂ (Set.range fun t : Fin (d + 1) × Fin q => (A ^ t.1.val) (x t.2))

instance iterateSpace_finiteDimensional {q : ℕ} (A : H →L[ℂ] H) (d : ℕ)
    (x : Fin q → H) : FiniteDimensional ℂ (iterateSpace A d x) :=
  FiniteDimensional.span_of_finite ℂ (Set.finite_range _)

@[simp] theorem tensorInclusion_tmul (E : Submodule ℂ H) {m : ℕ}
    (x : E) (v : CoeffSpace m) :
    tensorInclusion E m (↑(x ⊗ₜ[ℂ] v)) = (↑((x : H) ⊗ₜ[ℂ] v) : Amplification H m) := by
  change (TensorProduct.mapIsometry E.subtypeₗᵢ (.id : CoeffSpace m →ₗᵢ[ℂ] CoeffSpace m)
    ).toContinuousLinearMap.completion (↑(x ⊗ₜ[ℂ] v)) = _
  rw [ContinuousLinearMap.completion_apply_coe]
  rfl

@[simp] theorem tensorOp_tmul {m : ℕ} (A : H →L[ℂ] H) (B : Coeff m)
    (x : H) (v : CoeffSpace m) :
    tensorOp A B (↑(x ⊗ₜ[ℂ] v)) =
      (↑(A x ⊗ₜ[ℂ] (Matrix.toEuclideanCLM (n := Fin m) (𝕜 := ℂ) B) v) : Amplification H m) := by
  simp only [tensorOp, ContinuousLinearMap.completion_apply_coe, TensorProduct.mapL_tmul]

@[simp] theorem completion_coe_sum {V : Type*} [NormedAddCommGroup V]
    {ι : Type*} (s : Finset ι) (f : ι → V) :
    (↑(∑ i ∈ s, f i) : UniformSpace.Completion V) = ∑ i ∈ s, (↑(f i) : UniformSpace.Completion V) :=
  map_sum (UniformSpace.Completion.toCompl : V →+ UniformSpace.Completion V) f s

end Elementary

end HilbertCrouzeix

end

end OAI


