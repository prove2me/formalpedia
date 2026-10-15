-- Prove2me | Definitions.Def_OAI_Analysis_Unitarizability_Regular__DixmierAllDiscrete
-- name    : OAI_Analysis_Unitarizability_Regular__DixmierAllDiscrete
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T07:15:07.311069+00:00
-- url     : https://prove2.me/theorems/28addebd-75f7-458c-a99d-643f055d641d
-- title:
--   Left and right regular representations on $\ell^2(G)$, words and word products
-- statement:
--   Let $G$ be a set and $\ell^2(G)$ the complex Hilbert space of square-summable functions on $G$.
--
--   1. **Reindexing.** For a bijection $e:G\to G$, the map $\xi\mapsto\xi\circ e$. The file proves $\|\xi\|^2=\sum_{x\in G}|\xi(x)|^2$ and $\|\xi\circ e\|=\|\xi\|$, and packages reindexing as a complex-linear isometry of $\ell^2(G)$.
--   2. **Right regular representation.** For a group $G$, the homomorphism $t\mapsto R_t$ into the bounded operators on $\ell^2(G)$,
--   $$(R_t\xi)(x)=\xi(xt).$$
--   3. **Left regular representation.** The homomorphism $g\mapsto\lambda_g$,
--   $$(\lambda_g\xi)(x)=\xi(g^{-1}x).$$
--   Both are built by reindexing, so every $R_t$ and every $\lambda_g$ is an isometry; left and right regular operators commute.
--   4. **Words.** For a set $I$ and $n\in\mathbb{N}$, the words of length $n$ are defined recursively: $\mathrm{Word}(I,0)$ is a one-point set and $\mathrm{Word}(I,n+1)=I\times\mathrm{Word}(I,n)$, so a word is an $n$-tuple $(i_1,\dots,i_n)$. If $I$ is finite, so is $\mathrm{Word}(I,n)$, with $|I|^n$ elements.
--   5. **Word products.** For $s:I\to G$,
--   $$\pi_s(i_1,\dots,i_n)=s_{i_1}s_{i_2}\cdots s_{i_n},$$
--   with the empty word mapped to $1$.
--
--   Right regular operators detect non-amenability: the development shows that a non-amenable discrete group has a finite set $S\ni1$ with $|S|\ge2$ and $\bigl\|\sum_{t\in S}R_t\bigr\|\le|S|\rho$ for some $0<\rho<1$. Since $t\mapsto R_t$ is a homomorphism, $\bigl(\sum_{i\in I}R_{s_i}\bigr)^n=\sum_{w}R_{\pi_s(w)}$ over all $|I|^n$ words, so words index the terms of iterated sums with full multiplicity, distinct words staying distinct even when their products agree. The module uses this to show that if $\bigl\|\sum_{i\in I}R_{s_i}\bigr\|\le|I|\rho$ with $\rho\ge0$, then for every length $\ell\ge1$ the words of length $\ell$, labelled by their products, admit a Boolean mask with at most $\lceil|I|^\ell\rho^\ell\rceil$ row ones in every row and at most that many column zeros in every column.
--
--   **Formalization Note** `reindexL2`, `reindexIsometry`, `rightRegular` and `leftRegular` (the last two bundled monoid homomorphisms into `ScalarL2 G →L[ℂ] ScalarL2 G`) come with evaluation lemmas, together with `l2_norm_sq` and `reindexL2_norm`. `Word I n` is the nested product ending in `PUnit`, with `Fintype` instance `wordFintype`, and `wordProduct s (n+1) w` is `s w.1 * wordProduct s n w.2`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/Unitarizability/Regular.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Unitarizability/Regular.lean by skeleton subtraction
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

namespace OAI

/-! Regular convolution operators, product lists with multiplicity,
and sparse splitting from a contracting average. -/
noncomputable section
namespace Dixmier
universe u
open Finset
attribute [local instance] Classical.propDecidable

variable {G : Type*}

def reindexL2 (e : G ≃ G) (ξ : ScalarL2 G) : ScalarL2 G :=
  ⟨fun x => ξ (e x), memℓp_gen (((lp.memℓp ξ).summable (by norm_num)).comp_injective e.injective)⟩

@[simp] theorem reindexL2_apply (e : G ≃ G) (ξ : ScalarL2 G) (x : G) :
    reindexL2 e ξ x = ξ (e x) := rfl

theorem l2_norm_sq (ξ : ScalarL2 G) : ‖ξ‖ ^ 2 = ∑' x, ‖ξ x‖ ^ 2 := by
  simpa using lp.norm_rpow_eq_tsum (p := 2) (by norm_num) ξ

theorem reindexL2_norm (e : G ≃ G) (ξ : ScalarL2 G) : ‖reindexL2 e ξ‖ = ‖ξ‖ := by
  have hs : ‖reindexL2 e ξ‖ ^ 2 = ‖ξ‖ ^ 2 := by
    rw [l2_norm_sq, l2_norm_sq]
    exact e.tsum_eq (fun x => ‖ξ x‖ ^ 2)
  nlinarith [norm_nonneg (reindexL2 e ξ), norm_nonneg ξ]

def reindexIsometry (e : G ≃ G) : ScalarL2 G →ₗᵢ[ℂ] ScalarL2 G where
  toFun := reindexL2 e
  map_add' ξ η := by ext x; rfl
  map_smul' z ξ := by ext x; rfl
  norm_map' := reindexL2_norm e

variable [Group G]

/-- The right regular representation R_t ξ(x)=ξ(xt). -/
def rightRegular : G →* (ScalarL2 G →L[ℂ] ScalarL2 G) where
  toFun t := (reindexIsometry (Equiv.mulRight t)).toContinuousLinearMap
  map_one' := by ext ξ x; simp [reindexIsometry, reindexL2]
  map_mul' s t := by ext ξ x; simp [reindexIsometry, reindexL2, mul_assoc]

@[simp] theorem rightRegular_apply (t : G) (ξ : ScalarL2 G) (x : G) :
    rightRegular t ξ x = ξ (x * t) := rfl

/-- Left regular operators U_g commute with the right regular operators. -/
def leftRegular : G →* (ScalarL2 G →L[ℂ] ScalarL2 G) where
  toFun g := (reindexIsometry (Equiv.mulLeft g⁻¹)).toContinuousLinearMap
  map_one' := by ext ξ x; simp [reindexIsometry, reindexL2]
  map_mul' g h := by ext ξ x; simp [reindexIsometry, reindexL2]

@[simp] theorem leftRegular_apply (g : G) (ξ : ScalarL2 G) (x : G) :
    leftRegular g ξ x = ξ (g⁻¹ * x) := rfl

def Word (I : Type u) : ℕ → Type u
  | 0 => PUnit
  | n + 1 => I × Word I n

instance wordFintype {I : Type*} [Fintype I] : (n : ℕ) → Fintype (Word I n)
  | 0 => inferInstanceAs (Fintype PUnit)
  | n + 1 => by
    letI : Fintype (Word I n) := wordFintype n
    exact inferInstanceAs (Fintype (I × Word I n))

def wordProduct {I : Type*} (s : I → G) : (n : ℕ) → Word I n → G
  | 0, _ => 1
  | n + 1, w => s w.1 * wordProduct s n w.2

end Dixmier

end

end OAI


