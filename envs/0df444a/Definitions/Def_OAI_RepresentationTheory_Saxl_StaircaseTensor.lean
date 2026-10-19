-- Prove2me | Definitions.Def_OAI_RepresentationTheory_Saxl_StaircaseTensor
-- name    : OAI_RepresentationTheory_Saxl_StaircaseTensor
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T22:49:14.112735+00:00
-- url     : https://prove2.me/theorems/574b93bf-c5f8-477a-9e2f-6a345170651a
-- title:
--   Position-wise tensor regrouping and the staircase tensor generator
-- statement:
--   For $n\in\mathbb{N}$ write $[n]=\{0,1,\dots,n-1\}$ and let $S_n$ be the symmetric group on $[n]$. A *word* of length $n$ over the alphabet $[d]$ is a map $a:[n]\to[d]$, and $W_{n,d}=\mathbb{C}^{[d]^n}$ is the space of complex functions on words, with standard basis vectors $e_a$ (the indicator function of the word $a$), so that $W_{n,d}\cong(\mathbb{C}^d)^{\otimes n}$. The group $S_n$ acts on $W_{n,d}$ by permuting positions, $(\rho_{n,d}(g)x)(a)=x(a\circ g)$; equivalently $\rho_{n,d}(g)e_a=e_{a\circ g^{-1}}$. For alphabet sizes $d,e$, the product alphabet $[d]\times[e]$ is identified with $[de]$ by $(a,b)\mapsto ae+b$; for a word $w\in[de]^n$ let $w^{L}\in[d]^n$ and $w^{R}\in[e]^n$ be its left and right components, $w_i=w^{L}_i\,e+w^{R}_i$.
--
--   A Young diagram $\mu$ is a finite set of cells $(i,j)\in\mathbb{N}^2$ (row $i$, column $j$, both counted from $0$) that is closed under decreasing either coordinate; $\ell(\mu)$ denotes its number of rows. A tableau of shape $\mu$ on $n=|\mu|$ positions is a bijection $t:[n]\to\mu$. Its row word $r_t:[n]\to[\ell(\mu)]$ sends $i$ to the row index of $t(i)$, its column group $C_t\le S_n$ consists of the permutations $g$ such that $t(g(i))$ lies in the same column as $t(i)$ for every $i$, and its polytabloid is
--   $$
--   e_t=\sum_{g\in C_t}\operatorname{sgn}(g)\,\rho_{n,\ell(\mu)}(g)\,e_{r_t}\in W_{n,\ell(\mu)} .
--   $$
--   The Specht module $S^t\subseteq W_{n,\ell(\mu)}$ is the span of the $S_n$-orbit $\{\rho_{n,\ell(\mu)}(g)e_t:g\in S_n\}$.
--
--   For $m\in\mathbb{N}$ the staircase diagram is $\delta_m=\{(i,j)\in\mathbb{N}^2:i+j<m\}$, with rows of lengths $m,m-1,\dots,1$ and $N_m=|\delta_m|=m(m+1)/2$ cells. The canonical tableau $T_m:[N_m]\to\delta_m$ is the fixed enumeration of the cells of $\delta_m$ used in the target statement. The file introduces:
--
--   1. **Splitting and merging words.** The maps $w\mapsto(w^{L},w^{R})$ from $[de]^n$ to $[d]^n\times[e]^n$ and its inverse $(a,b)\mapsto w$ with $w_i=a_ie+b_i$.
--   2. **Position-wise tensor isomorphism.** The linear isomorphism $\Theta=\Theta_{n,d,e}:W_{n,d}\otimes W_{n,e}\to W_{n,de}$ determined by
--   $$
--   \Theta(x\otimes y)(w)=x(w^{L})\,y(w^{R}) .
--   $$
--   It is $S_n$-equivariant for the diagonal action, $\Theta\big((\rho_{n,d}(g)\otimes\rho_{n,e}(g))z\big)=\rho_{n,de}(g)\,\Theta(z)$, and is packaged as an intertwiner.
--   3. **Staircase tableaux.** The transposition $\tau(i,j)=(j,i)$ is a permutation of the cells of the self-conjugate diagram $\delta_m$; the transposed tableau is $T'_m=\tau\circ T_m$, so that $r_{T'_m}(i)$ is the column index of $T_m(i)$.
--   4. **Staircase word and its cyclic module.** With $\ell=\ell(\delta_m)$ (which equals $m$),
--   $$
--   \omega_m=\Theta\big(e_{T'_m}\otimes e_{T_m}\big)\in W_{N_m,\ell^2},\qquad Z_m=\operatorname{span}_{\mathbb{C}}\{\rho_{N_m,\ell^2}(g)\,\omega_m:\ g\in S_{N_m}\}.
--   $$
--   5. **Embedding of the tensor square.** For a tableau $t$, the inclusion $\iota_t:S^t\hookrightarrow W_{n,\ell(\mu)}$ as an intertwiner, and the intertwiner $\Psi_m=\Theta\circ(\iota_{T_m}\otimes\iota_{T_m}):S^{T_m}\otimes S^{T_m}\to W_{N_m,\ell^2}$, where the source carries the diagonal action. The map $\Psi_m$ is injective and $Z_m\subseteq\Psi_m\big(S^{T_m}\otimes S^{T_m}\big)$ (the polytabloid $e_{T'_m}$ lies in $S^{T_m}$, as the two tableaux have the same shape).
--
--   Because $\Psi_m$ is injective and equivariant, $Z_m$ is isomorphic to a subrepresentation of the tensor square $S^{T_m}\otimes S^{T_m}$ of the staircase Specht module. Hence a nonzero intertwiner from a Specht module into $Z_m$ yields a nonzero intertwiner into the tensor square, i.e. a positive Kronecker multiplicity. The surrounding development uses this to reduce the target statement to showing that every Specht module of size $N_m$ maps nontrivially into the explicit cyclic module $Z_m$.
--
--   **Formalization Note** The word splitting uses Mathlib's `finProdFinEquiv`; $\Theta$ is `wordTensor` (built from `TensorProduct.piScalarRight` and the currying equivalence `wordUncurry`) and its intertwiner form is `wordTensorIntertwiner`. The other objects are `staircaseSwap`, `stairTableau`, `stairRowTableau`, `staircaseWord`, `staircaseCyclic`, `spechtInclusion` and `staircaseTensorMap` (made irreducible at the end of the file), with lemmas `staircaseTensorMap_injective` and `staircaseCyclic_le_tensorRange`; $\ell(\delta_m)$ appears as `(staircase m).colLen 0`. The file also contains a private copy of the induction principle for tensor products, needed for compatibility with Lean 4.33.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/RepresentationTheory/Saxl/StaircaseTensor.lean

-- Generated from openai/math@1581d4c lean/OAI/RepresentationTheory/Saxl/StaircaseTensor.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the Saxl mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_Saxl
import Definitions.Def_OAI_RepresentationTheory_Saxl_Basic
import Definitions.Def_OAI_RepresentationTheory_Saxl_Polytabloid
import Definitions.Def_OAI_RepresentationTheory_Saxl_SpechtSubmodule
import Definitions.Def_OAI_RepresentationTheory_Saxl_SpechtDuality
import Definitions.Def_OAI_RepresentationTheory_Saxl_TableauTransport

-- Backport the two-case eliminator from Mathlib/LinearAlgebra/TensorProduct/Defs.lean
-- at d13f23b723b8a846827a245b89c10fc7d3f11612, using the 4.33.1 eliminator.
section Lean433TensorProductCompatibility
open scoped TensorProduct
variable {R M N : Type*} [CommSemiring R]
  [AddCommMonoid M] [AddCommMonoid N] [Module R M] [Module R N]
namespace TensorProduct
@[elab_as_elim, induction_eliminator]
private theorem inductionOn {motive : M ⊗[R] N → Prop} (z : M ⊗[R] N)
    (tmul : ∀ x y, motive (x ⊗ₜ[R] y))
    (add : ∀ x y, motive x → motive y → motive (x + y)) : motive z :=
  TensorProduct.induction_on z
    (by simpa only [TensorProduct.zero_tmul] using tmul (0 : M) (0 : N)) tmul add
end TensorProduct
end Lean433TensorProductCompatibility

namespace OAI

noncomputable section

open scoped TensorProduct

namespace Saxl
def splitLeft {n d e : ℕ} (w : Fin n → Fin (d*e)) : Fin n → Fin d :=
  fun i => (finProdFinEquiv.symm (w i)).1

def splitRight {n d e : ℕ} (w : Fin n → Fin (d*e)) : Fin n → Fin e :=
  fun i => (finProdFinEquiv.symm (w i)).2

def mergeWords {n d e : ℕ} (a : Fin n → Fin d) (b : Fin n → Fin e) : Fin n → Fin (d*e) :=
  fun i => finProdFinEquiv (a i, b i)

@[simp] lemma splitLeft_merge {n d e : ℕ} (a : Fin n → Fin d) (b : Fin n → Fin e) :
    splitLeft (mergeWords a b) = a := by ext i; simp [splitLeft, mergeWords]
@[simp] lemma splitRight_merge {n d e : ℕ} (a : Fin n → Fin d) (b : Fin n → Fin e) :
    splitRight (mergeWords a b) = b := by ext i; simp [splitRight, mergeWords]
@[simp] lemma merge_split {n d e : ℕ} (w : Fin n → Fin (d*e)) :
    mergeWords (splitLeft w) (splitRight w) = w := by
  funext i
  exact finProdFinEquiv.apply_symm_apply (w i)

def wordUncurry (n d e : ℕ) :
    ((Fin n → Fin e) → WordSpace n d) ≃ₗ[ℂ] WordSpace n (d*e) where
  toFun f w := f (splitRight w) (splitLeft w)
  invFun z b a := z (mergeWords a b)
  left_inv f := by ext b a; simp
  right_inv z := by ext w; simp
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/- Tensor regrouping by positions. -/
def wordTensor (n d e : ℕ) :
    WordSpace n d ⊗[ℂ] WordSpace n e ≃ₗ[ℂ] WordSpace n (d*e) :=
  TensorProduct.piScalarRight ℂ ℂ (WordSpace n d) (Fin n → Fin e) ≪≫ₗ wordUncurry n d e

@[simp] lemma wordTensor_tmul {n d e : ℕ} (x : WordSpace n d) (y : WordSpace n e)
    (w : Fin n → Fin (d*e)) :
    wordTensor n d e (x ⊗ₜ[ℂ] y) w = x (splitLeft w) * y (splitRight w) := by
  change y (splitRight w) • x (splitLeft w) = _
  exact mul_comm _ _

lemma wordTensor_equivariant {n d e : ℕ} (g : Equiv.Perm (Fin n))
    (z : WordSpace n d ⊗[ℂ] WordSpace n e) :
    wordTensor n d e (((wordRep n d).tprod (wordRep n e)) g z) =
      wordRep n (d*e) g (wordTensor n d e z) := by
  induction z using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul x y =>
    ext w
    change wordTensor n d e (wordRep n d g x ⊗ₜ[ℂ] wordRep n e g y) w = _
    change wordTensor n d e (wordRep n d g x ⊗ₜ[ℂ] wordRep n e g y) w =
      wordTensor n d e (x ⊗ₜ[ℂ] y) (w ∘ g)
    simp only [wordTensor_tmul]
    rfl

def wordTensorIntertwiner (n d e : ℕ) :
    Representation.IntertwiningMap ((wordRep n d).tprod (wordRep n e)) (wordRep n (d*e)) where
  toLinearMap := (wordTensor n d e).toLinearMap
  isIntertwining' g := by
    apply LinearMap.ext
    intro z
    exact wordTensor_equivariant g z

end Saxl

namespace Saxl

/- Transposition is an honest permutation of the self-conjugate staircase. -/
def staircaseSwap (m : ℕ) : (staircase m).cells ≃ (staircase m).cells where
  toFun x := ⟨(x.val.2, x.val.1), by
    have h : x.val.1 + x.val.2 < m := mem_staircase.mp x.property
    exact mem_staircase.mpr (by omega)⟩
  invFun x := ⟨(x.val.2, x.val.1), by
    have h : x.val.1 + x.val.2 < m := mem_staircase.mp x.property
    exact mem_staircase.mpr (by omega)⟩
  left_inv _ := rfl
  right_inv _ := rfl

abbrev stairTableau (m : ℕ) : Tableau (staircase m).card (staircase m) :=
  canonicalTableau (staircase m) rfl

def stairRowTableau (m : ℕ) : Tableau (staircase m).card (staircase m) :=
  (stairTableau m).trans (staircaseSwap m)

def staircaseWord (m : ℕ) : WordSpace (staircase m).card ((staircase m).colLen 0 * (staircase m).colLen 0) :=
  wordTensor _ _ _ (polytabloid (stairRowTableau m) ⊗ₜ[ℂ] polytabloid (stairTableau m))

def staircaseCyclic (m : ℕ) : Subrepresentation
    (wordRep (staircase m).card ((staircase m).colLen 0 * (staircase m).colLen 0)) :=
  cyclic (wordRep _ _) (staircaseWord m)

def spechtInclusion {n : ℕ} {μ : YoungDiagram} (t : Tableau n μ) :
    Representation.IntertwiningMap (spechtRep t) (wordRep n (μ.colLen 0)) where
  toLinearMap := (spechtSub t).toSubmodule.subtype
  isIntertwining' _ := rfl

def staircaseTensorMap (m : ℕ) :
    Representation.IntertwiningMap ((spechtRep (stairTableau m)).tprod (spechtRep (stairTableau m)))
    (wordRep (staircase m).card ((staircase m).colLen 0 * (staircase m).colLen 0)) :=
  (wordTensorIntertwiner _ _ _).comp
    ((spechtInclusion (stairTableau m)).tensor (spechtInclusion (stairTableau m)))

lemma staircaseTensorMap_injective (m : ℕ) : Function.Injective (staircaseTensorMap m) := by
  apply (wordTensor _ _ _).injective.comp
  exact TensorProduct.map_injective_of_flat_flat _ _
    (spechtSub (stairTableau m)).toSubmodule.subtype_injective
    (spechtSub (stairTableau m)).toSubmodule.subtype_injective

lemma staircaseCyclic_le_tensorRange (m : ℕ) :
    staircaseCyclic m ≤ (staircaseTensorMap m).range := by
  apply (cyclic_le _ _ _).mpr
  refine ⟨(⟨polytabloid (stairRowTableau m), polytabloid_mem_all _ _⟩ : Specht (stairTableau m)) ⊗ₜ[ℂ]
    (⟨polytabloid (stairTableau m), mem_cyclic _ _⟩ : Specht (stairTableau m)), ?_⟩
  rfl

attribute [irreducible] staircaseTensorMap

end Saxl

end

end OAI


