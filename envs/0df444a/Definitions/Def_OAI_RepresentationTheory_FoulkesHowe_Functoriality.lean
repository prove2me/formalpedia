-- Prove2me | Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_Functoriality
-- name    : OAI_RepresentationTheory_FoulkesHowe_Functoriality
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T15:14:13.83245+00:00
-- url     : https://prove2.me/theorems/eea27719-055d-4c44-89f5-80083e426c12
-- title:
--   Functoriality of the symmetric algebra and of the symmetric powers $\mathrm{Sym}^n$
-- statement:
--   Let $V,W,U$ be complex vector spaces of arbitrary dimension. Write $S(V)$ for the symmetric algebra of $V$ over $\mathbb{C}$ with canonical map $\iota_V:V\to S(V)$, and for $n\in\mathbb{N}$ let $\mathrm{Sym}^n V\subseteq S(V)$ be the linear span of the products $[x_0,\dots,x_{n-1}]=\iota_V(x_0)\cdots\iota_V(x_{n-1})$ with $x_i\in V$ (similarly for $W$ and $U$).
--
--   1. **Induced algebra homomorphism.** For a linear map $f:V\to W$, $S(f):S(V)\to S(W)$ is the $\mathbb{C}$-algebra homomorphism determined by $S(f)(\iota_V(x))=\iota_W(f(x))$. It sends products of generators to products of generators,
--   $$S(f)\bigl([x_0,\dots,x_{n-1}]\bigr)=[f(x_0),\dots,f(x_{n-1})]\qquad(n\in\mathbb{N},\ x_i\in V),$$
--   and $S(\mathrm{id}_V)=\mathrm{id}_{S(V)}$, $S(g\circ f)=S(g)\circ S(f)$ for every linear $g:W\to U$.
--   2. **Induced map on symmetric powers.** By the displayed formula, $S(f)$ maps $\mathrm{Sym}^n V$ into $\mathrm{Sym}^n W$; the restricted map is the linear map $\mathrm{Sym}^n f:\mathrm{Sym}^n V\to\mathrm{Sym}^n W$, so that $\mathrm{Sym}^n f([x_0,\dots,x_{n-1}])=[f(x_0),\dots,f(x_{n-1})]$. It satisfies $\mathrm{Sym}^n(\mathrm{id}_V)=\mathrm{id}$ and $\mathrm{Sym}^n(g\circ f)=\mathrm{Sym}^n g\circ\mathrm{Sym}^n f$.
--   3. **Induced isomorphisms.** A linear isomorphism $e:V\to W$ induces a linear isomorphism $\mathrm{Sym}^n e:\mathrm{Sym}^n V\to\mathrm{Sym}^n W$ whose inverse is $\mathrm{Sym}^n(e^{-1})$. This assignment sends the identity of $V$ to the identity, a composite $e'\circ e$ (with $e':W\to U$) to $\mathrm{Sym}^n e'\circ\mathrm{Sym}^n e$, and $e^{-1}$ to $(\mathrm{Sym}^n e)^{-1}$.
--
--   These maps make the symmetric algebra and each symmetric power functors on complex vector spaces. Iterating them gives the maps induced on plethysms $\mathrm{Sym}^p(\mathrm{Sym}^q V)$, in particular the action of the general linear group $\mathrm{GL}(V)$ on them.
--
--   **Formalization Note** `symAlgMap f` is `SymmetricAlgebra.lift` applied to the composite of `f` with the generator map of `W`; `symPowMap n f` is its restriction to `SymPow n V` with codomain `SymPow n W`, and `symPowEquiv n e` bundles `symPowMap n e` with `symPowMap n e.symm`. Composition of equivalences appears as `e.trans f` (first `e`, then `f`).
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/RepresentationTheory/FoulkesHowe/Functoriality.lean

-- Generated from openai/math@1581d4c lean/OAI/RepresentationTheory/FoulkesHowe/Functoriality.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the FoulkesHowe mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_FoulkesHowe
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_Model
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_DegreeOne

namespace OAI

noncomputable section
open scoped BigOperators
universe u v w
namespace Problem346

variable {V : Type u} {W : Type v} {U : Type w}
  [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
  [AddCommGroup U] [Module ℂ U]

/-- The algebra map induced by a complex-linear map. -/
def symAlgMap (f : V →ₗ[ℂ] W) : SymmetricAlgebra ℂ V →ₐ[ℂ] SymmetricAlgebra ℂ W :=
  SymmetricAlgebra.lift ((SymmetricAlgebra.ι ℂ W).comp f)

@[simp] theorem symAlgMap_ι (f : V →ₗ[ℂ] W) (x : V) :
    symAlgMap f (SymmetricAlgebra.ι ℂ V x) = SymmetricAlgebra.ι ℂ W (f x) := by
  simp [symAlgMap]

@[simp] theorem symAlgMap_symMonomialRaw (n : ℕ) (f : V →ₗ[ℂ] W) (x : Fin n → V) :
    symAlgMap f (symMonomialRaw n V x) = symMonomialRaw n W (fun i => f (x i)) := by
  simp [symMonomialRaw]

/-- Symmetric powers act covariantly on linear maps. -/
def symPowMap (n : ℕ) (f : V →ₗ[ℂ] W) : SymPow n V →ₗ[ℂ] SymPow n W :=
  ((symAlgMap f).toLinearMap.comp (symPowSubmodule n V).subtype).codRestrict
    (symPowSubmodule n W) (by
      have hle : symPowSubmodule n V ≤
          (symPowSubmodule n W).comap (symAlgMap f).toLinearMap := by
        apply Submodule.span_le.mpr
        rintro x ⟨v, rfl⟩
        change symAlgMap f (symMonomialRaw n V v) ∈ symPowSubmodule n W
        rw [symAlgMap_symMonomialRaw]
        exact Submodule.subset_span (Set.mem_range_self _)
      intro x
      exact hle x.property)

@[simp] theorem symPowMap_symMonomial (n : ℕ) (f : V →ₗ[ℂ] W) (x : Fin n → V) :
    symPowMap n f (symMonomial n V x) = symMonomial n W (fun i => f (x i)) := by
  apply Subtype.ext
  exact symAlgMap_symMonomialRaw n f x

@[simp] theorem symAlgMap_id :
    symAlgMap (LinearMap.id : V →ₗ[ℂ] V) = AlgHom.id ℂ (SymmetricAlgebra ℂ V) := by
  ext x
  simp

@[simp] theorem symAlgMap_comp (g : W →ₗ[ℂ] U) (f : V →ₗ[ℂ] W) :
    symAlgMap (g.comp f) = (symAlgMap g).comp (symAlgMap f) := by
  ext x
  simp

@[simp] theorem symPowMap_coe (n : ℕ) (f : V →ₗ[ℂ] W) (x : SymPow n V) :
    (symPowMap n f x : SymmetricAlgebra ℂ W) = symAlgMap f x := rfl

@[simp] theorem symPowMap_id (n : ℕ) :
    symPowMap n (LinearMap.id : V →ₗ[ℂ] V) = LinearMap.id := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  simp

@[simp] theorem symPowMap_comp (n : ℕ) (g : W →ₗ[ℂ] U) (f : V →ₗ[ℂ] W) :
    symPowMap n (g.comp f) = (symPowMap n g).comp (symPowMap n f) := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  simp

/-- A linear equivalence induces an equivalence on each symmetric power. -/
def symPowEquiv (n : ℕ) (e : V ≃ₗ[ℂ] W) : SymPow n V ≃ₗ[ℂ] SymPow n W where
  toLinearMap := symPowMap n e.toLinearMap
  invFun := symPowMap n e.symm.toLinearMap
  left_inv x := by
    change ((symPowMap n e.symm.toLinearMap).comp (symPowMap n e.toLinearMap)) x = x
    rw [← symPowMap_comp]
    simp
  right_inv x := by
    change ((symPowMap n e.toLinearMap).comp (symPowMap n e.symm.toLinearMap)) x = x
    rw [← symPowMap_comp]
    simp

@[simp] theorem symPowEquiv_symMonomial (n : ℕ) (e : V ≃ₗ[ℂ] W) (x : Fin n → V) :
    symPowEquiv n e (symMonomial n V x) = symMonomial n W (fun i => e (x i)) :=
  symPowMap_symMonomial n e.toLinearMap x

@[simp] theorem symPowEquiv_toLinearMap (n : ℕ) (e : V ≃ₗ[ℂ] W) :
    (symPowEquiv n e).toLinearMap = symPowMap n e.toLinearMap := rfl

@[simp] theorem symPowEquiv_refl (n : ℕ) :
    symPowEquiv n (LinearEquiv.refl ℂ V) = LinearEquiv.refl ℂ (SymPow n V) := by
  apply LinearEquiv.toLinearMap_injective
  exact symPowMap_id n

@[simp] theorem symPowEquiv_trans (n : ℕ) (e : V ≃ₗ[ℂ] W) (f : W ≃ₗ[ℂ] U) :
    symPowEquiv n (e.trans f) = (symPowEquiv n e).trans (symPowEquiv n f) := by
  apply LinearEquiv.toLinearMap_injective
  exact symPowMap_comp n f.toLinearMap e.toLinearMap

@[simp] theorem symPowEquiv_symm (n : ℕ) (e : V ≃ₗ[ℂ] W) :
    symPowEquiv n e.symm = (symPowEquiv n e).symm := by
  rfl

end Problem346

end

end OAI


