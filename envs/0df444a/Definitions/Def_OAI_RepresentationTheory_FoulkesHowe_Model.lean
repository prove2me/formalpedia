-- Prove2me | Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_Model
-- name    : OAI_RepresentationTheory_FoulkesHowe_Model
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T15:12:02.9791+00:00
-- url     : https://prove2.me/theorems/b56f6eac-ff93-417c-bfe1-039a124a3252
-- title:
--   Multilinear forms in $a$ arguments from $\mathrm{Sym}^b V$ and their symmetry
-- statement:
--   Let $V$ be a complex vector space and let $S(V)$ be its symmetric algebra over $\mathbb{C}$. For $n\in\mathbb{N}$, $\mathrm{Sym}^n V\subseteq S(V)$ denotes the linear span of all products $v_0v_1\cdots v_{n-1}$ of $n$ vectors $v_i\in V$ (the homogeneous component of degree $n$). Fix $a,b\in\mathbb{N}$. The file introduces two notions.
--
--   1. **Multilinear forms on $\mathrm{Sym}^b V$ in $a$ arguments.** This is the complex vector space
--   $$\mathcal{M}_{a,b}(V)=\bigl\{\,T:(\mathrm{Sym}^b V)^{a}\to\mathbb{C}\ :\ T\text{ is }\mathbb{C}\text{-linear in each of its }a\text{ arguments}\,\bigr\},$$
--   whose elements send an $a$-tuple $(x_0,\dots,x_{a-1})$ of elements of $\mathrm{Sym}^b V$ to a complex number. No symmetry condition is imposed on the elements of $\mathcal{M}_{a,b}(V)$.
--   2. **Symmetric forms.** A form $T\in\mathcal{M}_{a,b}(V)$ is called *symmetric* if
--   $$T(x_{\sigma(0)},\dots,x_{\sigma(a-1)})=T(x_0,\dots,x_{a-1})\qquad\text{for all }\sigma\in S_a\text{ and all }x_0,\dots,x_{a-1}\in\mathrm{Sym}^b V,$$
--   where $S_a$ is the symmetric group on $\{0,1,\dots,a-1\}$.
--
--   Symmetric $a$-linear forms on $\mathrm{Sym}^b V$ are the natural dual objects for the plethysm $\mathrm{Sym}^a(\mathrm{Sym}^b V)$: composing a linear functional on $\mathrm{Sym}^a(\mathrm{Sym}^b V)$ with the product map $(x_0,\dots,x_{a-1})\mapsto x_0x_1\cdots x_{a-1}$ produces a symmetric form in $\mathcal{M}_{a,b}(V)$, and the functional is determined by this form. This is how surjectivity of linear maps into $\mathrm{Sym}^a(\mathrm{Sym}^b V)$, such as the Foulkes–Howe map defined on $\mathrm{Sym}^b(\mathrm{Sym}^a V)$, is reduced to a vanishing statement for symmetric forms.
--
--   **Formalization Note** `SymmetricMultilinearForm a b V` abbreviates the type of `MultilinearMap`s from the `Fin a`-indexed family of copies of `SymPow b V` to the complex numbers; despite its name it contains all such multilinear forms, and symmetry is the separate predicate `IsSymmetricMultilinearForm a b V T`. Here `SymPow b V` is realized as the span of the `b`-fold products of generators inside `SymmetricAlgebra`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/RepresentationTheory/FoulkesHowe/Model.lean

-- Generated from openai/math@1581d4c lean/OAI/RepresentationTheory/FoulkesHowe/Model.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the FoulkesHowe mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_FoulkesHowe

namespace OAI

noncomputable section

open scoped BigOperators
universe u

namespace Problem346

abbrev SymmetricMultilinearForm (a b : ℕ) (V : Type u)
    [AddCommGroup V] [Module ℂ V] :=
  MultilinearMap ℂ (fun _ : Fin a => SymPow b V) ℂ

def IsSymmetricMultilinearForm (a b : ℕ) (V : Type u)
    [AddCommGroup V] [Module ℂ V]
    (T : SymmetricMultilinearForm a b V) : Prop :=
  ∀ (σ : Equiv.Perm (Fin a)) (x : Fin a → SymPow b V),
    T (fun i => x (σ i)) = T x

end Problem346

end

end OAI


