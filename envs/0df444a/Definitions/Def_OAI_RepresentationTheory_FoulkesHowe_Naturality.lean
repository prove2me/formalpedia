-- Prove2me | Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_Naturality
-- name    : OAI_RepresentationTheory_FoulkesHowe_Naturality
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T15:31:30.72165+00:00
-- url     : https://prove2.me/theorems/e53e3488-c8ed-43e1-ba49-b22d99e4e821
-- title:
--   Functoriality of the plethysm $\mathrm{Sym}^p(\mathrm{Sym}^q V)$ in the vector space $V$
-- statement:
--   Let $V,W,U$ be complex vector spaces. For a complex vector space $X$ and $n\in\mathbb{N}$, let $\mathrm{Sym}^n X$ be the linear span, inside the symmetric algebra $S(X)$ over $\mathbb{C}$, of the products $[x_0,\dots,x_{n-1}]=x_0\cdots x_{n-1}$ of $n$ elements of $X$; a linear map $f:X\to Y$ induces the linear map $\mathrm{Sym}^n f:\mathrm{Sym}^n X\to\mathrm{Sym}^n Y$ with $[x_0,\dots,x_{n-1}]\mapsto[f(x_0),\dots,f(x_{n-1})]$. Fix an outer degree $p\in\mathbb{N}$ and an inner degree $q\in\mathbb{N}$.
--
--   1. **Induced map.** For a linear map $f:V\to W$ put $P(f)=\mathrm{Sym}^p(\mathrm{Sym}^q f):\mathrm{Sym}^p(\mathrm{Sym}^q V)\to\mathrm{Sym}^p(\mathrm{Sym}^q W)$. For every array $(x_{i,j})$ of vectors of $V$, $0\le i<p$, $0\le j<q$,
--   $$P(f)\Bigl[[x_{0,0},\dots,x_{0,q-1}],\dots,[x_{p-1,0},\dots,x_{p-1,q-1}]\Bigr]=\Bigl[[f(x_{0,0}),\dots,f(x_{0,q-1})],\dots,[f(x_{p-1,0}),\dots,f(x_{p-1,q-1})]\Bigr].$$
--   2. **Functoriality.** $P(\mathrm{id}_V)=\mathrm{id}$, and $P(g\circ f)=P(g)\circ P(f)$ for linear maps $f:V\to W$ and $g:W\to U$.
--   3. **Compatibility with the group action.** For a linear automorphism $g$ of $V$, $P(g)$ coincides with the action $\rho(g)=\mathrm{Sym}^p(\mathrm{Sym}^q g)$ of $g$ on $\mathrm{Sym}^p(\mathrm{Sym}^q V)$.
--
--   Thus $V\mapsto\mathrm{Sym}^p(\mathrm{Sym}^q V)$ is a functor on complex vector spaces extending the $\mathrm{GL}(V)$-action to arbitrary linear maps, for example inclusions of subspaces or projections onto them.
--
--   **Formalization Note** `plethysmMap outer inner f` is `symPowMap outer (symPowMap inner f)`; item 3 is `plethysmMap_equiv`, which holds by definition.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/RepresentationTheory/FoulkesHowe/Naturality.lean

-- Generated from openai/math@1581d4c lean/OAI/RepresentationTheory/FoulkesHowe/Naturality.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the FoulkesHowe mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_FoulkesHowe
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_Model
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_DegreeOne
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_Functoriality
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_LinearCase
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_PermanentPairing
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_SymmetricLift
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_AlgebraEvaluation
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_SymmetricDual
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_TensorPresentation
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_FiniteDimension
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_MonomialMultilinear
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_Spanning
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_Actions

namespace OAI

noncomputable section
open scoped BigOperators
universe u v w
namespace Problem346

variable {V : Type u} {W : Type v} {U : Type w}
  [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
  [AddCommGroup U] [Module ℂ U]

/-- The map on a plethysm induced by a linear map on the original space. -/
def plethysmMap (outer inner : ℕ) (f : V →ₗ[ℂ] W) :
    SymPow outer (SymPow inner V) →ₗ[ℂ] SymPow outer (SymPow inner W) :=
  symPowMap outer (symPowMap inner f)

@[simp] theorem plethysmMap_symMonomial (outer inner : ℕ) (f : V →ₗ[ℂ] W)
    (x : Fin outer → Fin inner → V) :
    plethysmMap outer inner f
        (symMonomial outer (SymPow inner V) (fun i => symMonomial inner V (x i))) =
      symMonomial outer (SymPow inner W)
        (fun i => symMonomial inner W (fun j => f (x i j))) := by
  simp [plethysmMap]

@[simp] theorem plethysmMap_id (outer inner : ℕ) :
    plethysmMap outer inner (LinearMap.id : V →ₗ[ℂ] V) = LinearMap.id := by
  simp [plethysmMap]

@[simp] theorem plethysmMap_comp (outer inner : ℕ) (g : W →ₗ[ℂ] U) (f : V →ₗ[ℂ] W) :
    plethysmMap outer inner (g.comp f) =
      (plethysmMap outer inner g).comp (plethysmMap outer inner f) := by
  simp [plethysmMap]

@[simp] theorem plethysmMap_equiv (outer inner : ℕ) (g : V ≃ₗ[ℂ] V) :
    plethysmMap outer inner g.toLinearMap = plethysmAction outer inner g := rfl

end Problem346

end

end OAI


