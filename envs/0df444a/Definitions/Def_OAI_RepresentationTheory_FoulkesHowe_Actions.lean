-- Prove2me | Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_Actions
-- name    : OAI_RepresentationTheory_FoulkesHowe_Actions
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T15:27:18.23845+00:00
-- url     : https://prove2.me/theorems/f9b1739b-9a8d-4ba5-bec6-1467e6e694bc
-- title:
--   The action of $\mathrm{GL}(V)$ on the plethysm $\mathrm{Sym}^p(\mathrm{Sym}^q V)$
-- statement:
--   Let $V$ be a complex vector space and $\mathrm{GL}(V)$ the group of its linear automorphisms. For a complex vector space $U$ and $n\in\mathbb{N}$, let $\mathrm{Sym}^n U$ be the linear span, inside the symmetric algebra $S(U)$ over $\mathbb{C}$, of the products $[u_0,\dots,u_{n-1}]=u_0\cdots u_{n-1}$ of $n$ elements of $U$; a linear isomorphism $e:U\to U'$ induces the linear isomorphism $\mathrm{Sym}^n e:\mathrm{Sym}^n U\to\mathrm{Sym}^n U'$ with $[u_0,\dots,u_{n-1}]\mapsto[e(u_0),\dots,e(u_{n-1})]$. Fix an outer degree $p\in\mathbb{N}$ and an inner degree $q\in\mathbb{N}$.
--
--   1. **The action.** For $g\in\mathrm{GL}(V)$, $\rho(g)=\mathrm{Sym}^p(\mathrm{Sym}^q g)$ is a linear automorphism of $\mathrm{Sym}^p(\mathrm{Sym}^q V)$. For every array $(x_{i,j})$ of vectors of $V$, $0\le i<p$, $0\le j<q$, it acts on products of products by
--   $$\rho(g)\Bigl[[x_{0,0},\dots,x_{0,q-1}],\dots,[x_{p-1,0},\dots,x_{p-1,q-1}]\Bigr]=\Bigl[[g x_{0,0},\dots,g x_{0,q-1}],\dots,[g x_{p-1,0},\dots,g x_{p-1,q-1}]\Bigr].$$
--   2. **Representation property.** $\rho(\mathrm{id}_V)=\mathrm{id}$; $\rho(h\circ g)=\rho(h)\circ\rho(g)$ for all $g,h\in\mathrm{GL}(V)$; and $\rho(g^{-1})\circ\rho(g)=\rho(g)\circ\rho(g^{-1})=\mathrm{id}$.
--
--   Thus $\rho$ is the natural representation of $\mathrm{GL}(V)$ on the plethysm $\mathrm{Sym}^p(\mathrm{Sym}^q V)$. It is the setting in which linear maps between $\mathrm{Sym}^b(\mathrm{Sym}^a V)$ and $\mathrm{Sym}^a(\mathrm{Sym}^b V)$ given by formulas in the vectors, such as the Foulkes–Howe map, are studied as homomorphisms of $\mathrm{GL}(V)$-modules.
--
--   **Formalization Note** `plethysmEquiv outer inner g` is the linear equivalence `symPowEquiv outer (symPowEquiv inner g)` and `plethysmAction outer inner g` its underlying linear map. In `plethysmAction_trans`, the equivalence `g.trans h` means first `g`, then `h`, i.e. the composite $h\circ g$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/RepresentationTheory/FoulkesHowe/Actions.lean

-- Generated from openai/math@1581d4c lean/OAI/RepresentationTheory/FoulkesHowe/Actions.lean by skeleton subtraction
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

namespace OAI

noncomputable section
open scoped BigOperators
universe u
namespace Problem346

variable {V : Type u} [AddCommGroup V] [Module ℂ V]

/-- The canonical action of a linear automorphism on a plethysm. -/
def plethysmEquiv (outer inner : ℕ) (g : V ≃ₗ[ℂ] V) :
    SymPow outer (SymPow inner V) ≃ₗ[ℂ] SymPow outer (SymPow inner V) :=
  symPowEquiv outer (symPowEquiv inner g)

/-- The underlying endomorphism of the canonical plethysm action. -/
def plethysmAction (outer inner : ℕ) (g : V ≃ₗ[ℂ] V) :
    SymPow outer (SymPow inner V) →ₗ[ℂ] SymPow outer (SymPow inner V) :=
  (plethysmEquiv outer inner g).toLinearMap

@[simp] theorem plethysmAction_symMonomial (outer inner : ℕ) (g : V ≃ₗ[ℂ] V)
    (x : Fin outer → Fin inner → V) :
    plethysmAction outer inner g
      (symMonomial outer (SymPow inner V) (fun i => symMonomial inner V (x i))) =
    symMonomial outer (SymPow inner V)
      (fun i => symMonomial inner V (fun j => g (x i j))) := by
  simp [plethysmAction, plethysmEquiv]

@[simp] theorem plethysmAction_refl (outer inner : ℕ) :
    plethysmAction outer inner (LinearEquiv.refl ℂ V) = LinearMap.id := by
  simp [plethysmAction, plethysmEquiv]

@[simp] theorem plethysmAction_trans (outer inner : ℕ) (g h : V ≃ₗ[ℂ] V) :
    plethysmAction outer inner (g.trans h) =
      (plethysmAction outer inner h).comp (plethysmAction outer inner g) := by
  change symPowMap outer (symPowMap inner (g.trans h).toLinearMap) = _
  change symPowMap outer (symPowMap inner (h.toLinearMap.comp g.toLinearMap)) = _
  rw [symPowMap_comp, symPowMap_comp]
  rfl

@[simp] theorem plethysmAction_symm_comp (outer inner : ℕ) (g : V ≃ₗ[ℂ] V) :
    (plethysmAction outer inner g.symm).comp (plethysmAction outer inner g) =
      LinearMap.id := by
  rw [← plethysmAction_trans]
  simp

@[simp] theorem plethysmAction_comp_symm (outer inner : ℕ) (g : V ≃ₗ[ℂ] V) :
    (plethysmAction outer inner g).comp (plethysmAction outer inner g.symm) =
      LinearMap.id := by
  rw [← plethysmAction_trans]
  simp

end Problem346

end

end OAI


