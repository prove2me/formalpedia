-- Prove2me | Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_MonomialMultilinear
-- name    : OAI_RepresentationTheory_FoulkesHowe_MonomialMultilinear
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T15:24:31.093231+00:00
-- url     : https://prove2.me/theorems/664a5a52-7392-46e2-b475-d0eb806df552
-- title:
--   Functionals on $\mathrm{Sym}^a(\mathrm{Sym}^b V)$ as $a$-linear forms, and their flattening to $ab$ vector arguments
-- statement:
--   Let $V$ be a complex vector space. For a complex vector space $U$ and $n\in\mathbb{N}$, let $\mathrm{Sym}^n U$ be the linear span, inside the symmetric algebra $S(U)$ over $\mathbb{C}$, of the products $[u_0,\dots,u_{n-1}]=u_0u_1\cdots u_{n-1}$ of $n$ elements of $U$. Taking $U=V$ and then $U=\mathrm{Sym}^b V$ gives the plethysm $\mathrm{Sym}^a(\mathrm{Sym}^b V)$. Fix $a,b\in\mathbb{N}$.
--
--   1. **Product map.** For each $n$, the map $\pi_n:V^n\to\mathrm{Sym}^n V$, $\pi_n(v_0,\dots,v_{n-1})=[v_0,\dots,v_{n-1}]$, regarded as a multilinear map.
--   2. **From functionals to forms.** A linear functional $\varphi:\mathrm{Sym}^a(\mathrm{Sym}^b V)\to\mathbb{C}$ determines the $a$-linear form on $\mathrm{Sym}^b V$
--   $$T_\varphi(x_0,\dots,x_{a-1})=\varphi\bigl([x_0,\dots,x_{a-1}]\bigr),\qquad x_0,\dots,x_{a-1}\in\mathrm{Sym}^b V.$$
--   3. **Flattening.** An $a$-linear form $T:(\mathrm{Sym}^b V)^a\to\mathbb{C}$ determines a form $\widetilde T$ in $ab$ vector arguments $x_{i,j}\in V$, indexed by pairs $(i,j)$ with $0\le i<a$ and $0\le j<b$:
--   $$\widetilde T\bigl((x_{i,j})_{i,j}\bigr)=T\Bigl([x_{0,0},\dots,x_{0,b-1}],\ \dots,\ [x_{a-1,0},\dots,x_{a-1,b-1}]\Bigr),$$
--   and $\widetilde T$ is linear in each of the $ab$ vectors separately.
--
--   These maps translate statements about linear functionals on the plethysm into statements about multilinear forms. Because products in a symmetric algebra commute, $T_\varphi$ is symmetric in its $a$ arguments, and $\varphi$ is determined by $T_\varphi$ since products span $\mathrm{Sym}^a(\mathrm{Sym}^b V)$; flattening then turns such a form into a multilinear form in the individual vectors, to which polynomial and differentiation arguments apply.
--
--   **Formalization Note** The three objects are `symMonomialMultilinear n V`, `monomialFunctional a b V φ` (valued in `SymmetricMultilinearForm a b V`, the type of all `a`-linear forms on `SymPow b V`) and `plethysmFormMultilinear a b V T`, whose arguments are indexed by the sigma type of pairs `⟨i, j⟩` with `i : Fin a` and `j : Fin b`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/RepresentationTheory/FoulkesHowe/MonomialMultilinear.lean

-- Generated from openai/math@1581d4c lean/OAI/RepresentationTheory/FoulkesHowe/MonomialMultilinear.lean by skeleton subtraction
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

namespace OAI

noncomputable section

open scoped BigOperators

universe u v

namespace Problem346

/-- The product of degree-one generators, with its multilinearity bundled. -/
def symMonomialMultilinear (n : ℕ) (V : Type u)
    [AddCommGroup V] [Module ℂ V] :
    MultilinearMap ℂ (fun _ : Fin n => V) (SymPow n V) :=
  ((MultilinearMap.mkPiAlgebra ℂ (Fin n) (SymmetricAlgebra ℂ V)).compLinearMap
    (fun _ => SymmetricAlgebra.ι ℂ V)).codRestrict (symPowSubmodule n V)
      (fun x => Submodule.subset_span (Set.mem_range_self x))

@[simp]
theorem symMonomialMultilinear_apply (n : ℕ) (V : Type u)
    [AddCommGroup V] [Module ℂ V] (x : Fin n → V) :
    symMonomialMultilinear n V x = symMonomial n V x := rfl

/-- A functional on a symmetric power induces a symmetric multilinear form. -/
def monomialFunctional (a b : ℕ) (V : Type u)
    [AddCommGroup V] [Module ℂ V]
    (φ : SymPow a (SymPow b V) →ₗ[ℂ] ℂ) : SymmetricMultilinearForm a b V :=
  φ.compMultilinearMap (symMonomialMultilinear a (SymPow b V))

@[simp]
theorem monomialFunctional_apply (a b : ℕ) (V : Type u)
    [AddCommGroup V] [Module ℂ V]
    (φ : SymPow a (SymPow b V) →ₗ[ℂ] ℂ) (x : Fin a → SymPow b V) :
    monomialFunctional a b V φ x = φ (symMonomial a (SymPow b V) x) := rfl

/-- Flatten the `a` rows of `b` vector arguments of a form on `SymPow b V`. -/
def plethysmFormMultilinear (a b : ℕ) (V : Type u)
    [AddCommGroup V] [Module ℂ V] (T : SymmetricMultilinearForm a b V) :
    MultilinearMap ℂ (fun _ : Σ _ : Fin a, Fin b => V) ℂ :=
  T.compMultilinearMap (fun _ => symMonomialMultilinear b V)

@[simp]
theorem plethysmFormMultilinear_apply (a b : ℕ) (V : Type u)
    [AddCommGroup V] [Module ℂ V] (T : SymmetricMultilinearForm a b V)
    (x : (Σ _ : Fin a, Fin b) → V) :
    plethysmFormMultilinear a b V T x =
      T (fun i => symMonomial b V (fun j => x ⟨i,j⟩)) := rfl

end Problem346

end

end OAI


