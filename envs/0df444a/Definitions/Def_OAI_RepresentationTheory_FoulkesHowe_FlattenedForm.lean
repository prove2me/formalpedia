-- Prove2me | Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_FlattenedForm
-- name    : OAI_RepresentationTheory_FoulkesHowe_FlattenedForm
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T15:51:48.22768+00:00
-- url     : https://prove2.me/theorems/a482ef41-9067-4621-8980-b5ec7afb7000
-- title:
--   Flattening a form on symmetric powers into a multilinear form on vectors
-- statement:
--   Let $V$ be a complex vector space, $S(V)$ its symmetric algebra over $\mathbb{C}$, $\mathrm{Sym}^bV\subseteq S(V)$ the $\mathbb{C}$-span of all products of $b$ vectors of $V$, and $[u_0,\dots,u_{b-1}]\in\mathrm{Sym}^bV$ the product $u_0\cdots u_{b-1}$. Let $T\colon(\mathrm{Sym}^bV)^a\to\mathbb{C}$ be a $\mathbb{C}$-multilinear form of arity $a$.
--
--   The flattening of $T$ is the multilinear form in $ab$ vector arguments $v=(v_{i,j})_{0\le i<a,\ 0\le j<b}$ given by
--   $$
--   \widetilde T(v)=T\bigl([v_{0,0},\dots,v_{0,b-1}],\ [v_{1,0},\dots,v_{1,b-1}],\ \dots,\ [v_{a-1,0},\dots,v_{a-1,b-1}]\bigr),
--   $$
--   so the $i$-th argument of $T$ is the monomial formed from row $i$. Two special cases are recorded as lemmas:
--
--   1. if $v_{i,j}=u_i$ depends only on the row, then $\widetilde T(v)=T(u_0^{\,b},\dots,u_{a-1}^{\,b})$, where $u^b=[u,\dots,u]$;
--   2. if $v_{i,j}=w_j$ depends only on the column, then $\widetilde T(v)=T\bigl([w_0,\dots,w_{b-1}],\dots,[w_0,\dots,w_{b-1}]\bigr)$, the same monomial in all $a$ arguments.
--
--   Flattening turns statements about $T$ evaluated on monomials into statements about an ordinary multilinear form on $V$, to which coordinate polynomials and polarization operators can then be applied.
--
--   **Formalization Note** The form is `flattenedSymmetricForm T`, indexed by `Fin a × Fin b`; `flattenedForm` is a compatibility abbreviation for the same object with the degrees inferred. The definition composes $T$ with the bundled monomial maps and reindexes along `Equiv.sigmaEquivProd`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/RepresentationTheory/FoulkesHowe/FlattenedForm.lean

-- Generated from openai/math@1581d4c lean/OAI/RepresentationTheory/FoulkesHowe/FlattenedForm.lean by skeleton subtraction
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
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_Naturality
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_DualEmbedding
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_PairingConstruction
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_FoulkesMultilinear
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_CanonicalMap
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_Multiplication
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_VanishingInduction
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_DiagonalCoefficient
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_FirstLabels

namespace OAI

noncomputable section

namespace Problem346

universe u

variable {a b : ℕ} {V : Type u} [AddCommGroup V] [Module ℂ V]

/-- A form on symmetric powers, evaluated on products, is multilinear in all
of the underlying vector factors. -/
def flattenedSymmetricForm (T : SymmetricMultilinearForm a b V) :
    MultilinearMap ℂ (fun _ : Fin a × Fin b => V) ℂ :=
  (T.compMultilinearMap (fun _ => symMonomialMultilinear b V)).domDomCongr
    (Equiv.sigmaEquivProd (Fin a) (Fin b))

@[simp]
theorem flattenedSymmetricForm_apply (T : SymmetricMultilinearForm a b V)
    (v : Fin a × Fin b → V) :
    flattenedSymmetricForm T v =
      T (fun i => symMonomial b V (fun j => v (i, j))) := rfl

/-- Compatibility API for the same flattened form, with inferred degrees. -/
abbrev flattenedForm {a b : ℕ} {V : Type u} [AddCommGroup V] [Module ℂ V]
    (T : SymmetricMultilinearForm a b V) :
    MultilinearMap ℂ (fun _ : Fin a × Fin b => V) ℂ :=
  flattenedSymmetricForm T

@[simp]
theorem flattenedForm_apply {a b : ℕ} {V : Type u} [AddCommGroup V] [Module ℂ V]
    (T : SymmetricMultilinearForm a b V) (x : Fin a × Fin b → V) :
    flattenedForm T x = T (fun i => symMonomial b V (fun j => x (i, j))) := rfl

@[simp] theorem flattenedForm_constant_rows (T : SymmetricMultilinearForm a b V)
    (v : Fin a → V) :
    flattenedForm T (fun p => v p.1) =
      T (fun i => symMonomial b V (fun _ => v i)) := rfl

@[simp] theorem flattenedForm_constant_columns (T : SymmetricMultilinearForm a b V)
    (v : Fin b → V) :
    flattenedForm T (fun p => v p.2) =
      T (fun _ => symMonomial b V v) := rfl

end Problem346

end

end OAI


