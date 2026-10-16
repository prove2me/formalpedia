-- Prove2me | Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_FirstPolynomial
-- name    : OAI_RepresentationTheory_FoulkesHowe_FirstPolynomial
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T16:00:25.883967+00:00
-- url     : https://prove2.me/theorems/c9f1f111-63e0-42fc-b386-5a9cd8b8a1fb
-- title:
--   Stage polynomials of the first transfer sequence
-- statement:
--   Let $V$ be a complex vector space, $S(V)$ its symmetric algebra over $\mathbb{C}$, and $\mathrm{Sym}^nV\subseteq S(V)$ the $\mathbb{C}$-span of all products of $n$ vectors, with $[u_0,\dots,u_{n-1}]$ denoting such a product. Fix $r,m\in\mathbb{N}$, a multilinear form $T\colon(\mathrm{Sym}^{r+m}V)^{r+1}\to\mathbb{C}$, a finite index set $\kappa$ and a family of vectors $(e_q)_{q\in\kappa}$ of $V$. The ingredients are:
--
--   - the flattening $\widetilde T$ of $T$, the multilinear form in the $(r+1)(r+m)$ vector entries $v_{i,j}$ ($0\le i\le r$, $0\le j<r+m$) given by $\widetilde T(v)=T\bigl([v_{0,0},\dots,v_{0,r+m-1}],\dots,[v_{r,0},\dots,v_{r,r+m-1}]\bigr)$;
--   - the block labels $\mathsf{x},\mathsf{t},\mathsf{y}_0,\dots,\mathsf{y}_{m-1}$ and, for each $k\in\mathbb{N}$, the stage-$k$ labelling $\lambda_k$ of the slots: in row $0$, slot $j$ is labelled $\mathsf{y}_j$ if $j<k$ and $j<m$, and $\mathsf{t}$ otherwise; in each row $i\ge 1$, slot $j$ is labelled $\mathsf{x}$ if $j<r$ and $\mathsf{y}_{j-r}$ if $j\ge r$.
--
--   The stage-$k$ polynomial is the coordinate polynomial of $\widetilde T$ for this labelling,
--   $$
--   P_k=\sum_{f}\widetilde T\bigl((e_{f(i,j)})_{i,j}\bigr)\prod_{i=0}^{r}\prod_{j=0}^{r+m-1}X_{(\lambda_k(i,j),\,f(i,j))},
--   $$
--   where $f$ ranges over all maps from the slots to $\kappa$; it is a polynomial over $\mathbb{C}$ in the variables $X_{(c,q)}$ with $c$ a block label and $q\in\kappa$.
--
--   Evaluating $P_k$ at a point $z$ gives $\widetilde T$ applied to the grid in which every slot labelled $c$ carries the vector $\sum_q z_{(c,q)}e_q$. Writing $x,t,y_0,\dots,y_{m-1}$ for the vectors attached to the labels, for $k\le m$ this value is $T\bigl(y_0\cdots y_{k-1}\,t^{r+m-k},\ x^ry_0\cdots y_{m-1},\ \dots,\ x^ry_0\cdots y_{m-1}\bigr)$. The first transfer shows that $P_m=0$ forces $P_0=0$, which removes the common product $y_0\cdots y_{m-1}$ from the first argument.
--
--   **Formalization Note** `firstPolynomial T e k` is by definition `multilinearPolynomial (flattenedForm T) e (firstLabel r m k)`, a polynomial with complex coefficients in variables indexed by `FirstBlock m × κ`. The stage index $k$ is an arbitrary natural number; the stages $k\ge m$ all coincide.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/RepresentationTheory/FoulkesHowe/FirstPolynomial.lean

-- Generated from openai/math@1581d4c lean/OAI/RepresentationTheory/FoulkesHowe/FirstPolynomial.lean by skeleton subtraction
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
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_FlattenedForm
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_MultilinearPolynomial
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_BlockWeight

namespace OAI

noncomputable section
open scoped BigOperators
namespace Problem346
universe u v
variable {V : Type u} [AddCommGroup V] [Module ℂ V]
variable {κ : Type v} [Fintype κ]

/-- The scalar polynomial at the k-th stage of the first transfer sequence. -/
def firstPolynomial {r m : ℕ}
    (T : SymmetricMultilinearForm (r+1) (r+m) V) (e : κ → V) (k : ℕ) :
    MvPolynomial (FirstBlock m × κ) ℂ :=
  multilinearPolynomial (flattenedForm T) e (firstLabel r m k)

end Problem346

end

end OAI


