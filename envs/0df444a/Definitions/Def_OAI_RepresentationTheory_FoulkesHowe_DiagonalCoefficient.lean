-- Prove2me | Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_DiagonalCoefficient
-- name    : OAI_RepresentationTheory_FoulkesHowe_DiagonalCoefficient
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T15:46:40.712876+00:00
-- url     : https://prove2.me/theorems/b566f2c9-7de6-40a8-8cd4-1d3cae275391
-- title:
--   Polynomial restriction of a multilinear form to an affine diagonal
-- statement:
--   Let $E$ be a complex vector space, $a\in\mathbb{N}$, and $T\colon E^a\to\mathbb{C}$ a $\mathbb{C}$-multilinear form (no symmetry is assumed). For vectors $x,y\in E$ and a subset $s\subseteq\{0,\dots,a-1\}$ let $z^{s}\in E^a$ be the tuple with $z^s_i=y$ for $i\in s$ and $z^s_i=x$ for $i\notin s$. The module defines the one-variable polynomial
--   $$
--   p_{T,x,y}(X)=\sum_{s\subseteq\{0,\dots,a-1\}}T(z^{s})\,X^{|s|}\in\mathbb{C}[X].
--   $$
--
--   By multilinearity, $p_{T,x,y}(c)=T(x+cy,\dots,x+cy)$ for every $c\in\mathbb{C}$, so $p_{T,x,y}$ is the restriction of $T$ to the diagonal along the affine line $c\mapsto x+cy$. Its coefficient of $X^k$ is the sum of the values $T(z^s)$ over the subsets with $|s|=k$; in particular the coefficient of $X$ is $\sum_{i}T(x,\dots,x,y,x,\dots,x)$, with $y$ in slot $i$. The polynomial is used for coefficient extraction: if $T(x+cy,\dots,x+cy)=0$ for all $c\in\mathbb{C}$, then $p_{T,x,y}=0$, so each of these coefficient sums vanishes.
--
--   **Formalization Note** `diagonalPolynomial T x y` is an element of Mathlib's univariate polynomial ring over $\mathbb{C}$, written as a finite sum over all finite subsets of `Fin a`; the tuple $z^s$ is `s.piecewise (fun _ => y) (fun _ => x)`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/RepresentationTheory/FoulkesHowe/DiagonalCoefficient.lean

-- Generated from openai/math@1581d4c lean/OAI/RepresentationTheory/FoulkesHowe/DiagonalCoefficient.lean by skeleton subtraction
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

namespace OAI

noncomputable section

open scoped BigOperators

namespace Problem346

universe u

variable {E : Type u} [AddCommGroup E] [Module ℂ E]

/-- The one-variable polynomial obtained by restricting a multilinear form to an affine diagonal. -/
def diagonalPolynomial {a : ℕ} (T : MultilinearMap ℂ (fun _ : Fin a => E) ℂ)
    (x y : E) : Polynomial ℂ :=
  ∑ s : Finset (Fin a),
    Polynomial.C (T (s.piecewise (fun _ => y) (fun _ => x))) * Polynomial.X ^ s.card

end Problem346

end

end OAI


