-- Prove2me | Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_SlotDerivative
-- name    : OAI_RepresentationTheory_FoulkesHowe_SlotDerivative
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T16:07:11.394864+00:00
-- url     : https://prove2.me/theorems/612acb8c-a076-4091-beba-ffdea9dfda12
-- title:
--   Slot polynomial of a coefficient array and a labelling of slots
-- statement:
--   Let $R$ be a commutative ring, $S$ a finite set of slots, $I$ a finite index set and $B$ an arbitrary set of block labels. Given a coefficient array $c$, which assigns a coefficient $c(f)\in R$ to every map $f\colon S\to I$, and a labelling $\ell\colon S\to B$ of the slots, the module defines the polynomial
--   $$
--   P_{c,\ell}=\sum_{f\colon S\to I}c(f)\prod_{s\in S}X_{(\ell(s),\,f(s))}\ \in\ R\bigl[X_{(b,i)} : b\in B,\ i\in I\bigr].
--   $$
--   Each term chooses an index $f(s)$ for every slot $s$ and multiplies the variables of the corresponding blocks.
--
--   This is the abstract form of the coordinate polynomial of a multilinear form: taking $c(f)=L\bigl((e_{f(s)})_{s\in S}\bigr)$ for a multilinear form $L$ and vectors $(e_i)_{i\in I}$ recovers that polynomial. In this generality one studies how a derivation that moves variables from one block to another acts on $P_{c,\ell}$ (it relabels one slot at a time) and how $P_{c,\ell}$ behaves when the slots are permuted.
--
--   **Formalization Note** `SlotPolynomial.polynomial c l` lies in the multivariate polynomial ring over $R$ with variables indexed by $B\times I$; the coefficient array `c` is a function on the maps from `S` to `I`, and decidable equality on `S` is part of the ambient context.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/RepresentationTheory/FoulkesHowe/SlotDerivative.lean

-- Generated from openai/math@1581d4c lean/OAI/RepresentationTheory/FoulkesHowe/SlotDerivative.lean by skeleton subtraction
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
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_FirstPolynomial
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_PolynomialShift
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_FirstCounts

namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem346.SlotPolynomial

variable {R A S I B : Type*} [CommRing R] [CommRing A] [Algebra R A] [DecidableEq S]

variable [Fintype S] [Fintype I]

/-- Coordinate polynomial of a coefficient array and an assignment of slots to blocks. -/
def polynomial (c : (S → I) → R) (l : S → B) : MvPolynomial (B × I) R :=
  ∑ k : S → I, MvPolynomial.C (c k) * ∏ s : S, MvPolynomial.X (l s, k s)

end Problem346.SlotPolynomial

end

end OAI


