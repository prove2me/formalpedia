-- Prove2me | Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_MultilinearPolynomial
-- name    : OAI_RepresentationTheory_FoulkesHowe_MultilinearPolynomial
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T15:52:27.323558+00:00
-- url     : https://prove2.me/theorems/e2d41aff-f403-476c-8247-a58032ca0374
-- title:
--   Coordinate polynomial of a multilinear form with block-labelled slots
-- statement:
--   Let $V$ be a complex vector space, $\iota$ and $\kappa$ finite sets, and $\beta$ an arbitrary set of block labels. The data are a $\mathbb{C}$-multilinear form $L\colon V^{\iota}\to\mathbb{C}$ (one vector argument for each slot $i\in\iota$), a family of vectors $(e_q)_{q\in\kappa}$ of $V$ (typically a basis), and a labelling $\mathrm{block}\colon\iota\to\beta$ of the slots. The module defines the polynomial in commuting variables $X_{(c,q)}$, $c\in\beta$, $q\in\kappa$,
--   $$
--   P_{L,e,\mathrm{block}}=\sum_{f\colon\iota\to\kappa}L\bigl((e_{f(i)})_{i\in\iota}\bigr)\prod_{i\in\iota}X_{(\mathrm{block}(i),\,f(i))}\ \in\ \mathbb{C}\bigl[X_{(c,q)} : c\in\beta,\ q\in\kappa\bigr],
--   $$
--   where the sum runs over all maps $f$ from slots to indices.
--
--   By multilinearity, evaluating $P_{L,e,\mathrm{block}}$ at a point $z$ gives $L\bigl((v_{\mathrm{block}(i)})_{i\in\iota}\bigr)$, where $v_c=\sum_{q}z_{(c,q)}e_q$ is a vector variable attached to block $c$: all slots carrying the same label receive the same vector. Thus the polynomial encodes, in the coordinates of the blocks, the function $(v_c)_{c\in\beta}\mapsto L\bigl((v_{\mathrm{block}(i)})_i\bigr)$. This converts identities between vector expressions into polynomial identities, on which polarization derivations that move degree from one block to another can act.
--
--   **Formalization Note** `multilinearPolynomial L e block` lies in the multivariate polynomial ring over $\mathbb{C}$ with variables indexed by $\beta\times\kappa$ (`MvPolynomial (β × κ)`); the variable indexed by $(c,q)$ is `MvPolynomial.X (c, q)`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/RepresentationTheory/FoulkesHowe/MultilinearPolynomial.lean

-- Generated from openai/math@1581d4c lean/OAI/RepresentationTheory/FoulkesHowe/MultilinearPolynomial.lean by skeleton subtraction
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

namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem346

universe uι uκ uβ uV
variable {ι : Type uι} {κ : Type uκ} {β : Type uβ} {V : Type uV}
variable [Fintype ι] [Fintype κ] [AddCommGroup V] [Module ℂ V]

/-- The scalar polynomial obtained by feeding a multilinear form vector variables,
with `block i` specifying which vector variable occurs in its `i`th argument. -/
def multilinearPolynomial (L : MultilinearMap ℂ (fun _ : ι => V) ℂ)
    (e : κ → V) (block : ι → β) : MvPolynomial (β × κ) ℂ := by
  classical
  exact ∑ k : ι → κ,
    MvPolynomial.C (L (fun i => e (k i))) *
      ∏ i, MvPolynomial.X (block i, k i)

end Problem346

end

end OAI


