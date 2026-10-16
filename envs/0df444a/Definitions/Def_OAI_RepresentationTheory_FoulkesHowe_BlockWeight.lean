-- Prove2me | Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_BlockWeight
-- name    : OAI_RepresentationTheory_FoulkesHowe_BlockWeight
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T15:56:17.114691+00:00
-- url     : https://prove2.me/theorems/d05ac360-927c-45ff-932b-584ce61405b5
-- title:
--   Weighted Euler derivations and block-homogeneous polynomials
-- statement:
--   Let $R$ be a commutative semiring and $\sigma$ a finite set of variables, and consider the polynomial ring $R[X_s : s\in\sigma]$ with partial derivatives $\partial_s=\partial/\partial X_s$. The module defines:
--
--   1. **Weighted Euler derivation.** For a weight function $w\colon\sigma\to\mathbb{N}$, the $R$-derivation
--   $$
--   E_w=\sum_{s\in\sigma}w_s\,X_s\,\partial_s,\qquad\text{that is,}\qquad E_w(f)=\sum_{s\in\sigma}w_s\,X_s\,\frac{\partial f}{\partial X_s},
--   $$
--   so that $E_w(X_s)=w_sX_s$; both identities are recorded as lemmas.
--   2. **Block weight.** For variables indexed by pairs $(c,i)\in\beta\times\iota$ of a block label and a coordinate index, with $\beta$ and $\iota$ finite, and a chosen block $u\in\beta$, the weight $\omega_u(c,i)=1$ if $c=u$ and $\omega_u(c,i)=0$ otherwise.
--   3. **Block homogeneity.** A polynomial $f\in R[X_{(c,i)} : (c,i)\in\beta\times\iota]$ is block-homogeneous of degree $n$ in block $u$ if it is weighted homogeneous of degree $n$ for $\omega_u$: every monomial occurring in $f$ with nonzero coefficient has total degree exactly $n$ in the variables $X_{(u,i)}$, $i\in\iota$.
--
--   For a block weight, $E_{\omega_u}=\sum_iX_{(u,i)}\,\partial/\partial X_{(u,i)}$ counts the degree in block $u$, so a polynomial that is block-homogeneous of degree $n$ in $u$ satisfies $E_{\omega_u}(f)=nf$. These degree counts are used to show that a polarization operator moving degree from one block to another kills no nonzero polynomial that is block-homogeneous in both blocks with strictly larger degree in the source block than in the target block.
--
--   **Formalization Note** Block homogeneity is Mathlib's `MvPolynomial.IsWeightedHomogeneous` for the weight `blockWeight u`; in particular the zero polynomial is block-homogeneous of every degree. The natural-number weights act on derivations through the scalar action of $\mathbb{N}$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/RepresentationTheory/FoulkesHowe/BlockWeight.lean

-- Generated from openai/math@1581d4c lean/OAI/RepresentationTheory/FoulkesHowe/BlockWeight.lean by skeleton subtraction
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

namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem346
namespace PolynomialWeights

open MvPolynomial

variable {R σ : Type*} [CommSemiring R] [Fintype σ]

/-- The Euler derivation associated with natural-number weights. -/
def weightedEuler (w : σ → ℕ) :
    Derivation R (MvPolynomial σ R) (MvPolynomial σ R) :=
  ∑ i : σ, (w i) • ((X i : MvPolynomial σ R) • pderiv i)

@[simp] theorem weightedEuler_apply (w : σ → ℕ) (f : MvPolynomial σ R) :
    weightedEuler w f = ∑ i : σ, w i • (X i * pderiv i f) := by
  classical
  unfold weightedEuler
  induction (Finset.univ : Finset σ) using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih => simp [Finset.sum_insert ha, Derivation.smul_apply, ih, smul_eq_mul] <;> ring

@[simp] theorem weightedEuler_X (w : σ → ℕ) (i : σ) :
    weightedEuler (R := R) w (X i) = w i • X i := by
  classical
  simp [weightedEuler_apply, Pi.single_apply]

section Blocks

variable {β ι : Type*} [Fintype β] [Fintype ι] [DecidableEq β]

/-- Weight one on one coordinate block, and zero on all spectator blocks. -/
def blockWeight (u : β) (ki : β × ι) : ℕ := if ki.1 = u then 1 else 0

/-- A polynomial is homogeneous of the specified degree in one block. -/
def IsBlockHomogeneous (u : β) (f : MvPolynomial (β × ι) R) (n : ℕ) : Prop :=
  f.IsWeightedHomogeneous (blockWeight u) n

omit [Fintype β] [Fintype ι] in
@[simp] theorem blockWeight_apply (u k : β) (i : ι) :
    blockWeight u (k, i) = if k = u then 1 else 0 := rfl

end Blocks

end PolynomialWeights
end Problem346

end

end OAI


