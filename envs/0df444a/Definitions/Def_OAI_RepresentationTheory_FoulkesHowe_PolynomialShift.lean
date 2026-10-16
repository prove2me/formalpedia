-- Prove2me | Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_PolynomialShift
-- name    : OAI_RepresentationTheory_FoulkesHowe_PolynomialShift
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T16:03:23.784099+00:00
-- url     : https://prove2.me/theorems/cdc5f0e5-26d9-40c4-aba3-2a85be119a1e
-- title:
--   Polarization derivation moving degree from one block of variables to another
-- statement:
--   Let $K$ be a commutative ring, $B$ a set of block labels and $I$ an index set, and consider the polynomial ring $K[X_{(c,i)} : c\in B,\ i\in I]$ whose variables are indexed by pairs of a block and an index. For blocks $\mathrm{src},\mathrm{dst}\in B$ the module defines:
--
--   1. **Transfer derivation.** The unique $K$-derivation $D_{\mathrm{src}\to\mathrm{dst}}$ of this polynomial ring with
--   $$
--   D_{\mathrm{src}\to\mathrm{dst}}\bigl(X_{(c,i)}\bigr)=\begin{cases}X_{(\mathrm{dst},i)}&\text{if } c=\mathrm{src},\\ 0&\text{otherwise,}\end{cases}
--   $$
--   that is, $D_{\mathrm{src}\to\mathrm{dst}}=\sum_{i\in I}X_{(\mathrm{dst},i)}\,\partial/\partial X_{(\mathrm{src},i)}$, where on each polynomial only finitely many terms are nonzero. It replaces one variable of block $\mathrm{src}$ by the corresponding variable of block $\mathrm{dst}$ in all possible ways, so for $\mathrm{src}\ne\mathrm{dst}$ it lowers the degree in $\mathrm{src}$ by one and raises the degree in $\mathrm{dst}$ by one; variables of all other blocks are spectators. A lemma records the displayed values on variables.
--   2. **Shift operator.** The same map regarded as a $K$-linear endomorphism of the polynomial ring.
--
--   These are polarization operators. For $\mathrm{src}=\mathrm{dst}=u$ the derivation is the Euler operator $\sum_iX_{(u,i)}\,\partial/\partial X_{(u,i)}$ counting the degree in block $u$. The operators $D_{\mathrm{src}\to\mathrm{dst}}$, $D_{\mathrm{dst}\to\mathrm{src}}$ and the difference of the two Euler operators satisfy the commutation relations of an $\mathfrak{sl}_2$-triple, which is used to show that, for $\mathrm{src}\ne\mathrm{dst}$, the shift kills no nonzero polynomial that is block-homogeneous in both blocks with strictly larger degree in $\mathrm{src}$ than in $\mathrm{dst}$.
--
--   **Formalization Note** The derivation is built with `MvPolynomial.mkDerivation` from its values on the variables, using classical decidability of equality of blocks; `shift src dst` is its underlying linear map.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/RepresentationTheory/FoulkesHowe/PolynomialShift.lean

-- Generated from openai/math@1581d4c lean/OAI/RepresentationTheory/FoulkesHowe/PolynomialShift.lean by skeleton subtraction
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

namespace OAI

noncomputable section

open scoped BigOperators

namespace Problem346
namespace PolynomialShift

variable {K B I : Type*} [CommRing K]

attribute [local instance] Classical.propDecidable

/-- Transfer one unit of polynomial degree from `src` to `dst`. Other blocks
are spectator variables. -/
def derivation (src dst : B) :
    Derivation K (MvPolynomial (B × I) K) (MvPolynomial (B × I) K) := by
  classical
  exact MvPolynomial.mkDerivation K
    (fun v => if v.1 = src then MvPolynomial.X (dst, v.2) else 0)

@[simp]
theorem derivation_X (src dst block : B) (i : I) :
    derivation (K := K) src dst (MvPolynomial.X (block, i)) =
      if block = src then MvPolynomial.X (dst, i) else 0 := by
  classical
  simp [derivation]

/-- The directional shift as a linear endomorphism. -/
def shift (src dst : B) : Module.End K (MvPolynomial (B × I) K) :=
  (derivation src dst).toLinearMap

@[simp]
theorem shift_apply (src dst : B) (p : MvPolynomial (B × I) K) :
    shift src dst p = derivation src dst p := rfl

end PolynomialShift
end Problem346

end

end OAI


