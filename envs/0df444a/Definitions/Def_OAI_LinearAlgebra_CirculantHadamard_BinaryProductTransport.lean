-- Prove2me | Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_BinaryProductTransport
-- name    : OAI_LinearAlgebra_CirculantHadamard_BinaryProductTransport
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T08:31:38.801182+00:00
-- url     : https://prove2.me/theorems/0a6a72d4-7334-44ab-bdb2-66c8e6aacd08
-- title:
--   Local units mapped into the fraction field
-- statement:
--   These notions belong to a formal proof that a real circulant Hadamard matrix of positive order $n$ exists only for $n=1$ and $n=4$. Such a matrix has entries $\pm1$, satisfies $HH^{\mathsf T}=nI$, and has the form $H_{ij}=h(j-i)$ with indices in $\mathbb Z/n$. Its first row becomes an element $f$ of the integer group ring $\mathbb Z[\mathbb Z/n]$ with $f f^{*}=n$, where $f^{*}$ reverses the indices. Two-adic descent reduces every order $n>1$ to $n=4u^2$ with $u$ odd; for $u>1$, evaluation at characters with values in cyclotomic rings and a local argument at a prime above $2$ give a contradiction.
--
--   1. **Units to fractions.** For odd $u$, the monoid homomorphism from the unit group of the local ring $O_u=(B_u)_{\mathfrak m_u}$ into the fraction field of $B_u$,
--   $$
--   O_u^{\times}\longrightarrow\operatorname{Frac}(B_u),\qquad X\mapsto X,
--   $$
--   given by the canonical embedding of $O_u$. An alternating product of local units maps to the alternating product of their values in the fraction field, and injectivity carries power identities back to the local units with the same exponent.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/LinearAlgebra/CirculantHadamard/BinaryProductTransport.lean

-- Generated from openai/math@1581d4c lean/OAI/LinearAlgebra/CirculantHadamard/BinaryProductTransport.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the CirculantHadamard mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_CirculantHadamard
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_Basic
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_Witnesses
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_MatrixBridge
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_CyclicRing
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_CyclicNorm
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_CyclicProjection
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_LocalDVR
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_IntegerTwoLocal
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_CyclicEvaluation
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_CyclicPolynomial
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_RamifiedConjugation
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_CyclotomicIntegerEvaluation
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_DyadicRemainder
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_RamifiedEisenstein
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_RamifiedLocal
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_OrderHalving
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_BinaryBlocks
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_BinaryCoefficients
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_CyclotomicRings
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_PrimeComponents
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_PrimeCharacterEvaluations
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_BinaryEvaluation
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_LocalizationMaps
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_BinaryLocalization
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_BinaryLocalRing
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_AlternatingProducts

namespace OAI

universe uG uI

/-!
# Odd-power products in the concrete binary local ring

The local units are supplied with their actual coefficient-ring values.
Their alternating product maps to the fixed alternating product in the
fraction field. Injectivity transports each exact power identity back to
the local units, with the same exponent.
-/

noncomputable section

namespace CirculantHadamard.BinaryProductTransport

open CyclotomicRings BinaryLocalRing

/-- The actual map from local units to the fraction field of `B u`. -/
def localUnitToFraction (u : ℕ) : (O u)ˣ →* FractionRing (B u) :=
  (toFraction u).toRingHom.toMonoidHom.comp (Units.coeHom (O u))

@[simp] theorem localUnitToFraction_apply (u : ℕ) (X : (O u)ˣ) :
    localUnitToFraction u X = toFraction u (X : O u) := rfl

end CirculantHadamard.BinaryProductTransport

end

end OAI


