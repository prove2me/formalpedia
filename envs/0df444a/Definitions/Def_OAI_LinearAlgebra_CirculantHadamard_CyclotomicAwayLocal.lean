-- Prove2me | Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_CyclotomicAwayLocal
-- name    : OAI_LinearAlgebra_CirculantHadamard_CyclotomicAwayLocal
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T08:43:34.815391+00:00
-- url     : https://prove2.me/theorems/4a013277-7430-4c7b-b688-6d2e10979221
-- title:
--   Localizing the away coefficient ring at a contracted prime
-- statement:
--   These notions belong to a formal proof that a real circulant Hadamard matrix of positive order $n$ exists only for $n=1$ and $n=4$. Such a matrix has entries $\pm1$, satisfies $HH^{\mathsf T}=nI$, and has the form $H_{ij}=h(j-i)$ with indices in $\mathbb Z/n$. Its first row becomes an element $f$ of the integer group ring $\mathbb Z[\mathbb Z/n]$ with $f f^{*}=n$, where $f^{*}$ reverses the indices. Two-adic descent reduces every order $n>1$ to $n=4u^2$ with $u$ odd; for $u>1$, evaluation at characters with values in cyclotomic rings and a local argument at a prime above $2$ give a contradiction.
--
--   Fix $u$, a prime $p\mid u$, and a prime ideal $\mathfrak m$ of $B_u=\mathbb Z[i,\rho_q:q\mid u]$.
--
--   1. **Away prime.** The contraction $\mathfrak m\cap B_{u,\hat p}$ of $\mathfrak m$ to the away ring $B_{u,\hat p}$, which omits $\rho_p$.
--   2. **Away localization.** The localization
--   $$
--   \bigl(B_{u,\hat p}\bigr)_{\mathfrak m\cap B_{u,\hat p}},
--   $$
--   an algebra over $B_{u,\hat p}$ that has characteristic zero and is Noetherian, since $B_{u,\hat p}$ is a finitely generated $\mathbb Z$-module. When $\mathfrak m$ is maximal, integrality makes the contraction maximal, and the single-generator description identifies this ring with an unramified cyclotomic localization.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/LinearAlgebra/CirculantHadamard/CyclotomicAwayLocal.lean

-- Generated from openai/math@1581d4c lean/OAI/LinearAlgebra/CirculantHadamard/CyclotomicAwayLocal.lean by skeleton subtraction
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
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_BinaryProductTransport
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_FirstOrderResidue
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_BinaryResidue
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_BinaryLocalFamily
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_ResidueOneAssociation
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_CyclotomicLocalBase

namespace OAI

universe uR uS

/-!
# The actual away coefficient localization

The prime ideal is the contraction of a maximal ideal of the actual global
root ring. Its maximality follows from integrality of the coefficient
inclusion, and the single-generator theorem identifies its localization
with the unramified cyclotomic construction.
-/

noncomputable section

namespace CirculantHadamard.CyclotomicAwayLocal

open CyclotomicRings IsLocalRing

/-- The actual prime ideal on the coefficient ring with one direction omitted. -/
abbrev awayPrime (u p : ℕ) (m : Ideal (B u)) : Ideal (awayRing u p) :=
  m.comap (awayInclusion u p).toRingHom

/-- The coefficient localization used in the prime-direction comparison. -/
abbrev AwayLocal (u p : ℕ) (m : Ideal (B u)) [m.IsPrime] :=
  Localization.AtPrime (awayPrime u p m)

instance awayLocal_algebra (u p : ℕ) (m : Ideal (B u)) [m.IsPrime] :
    Algebra (awayRing u p) (AwayLocal u p m) :=
  OreLocalization.instAlgebra (R := awayRing u p) (R₀ := awayRing u p)
    (S := (awayPrime u p m).primeCompl)

instance awayLocal_charZero (u p : ℕ) (m : Ideal (B u)) [m.IsPrime] :
    CharZero (AwayLocal u p m) :=
  charZero_of_injective_algebraMap
    (IsLocalization.injective (AwayLocal u p m)
      (awayPrime u p m).primeCompl_le_nonZeroDivisors)

instance awayLocal_noetherian (u p : ℕ) (m : Ideal (B u)) [m.IsPrime] :
    IsNoetherianRing (AwayLocal u p m) :=
  IsLocalization.isNoetherianRing (awayPrime u p m).primeCompl (AwayLocal u p m)
    (IsNoetherianRing.of_finite ℤ (awayRing u p))

end CirculantHadamard.CyclotomicAwayLocal

end

end OAI


