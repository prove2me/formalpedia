-- Prove2me | Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_CyclotomicProjection__EvenBarker
-- name    : OAI_LinearAlgebra_CirculantHadamard_CyclotomicProjection__EvenBarker
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T15:04:36.313294+00:00
-- url     : https://prove2.me/theorems/a552039f-3cce-42f8-9e1b-950e33b6185b
-- title:
--   Evaluation of a cyclic group algebra in its cyclotomic quotient
-- statement:
--   These notions belong to a formal proof that a real circulant Hadamard matrix of positive order $n$ exists only for $n=1$ and $n=4$. Such a matrix has entries $\pm1$, satisfies $HH^{\mathsf T}=nI$, and has the form $H_{ij}=h(j-i)$ with indices in $\mathbb Z/n$. Its first row becomes an element $f$ of the integer group ring $\mathbb Z[\mathbb Z/n]$ with $f f^{*}=n$, where $f^{*}$ reverses the indices. Two-adic descent reduces every order $n>1$ to $n=4u^2$ with $u$ odd; for $u>1$, evaluation at characters with values in cyclotomic rings and a local argument at a prime above $2$ give a contradiction. Write $R[\mathbb Z/n]$ for the cyclic group ring (finitely supported coefficient functions on $\mathbb Z/n$ with convolution), $e_a$ for its basis element at $a$, and $f^{*}(a)=\overline{f(-a)}$ for its involution, which reverses indices and applies the coefficient star.
--
--   1. **Root relation.** In $R[X]/(\Phi_n(X))$ the class $\zeta$ of $X$ satisfies $\zeta^n=1$, because $\Phi_n$ divides $X^n-1$.
--   2. **Cyclotomic evaluation.** For $n>0$, the $R$-algebra homomorphism
--   $$
--   R[\mathbb Z/n]\longrightarrow R[X]/(\Phi_n(X)),\qquad e_1\mapsto\zeta,
--   $$
--   evaluation at $\zeta$, which sends a polynomial $P(e_1)$ to the class of $P$. At an element of order dividing $p^e$, $\Phi_{p^{e+1}}$ evaluates to $p$, which turns divisibility of a monic remainder by $p$ into divisibility of a projection by $p$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/LinearAlgebra/CirculantHadamard/CyclotomicProjection.lean

-- Generated from openai/math@1581d4c lean/OAI/LinearAlgebra/CirculantHadamard/CyclotomicProjection.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the EvenBarker mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_EvenBarker
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_Model
import Definitions.Def_OAI_LinearAlgebra_Barker_Model
import Definitions.Def_OAI_LinearAlgebra_Barker_PeriodicModFour
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_Basic__EvenBarker
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_Witnesses__EvenBarker
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_MatrixBridge__EvenBarker
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_CyclicRing__EvenBarker
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_CyclicNorm__EvenBarker
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_CyclicProjection__EvenBarker
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_LocalDVR__EvenBarker
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_IntegerTwoLocal__EvenBarker
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_CyclicEvaluation__EvenBarker
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_CyclicPolynomial__EvenBarker
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_RamifiedConjugation__EvenBarker
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_CyclotomicIntegerEvaluation__EvenBarker
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_DyadicRemainder__EvenBarker
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_RamifiedEisenstein__EvenBarker
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_RamifiedLocal__EvenBarker
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_OrderHalving__EvenBarker
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_BinaryBlocks__EvenBarker
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_BinaryCoefficients__EvenBarker
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_CyclotomicRings__EvenBarker
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_PrimeComponents__EvenBarker
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_PrimeCharacterEvaluations__EvenBarker
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_BinaryEvaluation__EvenBarker
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_LocalizationMaps__EvenBarker
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_BinaryLocalization__EvenBarker
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_BinaryLocalRing__EvenBarker
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_AlternatingProducts__EvenBarker
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_BinaryProductTransport__EvenBarker
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_FirstOrderResidue__EvenBarker
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_BinaryResidue__EvenBarker
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_BinaryLocalFamily__EvenBarker
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_ResidueOneAssociation__EvenBarker
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_CyclotomicLocalBase__EvenBarker
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_CyclotomicAwayLocal__EvenBarker
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_CyclicProjectionPolynomial__EvenBarker
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_CyclicEvaluationAt__EvenBarker

namespace OAI

universe uR uS

/-!
# Integral division after projection to a smaller cyclic group

At an element of order dividing `p ^ e`, the prime-power cyclotomic polynomial
`cyclotomic (p ^ (e + 1)) R` evaluates to the scalar `p`. Consequently, if all
coefficients of a polynomial's monic remainder are divisible by `p`, its image
in the group algebra of `ZMod (p ^ e)` is divisible by the same scalar.

All divisions are witnessed inside the coefficient ring or group algebra.
No domain instance or cancellation assumption on a finite group algebra is used.
-/

noncomputable section

namespace CirculantHadamard

open Polynomial

variable {R : Type uR} {S : Type uS} [CommRing R] [CommRing S] [Algebra R S]

/-- The actual root in the cyclotomic quotient satisfies its `n`th-power
relation, directly because the cyclotomic polynomial divides `X ^ n - 1`. -/
theorem cyclotomicAdjoinRoot_pow (n : ℕ) :
    AdjoinRoot.root (cyclotomic n R) ^ n = 1 := by
  have h : AdjoinRoot.mk (cyclotomic n R) ((X : R[X]) ^ n - 1) = 0 :=
    AdjoinRoot.mk_eq_zero.mpr (cyclotomic.dvd_X_pow_sub_one n R)
  simpa only [map_sub, map_pow, AdjoinRoot.mk_X, map_one, sub_eq_zero] using h

/-- Evaluation of the actual cyclic group ring at the root in its cyclotomic
quotient, using the root's proved power relation. -/
def cyclicCyclotomicEvaluation (R : Type uR) [CommRing R] (n : ℕ) [NeZero n] :
    AddMonoidAlgebra R (ZMod n) →ₐ[R] AdjoinRoot (cyclotomic n R) :=
  CyclicRing.evaluateAt n (AdjoinRoot.root (cyclotomic n R))
    (cyclotomicAdjoinRoot_pow n)

@[simp]
theorem cyclicCyclotomicEvaluation_aeval (n : ℕ) [NeZero n] (P : R[X]) :
    cyclicCyclotomicEvaluation R n (aeval (CyclicPolynomial.generator R n) P) =
      AdjoinRoot.mk (cyclotomic n R) P := by
  rw [cyclicCyclotomicEvaluation, CyclicRing.evaluateAt_aeval, AdjoinRoot.aeval_eq]

end CirculantHadamard

end

end OAI


