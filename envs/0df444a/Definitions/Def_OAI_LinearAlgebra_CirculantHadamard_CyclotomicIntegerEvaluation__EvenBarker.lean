-- Prove2me | Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_CyclotomicIntegerEvaluation__EvenBarker
-- name    : OAI_LinearAlgebra_CirculantHadamard_CyclotomicIntegerEvaluation__EvenBarker
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T13:57:44.167268+00:00
-- url     : https://prove2.me/theorems/05a6d06c-7a8e-4e48-9038-ca88fa6f8843
-- title:
--   Evaluation of integer cyclic group rings in a cyclotomic quotient
-- statement:
--   These notions belong to a formal proof that a real circulant Hadamard matrix of positive order $n$ exists only for $n=1$ and $n=4$. Such a matrix has entries $\pm1$, satisfies $HH^{\mathsf T}=nI$, and has the form $H_{ij}=h(j-i)$ with indices in $\mathbb Z/n$. Its first row becomes an element $f$ of the integer group ring $\mathbb Z[\mathbb Z/n]$ with $f f^{*}=n$, where $f^{*}$ reverses the indices. Two-adic descent reduces every order $n>1$ to $n=4u^2$ with $u$ odd; for $u>1$, evaluation at characters with values in cyclotomic rings and a local argument at a prime above $2$ give a contradiction. Write $R[\mathbb Z/n]$ for the cyclic group ring (finitely supported coefficient functions on $\mathbb Z/n$ with convolution), $e_a$ for its basis element at $a$, and $f^{*}(a)=\overline{f(-a)}$ for its involution, which reverses indices and applies the coefficient star.
--
--   1. **Integer cyclotomic evaluation.** For a commutative ring $A$ and $n>0$, the ring homomorphism $\mathbb Z[\mathbb Z/n]\to A[X]/(\Phi_n(X))$ obtained by casting integer coefficients and sending $e_a$ to $\zeta^{a}$, where $\zeta$ is the class of $X$:
--   $$
--   f\longmapsto\sum_{a\in\mathbb Z/n}f(a)\,\zeta^{a}.
--   $$
--   It sends an integer scalar to its image. When the quotient is a domain of characteristic zero, the root-inverting conjugation carries this evaluation to the evaluation of $f^{*}$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/LinearAlgebra/CirculantHadamard/CyclotomicIntegerEvaluation.lean

-- Generated from openai/math@1581d4c lean/OAI/LinearAlgebra/CirculantHadamard/CyclotomicIntegerEvaluation.lean by skeleton subtraction
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

namespace OAI

universe uA

/-!
# Integer cyclic evaluation and actual cyclotomic conjugation

The coefficient map is the integer cast into the cyclotomic quotient. The
character sends the cyclic generator to its adjoined root. The root-inverting
automorphism therefore carries evaluation to evaluation of the actual cyclic
group-ring involution.
-/

noncomputable section

namespace CirculantHadamard

open Polynomial
open scoped BigOperators

variable (A : Type uA) [CommRing A] (n : ℕ) [NeZero n]

/-- Integer cyclic group-ring evaluation in the actual cyclotomic quotient. -/
def integerCyclotomicEvaluation :
    CyclicRing.Elem ℤ n →+* AdjoinRoot (cyclotomic n A) :=
  CyclicRing.evaluate (Int.castRingHom (AdjoinRoot (cyclotomic n A)))
    (CyclicPolynomial.powerCharacter n (AdjoinRoot.root (cyclotomic n A))
      (RamifiedConjugation.root_pow_order A n))

@[simp] theorem integerCyclotomicEvaluation_scalar (a : ℤ) :
    integerCyclotomicEvaluation A n (CyclicRing.scalar n a) =
      (a : AdjoinRoot (cyclotomic n A)) :=
  CyclicRing.evaluate_scalar _ _ a

variable (hn : 0 < n)
variable [IsDomain (AdjoinRoot (cyclotomic n A))]
variable [CharZero (AdjoinRoot (cyclotomic n A))]

end CirculantHadamard

end

end OAI


