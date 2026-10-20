-- Prove2me | Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_CyclicEvaluationAt__EvenBarker
-- name    : OAI_LinearAlgebra_CirculantHadamard_CyclicEvaluationAt__EvenBarker
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T15:03:18.692361+00:00
-- url     : https://prove2.me/theorems/61c31146-2e9b-4fb7-9d93-8b256e1e54c9
-- title:
--   Evaluating the cyclic group algebra at a root of unity
-- statement:
--   These notions belong to a formal proof that a real circulant Hadamard matrix of positive order $n$ exists only for $n=1$ and $n=4$. Such a matrix has entries $\pm1$, satisfies $HH^{\mathsf T}=nI$, and has the form $H_{ij}=h(j-i)$ with indices in $\mathbb Z/n$. Its first row becomes an element $f$ of the integer group ring $\mathbb Z[\mathbb Z/n]$ with $f f^{*}=n$, where $f^{*}$ reverses the indices. Two-adic descent reduces every order $n>1$ to $n=4u^2$ with $u$ odd; for $u>1$, evaluation at characters with values in cyclotomic rings and a local argument at a prime above $2$ give a contradiction. Write $R[\mathbb Z/n]$ for the cyclic group ring (finitely supported coefficient functions on $\mathbb Z/n$ with convolution), $e_a$ for its basis element at $a$, and $f^{*}(a)=\overline{f(-a)}$ for its involution, which reverses indices and applies the coefficient star.
--
--   1. **Evaluation at a root.** For commutative $A$-algebras $S$, $n>0$ and $x\in S$ with $x^n=1$, the $A$-algebra homomorphism $\mathrm{ev}_x:A[\mathbb Z/n]\to S$ obtained from $A[\mathbb Z/n]\cong A[X]/(X^n-1)$ and $X\mapsto x$, so that
--   $$
--   \mathrm{ev}_x(f)=\sum_{a\in\mathbb Z/n}f(a)\,x^{a}.
--   $$
--   It sends $e_1$ to $x$ and a polynomial in $e_1$ to the same polynomial in $x$. It coincides with character evaluation at the power character $a\mapsto x^a$, and $\mathrm{ev}_1$ is the augmentation.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/LinearAlgebra/CirculantHadamard/CyclicEvaluationAt.lean

-- Generated from openai/math@1581d4c lean/OAI/LinearAlgebra/CirculantHadamard/CyclicEvaluationAt.lean by skeleton subtraction
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

namespace OAI

universe uA uS uT

/-!
# Evaluation at an actual root of unity

The algebra map factors through the proved polynomial presentation of the
cyclic group ring and the universal property of `AdjoinRoot (X ^ n - 1)`.
-/

noncomputable section

namespace CirculantHadamard.CyclicRing

open Polynomial
open scoped BigOperators

variable {A : Type uA} {S : Type uS} {T : Type uT} [CommRing A] [CommRing S] [CommRing T]
variable [Algebra A S] [Algebra A T]

/-- Evaluate the polynomial quotient at a proved `n`th root of unity. -/
def evaluateAt (n : ℕ) [NeZero n] (x : S) (hx : x ^ n = 1) : Elem A n →ₐ[A] S :=
  (AdjoinRoot.liftAlgHom (CyclicPolynomial.relation A n) (Algebra.ofId A S) x
    (by simp [CyclicPolynomial.relation, hx])).comp
      (CyclicPolynomial.cyclicEquiv A n).toAlgHom

@[simp] theorem evaluateAt_single (n : ℕ) [NeZero n] (x : S) (hx : x ^ n = 1)
    (a : ZMod n) (r : A) :
    evaluateAt n x hx (AddMonoidAlgebra.single a r) = algebraMap A S r * x ^ a.val := by
  change (AdjoinRoot.liftAlgHom (CyclicPolynomial.relation A n) (Algebra.ofId A S) x
    (by simp [CyclicPolynomial.relation, hx]))
      (CyclicPolynomial.cyclicEquiv A n (AddMonoidAlgebra.single a r)) = _
  rw [CyclicPolynomial.cyclicEquiv_single, map_mul, map_pow, AlgHom.commutes,
    AdjoinRoot.liftAlgHom_root (CyclicPolynomial.relation A n) (Algebra.ofId A S) x
      (by simp [CyclicPolynomial.relation, hx])]

@[simp] theorem evaluateAt_scalar (n : ℕ) [NeZero n] (x : S) (hx : x ^ n = 1)
    (r : A) : evaluateAt n x hx (scalar n r) = algebraMap A S r := by
  simp [scalar]

@[simp] theorem evaluateAt_generator (n : ℕ) [NeZero n] (x : S) (hx : x ^ n = 1) :
    evaluateAt (A := A) n x hx (CyclicPolynomial.generator A n) = x := by
  change (AdjoinRoot.liftAlgHom (CyclicPolynomial.relation A n) (Algebra.ofId A S) x
    (by simp [CyclicPolynomial.relation, hx]))
      (CyclicPolynomial.cyclicEquiv A n (CyclicPolynomial.generator A n)) = x
  rw [CyclicPolynomial.cyclicEquiv_generator]
  exact AdjoinRoot.liftAlgHom_root (CyclicPolynomial.relation A n) (Algebra.ofId A S) x
    (by simp [CyclicPolynomial.relation, hx])

/-- Evaluation agrees with evaluation of every polynomial in the cyclic generator. -/
@[simp] theorem evaluateAt_aeval (n : ℕ) [NeZero n] (x : S) (hx : x ^ n = 1)
    (p : A[X]) :
    evaluateAt n x hx (aeval (CyclicPolynomial.generator A n) p) = aeval x p := by
  change (AdjoinRoot.liftAlgHom (CyclicPolynomial.relation A n) (Algebra.ofId A S) x
    (by simp [CyclicPolynomial.relation, hx]))
      (CyclicPolynomial.cyclicEquiv A n (aeval (CyclicPolynomial.generator A n) p)) = _
  rw [CyclicPolynomial.cyclicEquiv_aeval]
  exact AdjoinRoot.liftAlgHom_mk (CyclicPolynomial.relation A n) (Algebra.ofId A S) x
    (by simp [CyclicPolynomial.relation, hx]) p

/-- The quotient construction and the finite-character construction are the same
ring homomorphism. -/
theorem evaluateAt_eq_evaluate (n : ℕ) [NeZero n] (x : S) (hx : x ^ n = 1) :
    (evaluateAt (A := A) n x hx).toRingHom =
      evaluate (algebraMap A S) (CyclicPolynomial.powerCharacter n x hx) := by
  apply AddMonoidAlgebra.ringHom_ext
  · intro r
    simp [evaluateAt_single]
  · intro a
    simp [evaluateAt_single, CyclicPolynomial.powerCharacter_apply]

theorem evaluateAt_apply (n : ℕ) [NeZero n] (x : S) (hx : x ^ n = 1)
    (f : Elem A n) :
    evaluateAt n x hx f = ∑ a : ZMod n, algebraMap A S (f.coeff a) * x ^ a.val := by
  change (evaluateAt n x hx).toRingHom f = _
  rw [evaluateAt_eq_evaluate, evaluate_apply]
  rfl

/-- Evaluation at one is the actual augmentation followed by the coefficient map. -/
@[simp] theorem evaluateAt_one (n : ℕ) [NeZero n] (f : Elem A n) :
    evaluateAt n (1 : S) (one_pow n) f = algebraMap A S (augmentation n f) := by
  simp [evaluateAt_apply, augmentation_apply, map_sum]

end CirculantHadamard.CyclicRing

end

end OAI


