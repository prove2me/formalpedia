-- Prove2me | Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_LocalComparison__EvenBarker
-- name    : OAI_LinearAlgebra_CirculantHadamard_LocalComparison__EvenBarker
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T15:06:50.06315+00:00
-- url     : https://prove2.me/theorems/0b51f863-c9d5-44f3-8df9-34d6f25824d7
-- title:
--   Order-p evaluation and the comparison relation
-- statement:
--   These notions belong to a formal proof that a real circulant Hadamard matrix of positive order $n$ exists only for $n=1$ and $n=4$. Such a matrix has entries $\pm1$, satisfies $HH^{\mathsf T}=nI$, and has the form $H_{ij}=h(j-i)$ with indices in $\mathbb Z/n$. Its first row becomes an element $f$ of the integer group ring $\mathbb Z[\mathbb Z/n]$ with $f f^{*}=n$, where $f^{*}$ reverses the indices. Two-adic descent reduces every order $n>1$ to $n=4u^2$ with $u$ odd; for $u>1$, evaluation at characters with values in cyclotomic rings and a local argument at a prime above $2$ give a contradiction. Write $R[\mathbb Z/n]$ for the cyclic group ring (finitely supported coefficient functions on $\mathbb Z/n$ with convolution), $e_a$ for its basis element at $a$, and $f^{*}(a)=\overline{f(-a)}$ for its involution, which reverses indices and applies the coefficient star.
--
--   Let $A$ be a commutative ring and $p$ a prime, and let $E=A[X]/(\Phi_p(X))$ with root $\zeta$ and $\pi=\zeta-1$.
--
--   1. **Order-$p$ root.** $\zeta\in E$, with $\zeta^p=1$ and hence $\zeta^{p^{e+1}}=1$.
--   2. **Order-$p$ value.** For $F\in A[\mathbb Z/p^{e+1}]$, the evaluation $F(\zeta)\in E$ of the cyclic group algebra at $\zeta$; it fixes scalars.
--   3. **Compared.** $F$ is compared if its order-$p$ value equals a unit with residue one times its augmentation:
--   $$
--   F(\zeta)=w\cdot\varepsilon(F)\quad\text{with }w\in E^{\times},\ w-1\in(\pi).
--   $$
--   For a characteristic-zero DVR $A$ with maximal ideal $(p)$, this is the conclusion of the local comparison induction.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/LinearAlgebra/CirculantHadamard/LocalComparison.lean

-- Generated from openai/math@1581d4c lean/OAI/LinearAlgebra/CirculantHadamard/LocalComparison.lean by skeleton subtraction
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
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_CyclotomicProjection__EvenBarker

namespace OAI

universe uA

/-!
# Local character comparison in the actual cyclotomic quotient

Starting with a characteristic-zero DVR whose maximal ideal is generated by
the rational prime `p`, all ramified rings needed by the induction are
constructed as the actual cyclotomic quotients. No projection-divisibility,
comparison, or existence-of-valuation premise is taken from the caller.

The conclusion uses membership in the ideal generated by `root - 1` to state
residue one. This is independent of how a local-ring instance is installed and
can be transported directly to a later localization.
-/

noncomputable section

namespace CirculantHadamard.LocalComparison

open CyclicRing Polynomial

variable (A : Type uA) [CommRing A]

/-- The fixed primitive-order-`p` root used at every induction level. -/
def orderPRoot (p : ℕ) : RamifiedLocal.Extension A p 0 :=
  AdjoinRoot.root (cyclotomic (p ^ (0 + 1)) A)

theorem orderPRoot_pow (p : ℕ) : orderPRoot A p ^ p = 1 := by
  calc
    orderPRoot A p ^ p = orderPRoot A p ^ (p ^ (0 + 1)) :=
      congrArg (fun n : ℕ => orderPRoot A p ^ n) (by simp)
    _ = 1 := cyclotomicAdjoinRoot_pow (R := A) (p ^ (0 + 1))

theorem orderPRoot_pow_level (p e : ℕ) : orderPRoot A p ^ (p ^ (e + 1)) = 1 := by
  calc
    orderPRoot A p ^ (p ^ (e + 1)) = orderPRoot A p ^ (p * p ^ e) :=
      congrArg (fun n : ℕ => orderPRoot A p ^ n) (pow_succ' p e)
    _ = (orderPRoot A p ^ p) ^ (p ^ e) := pow_mul _ _ _
    _ = 1 := by rw [orderPRoot_pow, one_pow]

/-- Actual order-`p` evaluation of an element of the cyclic group ring of
order `p ^ (e + 1)`. -/
def orderPValue (p e : ℕ) [NeZero p] :
    Elem A (p ^ (e + 1)) →ₐ[A] RamifiedLocal.Extension A p 0 :=
  evaluateAt (p ^ (e + 1)) (orderPRoot A p) (orderPRoot_pow_level A p e)

@[simp] theorem orderPValue_scalar (p e : ℕ) [NeZero p] (a : A) :
    orderPValue A p e (scalar (p ^ (e + 1)) a) =
      algebraMap A (RamifiedLocal.Extension A p 0) a :=
  (orderPValue A p e).commutes a

/-- The conclusion of comparison, expressed by an actual unit and membership
in the actual ramified maximal ideal. -/
def OrderPCompared (p e : ℕ) [NeZero p] (F : Elem A (p ^ (e + 1))) : Prop :=
  ∃ u : (RamifiedLocal.Extension A p 0)ˣ,
    orderPValue A p e F = (u : RamifiedLocal.Extension A p 0) *
      algebraMap A (RamifiedLocal.Extension A p 0) (augmentation (p ^ (e + 1)) F) ∧
    (u : RamifiedLocal.Extension A p 0) - 1 ∈
      Ideal.span {RamifiedLocal.uniformizer A p 0}

section DVR

variable [IsDomain A] [CharZero A] [IsDiscreteValuationRing A]

end DVR

end CirculantHadamard.LocalComparison

end

end OAI


