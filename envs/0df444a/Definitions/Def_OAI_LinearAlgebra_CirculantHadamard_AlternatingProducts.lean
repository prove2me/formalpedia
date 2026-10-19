-- Prove2me | Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_AlternatingProducts
-- name    : OAI_LinearAlgebra_CirculantHadamard_AlternatingProducts
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T08:30:16.696645+00:00
-- url     : https://prove2.me/theorems/c4c91df8-ee75-4aab-b8d7-799c0a145bb5
-- title:
--   Alternating products over the subsets of a finite set
-- statement:
--   These notions belong to a formal proof that a real circulant Hadamard matrix of positive order $n$ exists only for $n=1$ and $n=4$. Such a matrix has entries $\pm1$, satisfies $HH^{\mathsf T}=nI$, and has the form $H_{ij}=h(j-i)$ with indices in $\mathbb Z/n$. Its first row becomes an element $f$ of the integer group ring $\mathbb Z[\mathbb Z/n]$ with $f f^{*}=n$, where $f^{*}$ reverses the indices. Two-adic descent reduces every order $n>1$ to $n=4u^2$ with $u$ odd; for $u>1$, evaluation at characters with values in cyclotomic rings and a local argument at a prime above $2$ give a contradiction.
--
--   Let $t$ be a finite set and $x$ a family indexed by subsets of $t$.
--
--   1. **Subset sign.** $\varepsilon(S)=(-1)^{|S|}$, with $\varepsilon(\varnothing)=1$.
--   2. **Even and odd products.** In a commutative monoid, the products of $x(S)$ over subsets $S\subseteq t$ of even, respectively odd, cardinality; they serve as numerator and denominator before any inverse is introduced.
--   3. **Alternating product.** In a division commutative monoid,
--   $$
--   \mathrm{Alt}_t(x)=\prod_{S\subseteq t}x(S)^{(-1)^{|S|}}.
--   $$
--   For $t=\varnothing$ it is $x(\varnothing)$, and it is $1$ for the constant family $1$. Pairing $S$ with $S\cup\{p\}$ writes it as a product of quotients $x(S)/x(S\cup\{p\})$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/LinearAlgebra/CirculantHadamard/AlternatingProducts.lean

-- Generated from openai/math@1581d4c lean/OAI/LinearAlgebra/CirculantHadamard/AlternatingProducts.lean by skeleton subtraction
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

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe uI uG uH

/-!
# Alternating products over literal finite subsets

The exponent is `(-1)^card S`. Pairing subsets along `p` follows from the
powerset decomposition, with the quotient orientation `x S / x (insert p S)`.

The definition and pairing are valid in a division commutative monoid, so they
apply both to actual field values and to units. Cancellation of a constant
family is stated in a commutative group. No local comparison, nonvanishing,
integrality, or torsion statement is assumed or inferred.
-/

namespace CirculantHadamard

open scoped BigOperators

variable {I : Type uI}

def subsetSign (S : Finset I) : ℤ := (-1) ^ S.card

@[simp] theorem subsetSign_empty : subsetSign (∅ : Finset I) = 1 := by
  simp [subsetSign]

/-- Numerator before introducing any inverse, available in a coefficient ring. -/
def evenSubsetProduct {G : Type uG} [CommMonoid G] (t : Finset I)
    (x : Finset I → G) : G :=
  ∏ S ∈ t.powerset.filter (fun S => Even S.card), x S

/-- Denominator before introducing any inverse, available in a coefficient ring. -/
def oddSubsetProduct {G : Type uG} [CommMonoid G] (t : Finset I)
    (x : Finset I → G) : G :=
  ∏ S ∈ t.powerset.filter (fun S => Odd S.card), x S

section DivisionCommMonoid

variable {G : Type uG} [DivisionCommMonoid G]

/-- The alternating product of the actual family indexed by subsets of `t`. -/
def alternatingProduct (t : Finset I) (x : Finset I → G) : G :=
  ∏ S ∈ t.powerset, (x S) ^ subsetSign S

@[simp] theorem alternatingProduct_empty (x : Finset I → G) :
    alternatingProduct ∅ x = x ∅ := by
  simp [alternatingProduct]

@[simp] theorem alternatingProduct_one (t : Finset I) :
    alternatingProduct t (fun _ => (1 : G)) = 1 := by
  simp [alternatingProduct]

end DivisionCommMonoid

section CommGroup

variable {G : Type uG} {H : Type uH} [CommGroup G] [DivisionCommMonoid H]

end CommGroup

section FiniteUniverse

variable [Fintype I] {G : Type uG} [DivisionCommMonoid G]

end FiniteUniverse

end CirculantHadamard

end OAI


