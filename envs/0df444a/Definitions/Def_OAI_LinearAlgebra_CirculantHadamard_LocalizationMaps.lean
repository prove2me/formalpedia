-- Prove2me | Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_LocalizationMaps
-- name    : OAI_LinearAlgebra_CirculantHadamard_LocalizationMaps
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T08:25:31.354995+00:00
-- url     : https://prove2.me/theorems/a1f9fd3f-3078-4f57-85bc-9fcafe0cdc82
-- title:
--   Localization along a contracted prime and maximal ideals over primes
-- statement:
--   These notions belong to a formal proof that a real circulant Hadamard matrix of positive order $n$ exists only for $n=1$ and $n=4$. Such a matrix has entries $\pm1$, satisfies $HH^{\mathsf T}=nI$, and has the form $H_{ij}=h(j-i)$ with indices in $\mathbb Z/n$. Its first row becomes an element $f$ of the integer group ring $\mathbb Z[\mathbb Z/n]$ with $f f^{*}=n$, where $f^{*}$ reverses the indices. Two-adic descent reduces every order $n>1$ to $n=4u^2$ with $u$ odd; for $u>1$, evaluation at characters with values in cyclotomic rings and a local argument at a prime above $2$ give a contradiction.
--
--   1. **Localization map.** For a ring homomorphism $f:A\to B$ and a prime ideal $\mathfrak m$ of $B$, the local homomorphism
--   $$
--   A_{f^{-1}(\mathfrak m)}\longrightarrow B_{\mathfrak m}
--   $$
--   induced by $f$; it agrees with $f$ on elements of $A$. No integrality is needed for this map.
--   2. **Maximal ideals over a prime.** If $B$ is an integral $\mathbb Z$-algebra with injective structure map (for instance of characteristic zero) and $p$ is a prime, there is a maximal ideal $\mathfrak m$ of $B$ with $\mathfrak m\cap\mathbb Z=(p)$ and $p\in\mathfrak m$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/LinearAlgebra/CirculantHadamard/LocalizationMaps.lean

-- Generated from openai/math@1581d4c lean/OAI/LinearAlgebra/CirculantHadamard/LocalizationMaps.lean by skeleton subtraction
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

namespace OAI

universe uA uB

/-!
# Maps between coefficient localizations and maximal ideals over primes

The localization map uses the actual contraction of the target prime ideal.
Its denominator condition follows from the definition of contraction; no
integrality is needed for this map. Integrality is used separately to prove
maximality of contractions and existence of maximal ideals over rational primes.
-/

namespace CirculantHadamard

section LocalizationMap

variable {A : Type uA} {B : Type uB} [CommRing A] [CommRing B]

/-- The actual map from the localization at a contracted prime ideal. -/
noncomputable def localizationAtComapMap (f : A →+* B) (m : Ideal B) [m.IsPrime] :
    Localization.AtPrime (m.comap f) →+* Localization.AtPrime m :=
  Localization.localRingHom (m.comap f) m f rfl

/-- The induced map agrees with the original ring map on coefficients. -/
@[simp] theorem localizationAtComapMap_algebraMap (f : A →+* B)
    (m : Ideal B) [m.IsPrime] (a : A) :
    localizationAtComapMap f m (algebraMap A (Localization.AtPrime (m.comap f)) a) =
      algebraMap B (Localization.AtPrime m) (f a) :=
  Localization.localRingHom_to_map (m.comap f) m f rfl a

end LocalizationMap

/-- Every rational prime has a maximal ideal above it in an integral
integer algebra with injective integer map. The conclusion retains the exact
contraction as well as membership of the prime in the maximal ideal. -/
theorem exists_maximal_ideal_over_nat_prime (B : Type uB) [CommRing B]
    [Algebra ℤ B] [Algebra.IsIntegral ℤ B]
    (hB : Function.Injective (algebraMap ℤ B)) {p : ℕ} (hp : p.Prime) :
    ∃ m : Ideal B, m.IsMaximal ∧
      m.comap (algebraMap ℤ B) = Ideal.span ({(p : ℤ)} : Set ℤ) ∧ (p : B) ∈ m := by
  let P : Ideal ℤ := Ideal.span ({(p : ℤ)} : Set ℤ)
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  let : P.IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible hpZ.irreducible
  have hker : RingHom.ker (algebraMap ℤ B) = ⊥ :=
    (RingHom.injective_iff_ker_eq_bot _).mp hB
  obtain ⟨m, hm, hcomap⟩ :=
    Ideal.exists_ideal_over_maximal_of_isIntegral (S := B) P
      (by rw [hker]; exact bot_le)
  refine ⟨m, hm, hcomap, ?_⟩
  have hpP : (p : ℤ) ∈ P := Ideal.subset_span (Set.mem_singleton _)
  have hpcomap : (p : ℤ) ∈ m.comap (algebraMap ℤ B) := by
    rwa [hcomap]
  have hpm := Ideal.mem_comap.mp hpcomap
  simpa only [map_natCast] using hpm

/-- Characteristic zero supplies the injective integer map automatically. -/
theorem exists_maximal_ideal_over_nat_prime_of_charZero (B : Type uB) [CommRing B]
    [CharZero B] [Algebra ℤ B] [Algebra.IsIntegral ℤ B] {p : ℕ} (hp : p.Prime) :
    ∃ m : Ideal B, m.IsMaximal ∧
      m.comap (algebraMap ℤ B) = Ideal.span ({(p : ℤ)} : Set ℤ) ∧ (p : B) ∈ m :=
  exists_maximal_ideal_over_nat_prime B (algebraMap ℤ B).injective_int hp

end CirculantHadamard

end OAI


