-- Prove2me | Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_PrimeComponents
-- name    : OAI_LinearAlgebra_CirculantHadamard_PrimeComponents
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T08:17:49.017495+00:00
-- url     : https://prove2.me/theorems/7977e99a-3413-4311-b8f8-783f8220d739
-- title:
--   Primary components of the cyclic group of order u squared
-- statement:
--   These notions belong to a formal proof that a real circulant Hadamard matrix of positive order $n$ exists only for $n=1$ and $n=4$. Such a matrix has entries $\pm1$, satisfies $HH^{\mathsf T}=nI$, and has the form $H_{ij}=h(j-i)$ with indices in $\mathbb Z/n$. Its first row becomes an element $f$ of the integer group ring $\mathbb Z[\mathbb Z/n]$ with $f f^{*}=n$, where $f^{*}$ reverses the indices. Two-adic descent reduces every order $n>1$ to $n=4u^2$ with $u$ odd; for $u>1$, evaluation at characters with values in cyclotomic rings and a local argument at a prime above $2$ give a contradiction.
--
--   Fix $u>0$.
--
--   1. **Prime index set.** The finite set of primes dividing $u$.
--   2. **Component orders.** For such $p$, the exponent $e_p$ of $p$ in $u^2$ and the order $p^{e_p}$; these are positive, pairwise coprime, and multiply to $u^2$.
--   3. **Primary decomposition.** The Chinese remainder ring isomorphism
--   $$
--   \mathbb Z/u^2\;\cong\;\prod_{p\mid u}\mathbb Z/p^{e_p},
--   $$
--   with coordinates the reductions, and its additive version.
--   4. **Primary generators.** For each $p$, the element of $\mathbb Z/u^2$ whose $p$-coordinate is $1$ and whose other coordinates are $0$. The cofactor $u^2/p^{e_p}$ is prime to $p$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/LinearAlgebra/CirculantHadamard/PrimeComponents.lean

-- Generated from openai/math@1581d4c lean/OAI/LinearAlgebra/CirculantHadamard/PrimeComponents.lean by skeleton subtraction
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

namespace OAI

/-!
# Actual primary components of the cyclic group of order u²

The prime set is the literal finite set of prime factors of `u`. The exponent
of each component is `(u ^ 2).factorization p`, hence twice the exponent in u.
Factorization and coprimality supply the hypotheses of the finite Chinese
remainder theorem. Its coordinates are the canonical reduction maps.

The generator of each primary component is the inverse image of its unit
coordinate vector. Its additive order is proved to be the full prime power,
and the complementary integer factor of u² is proved prime to p.
-/

noncomputable section

namespace CirculantHadamard.PrimeComponents

open scoped BigOperators

def primes (u : ℕ) : Finset ℕ := u.primeFactors

abbrev PrimeIndex (u : ℕ) := {p : ℕ // p ∈ primes u}

def exponent (u p : ℕ) : ℕ := (u ^ 2).factorization p

def order (u p : ℕ) : ℕ := p ^ exponent u p

abbrev Component (u : ℕ) (p : PrimeIndex u) := ZMod (order u p.val)

abbrev PrimaryProduct (u : ℕ) := (p : PrimeIndex u) → Component u p

theorem mem_primes {u p : ℕ} : p ∈ primes u ↔ p.Prime ∧ p ∣ u ∧ u ≠ 0 :=
  Nat.mem_primeFactors

theorem prime_of_mem {u p : ℕ} (hp : p ∈ primes u) : p.Prime :=
  (mem_primes.mp hp).1

theorem dvd_of_mem {u p : ℕ} (hp : p ∈ primes u) : p ∣ u :=
  (mem_primes.mp hp).2.1

theorem exponent_pos {u p : ℕ} (hu : 0 < u) (hp : p ∈ primes u) :
    0 < exponent u p := by
  apply (prime_of_mem hp).factorization_pos_of_dvd (pow_ne_zero 2 hu.ne')
  exact (dvd_of_mem hp).trans (dvd_pow_self u (by decide : 2 ≠ 0))

theorem order_pos {u p : ℕ} (hp : p ∈ primes u) : 0 < order u p :=
  pow_pos (prime_of_mem hp).pos _

instance componentOrder_neZero (u : ℕ) (p : PrimeIndex u) : NeZero (order u p.val) :=
  ⟨(order_pos p.property).ne'⟩

theorem prime_dvd_order {u p : ℕ} (hu : 0 < u) (hp : p ∈ primes u) :
    p ∣ order u p := dvd_pow_self p (exponent_pos hu hp).ne'

def cofactor (u p : ℕ) : ℕ := u ^ 2 / order u p

theorem prod_order_finset (u : ℕ) (hu : 0 < u) :
    (∏ p ∈ primes u, order u p) = u ^ 2 := by
  have h := Nat.prod_factorization_pow_eq_self (pow_ne_zero 2 hu.ne')
  simpa only [Nat.prod_factorization_eq_prod_primeFactors,
    Nat.primeFactors_pow u (by decide : 2 ≠ 0), primes, order, exponent] using h

theorem prod_order (u : ℕ) (hu : 0 < u) :
    (∏ p : PrimeIndex u, order u p.val) = u ^ 2 := by
  change (∏ p : (primes u), order u p.val) = u ^ 2
  rw [Finset.prod_coe_sort]
  exact prod_order_finset u hu

theorem pairwise_coprime (u : ℕ) :
    Pairwise (fun p q : PrimeIndex u => Nat.Coprime (order u p.val) (order u q.val)) := by
  intro p q hpq
  exact Nat.coprime_pow_primes _ _ (prime_of_mem p.property) (prime_of_mem q.property)
    (fun h => hpq (Subtype.ext h))

/-- The actual finite Chinese remainder equivalence, with no chosen-map premise. -/
def crtRing (u : ℕ) (hu : 0 < u) : ZMod (u ^ 2) ≃+* PrimaryProduct u :=
  (ZMod.ringEquivCongr (prod_order u hu).symm).trans
    (ZMod.prodEquivPi (fun p : PrimeIndex u => order u p.val) (pairwise_coprime u))

def crt (u : ℕ) (hu : 0 < u) : ZMod (u ^ 2) ≃+ PrimaryProduct u :=
  (crtRing u hu).toAddEquiv

@[simp] theorem crt_intCast (u : ℕ) (hu : 0 < u) (z : ℤ) (p : PrimeIndex u) :
    crt u hu (z : ZMod (u ^ 2)) p = (z : Component u p) := by
  change (crtRing u hu (z : ZMod (u ^ 2))) p = _
  exact congrArg (fun y : PrimaryProduct u => y p) (map_intCast (crtRing u hu) z)

@[simp] theorem crt_natCast (u : ℕ) (hu : 0 < u) (z : ℕ) (p : PrimeIndex u) :
    crt u hu (z : ZMod (u ^ 2)) p = (z : Component u p) := by
  change (crtRing u hu (z : ZMod (u ^ 2))) p = _
  exact congrArg (fun y : PrimaryProduct u => y p) (map_natCast (crtRing u hu) z)

def primaryGenerator (u : ℕ) (hu : 0 < u) (p : PrimeIndex u) : ZMod (u ^ 2) :=
  (crt u hu).symm (Pi.single p (1 : Component u p))

@[simp] theorem crt_primaryGenerator (u : ℕ) (hu : 0 < u) (p : PrimeIndex u) :
    crt u hu (primaryGenerator u hu p) = Pi.single p (1 : Component u p) :=
  (crt u hu).apply_symm_apply _

@[simp] theorem crt_primaryGenerator_same (u : ℕ) (hu : 0 < u) (p : PrimeIndex u) :
    crt u hu (primaryGenerator u hu p) p = 1 := by
  rw [crt_primaryGenerator, Pi.single_eq_same]

@[simp] theorem crt_primaryGenerator_ne (u : ℕ) (hu : 0 < u)
    (p q : PrimeIndex u) (hqp : q ≠ p) :
    crt u hu (primaryGenerator u hu p) q = 0 := by
  rw [crt_primaryGenerator, Pi.single_eq_of_ne hqp]

end CirculantHadamard.PrimeComponents

end

end OAI


