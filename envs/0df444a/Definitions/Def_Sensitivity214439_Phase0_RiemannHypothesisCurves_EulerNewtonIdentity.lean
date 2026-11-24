-- Prove2me | Definitions.Def_Sensitivity214439_Phase0_RiemannHypothesisCurves_EulerNewtonIdentity
-- name    : Sensitivity214439_Phase0_RiemannHypothesisCurves_EulerNewtonIdentity
-- status  : Definition
-- author  : @yousofy
-- created : 2026-11-24T13:08:13.278388+00:00
-- url     : https://prove2.me/theorems/7e9ce196-c6a8-4f17-9275-1598f97ad2bc
-- title:
--   Monic prime factorizations and degree-indexed prime sets
-- statement:
--   A monic prime is a monic irreducible polynomial over a field. A finitely supported natural multiplicity function on these primes determines their product and its total degree, obtained by summing multiplicity times prime degree. The reverse construction records the normalized irreducible factors of a polynomial. The bundle includes the inverse identities on monic polynomials, their compatibility with multiplication, and the resulting equivalence between monic polynomials of degree n and multiplicity functions of total degree n. Over a finite field, it also defines the finite sets of monic primes of a specified degree and of degree at most a given cutoff.
-- source:
--   Formalization for https://prove2.me/campaigns/block-sensitivity-vs-sensitivity; task source research/hec-lean433/RiemannHypothesisCurves/EulerNewtonIdentity.lean lines 22–179; SHA256 e417bf4db8ee0c06746ee939c7b84020ce7ceefde540c73552313d7cbe5fbd17; original campaign checkpoint SHA256 ed463039fb45e15e0e62a99e149dc811ac44ae8f790a5ae03ea5a7501f0639df.

import Definitions.Def_Sensitivity214439_Phase0_ZetaLean_PrivateStock_FiniteIsMonicOfDegree
import Mathlib.Algebra.Polynomial.Degree.IsMonicOfDegree
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Data.Finsupp.Weight
import Mathlib.FieldTheory.Finite.Extension
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic
import Mathlib.RingTheory.Norm.Transitivity
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.RingTheory.UniqueFactorizationDomain.Finsupp
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.InfiniteSum.Basic

namespace Finset
end Finset
namespace PaleyWeil
end PaleyWeil
namespace Polynomial
end Polynomial
namespace UniqueFactorizationMonoid
end UniqueFactorizationMonoid



/-!
The unique-factorization and finite Euler-product bridge for the split
quadratic-character L-series. All factorization statements concern actual
monic polynomials; no character-sum estimate is assumed here.
-/

open Polynomial Finset UniqueFactorizationMonoid

namespace PaleyWeil

noncomputable section

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1200000

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]

abbrev MonicPrime (K : Type*) [Field K] :=
  {P : K[X] // P.Monic ∧ Irreducible P}

def primeProduct (m : MonicPrime K →₀ ℕ) : K[X] :=
  m.prod fun P e ↦ (P : K[X]) ^ e

def primeFactors (P : K[X]) : MonicPrime K →₀ ℕ :=
  (factorization P).subtypeDomain (fun Q ↦ Q.Monic ∧ Irreducible Q)

@[simp] theorem primeProduct_zero : primeProduct (0 : MonicPrime K →₀ ℕ) = 1 := by
  simp [primeProduct]

theorem primeProduct_add (m t : MonicPrime K →₀ ℕ) :
    primeProduct (m + t) = primeProduct m * primeProduct t := by
  exact Finsupp.prod_add_index' (fun _ ↦ pow_zero _) (fun _ _ _ ↦ pow_add ..)

@[simp] theorem primeProduct_single (P : MonicPrime K) (e : ℕ) :
    primeProduct (Finsupp.single P e) = (P : K[X]) ^ e := by
  exact Finsupp.prod_single_index (pow_zero _)

theorem primeProduct_monic (m : MonicPrime K →₀ ℕ) : (primeProduct m).Monic := by
  exact monic_prod_of_monic m.support _ (fun P _ ↦ P.2.1.pow _)

theorem primeProduct_natDegree (m : MonicPrime K →₀ ℕ) :
    (primeProduct m).natDegree = m.sum (fun P e ↦ e * (P : K[X]).natDegree) := by
  rw [primeProduct, Finsupp.prod, natDegree_prod_of_monic]
  · simp only [natDegree_pow, Finsupp.sum, Nat.mul_comm]
  · exact fun P _ ↦ P.2.1.pow _

@[simp] theorem primeFactors_one : primeFactors (1 : K[X]) = 0 := by
  simp [primeFactors]

theorem primeFactors_mul {P Q : K[X]} (hP : P ≠ 0) (hQ : Q ≠ 0) :
    primeFactors (P * Q) = primeFactors P + primeFactors Q := by
  simp only [primeFactors, factorization_mul hP hQ, Finsupp.subtypeDomain_add]

@[simp] theorem primeFactors_prime_pow (P : MonicPrime K) (e : ℕ) :
    primeFactors ((P : K[X]) ^ e) = Finsupp.single P e := by
  classical
  have hnorm : normalize (P : K[X]) = (P : K[X]) :=
    (normalize_eq_self_iff_monic P.2.1.ne_zero).mpr P.2.1
  ext Q
  simp only [primeFactors, Finsupp.subtypeDomain_apply, factorization_eq_count,
    normalizedFactors_of_irreducible_pow P.2.2, hnorm, Multiset.count_replicate,
    Finsupp.single_apply]
  simp only [Subtype.ext_iff]

theorem primeProduct_primeFactors {P : K[X]} (hP : P.Monic) :
    primeProduct (primeFactors P) = P := by
  have hsupp : ∀ Q ∈ (factorization P).support, Q.Monic ∧ Irreducible Q := by
    intro Q hQ
    have hmem : Q ∈ normalizedFactors P := by
      simpa only [support_factorization, Multiset.mem_toFinset] using hQ
    have hp := (Polynomial.mem_normalizedFactors_iff hP.ne_zero).mp hmem
    exact ⟨hp.2.1, hp.1⟩
  rw [primeProduct, primeFactors, Finsupp.prod_subtypeDomain_index hsupp,
    ← Finsupp.prod_toMultiset]
  change (Finsupp.toMultiset (Multiset.toFinsupp (normalizedFactors P))).prod = P
  rw [Multiset.toFinsupp_toMultiset]
  simpa only [hP.leadingCoeff, C_1, one_mul] using
    leadingCoeff_mul_prod_normalizedFactors P

theorem primeFactors_primeProduct (m : MonicPrime K →₀ ℕ) :
    primeFactors (primeProduct m) = m := by
  classical
  induction m using Finsupp.induction with
  | zero => simp
  | single_add P e m _ _ ih =>
    rw [primeProduct_add, primeFactors_mul (primeProduct_monic _).ne_zero
      (primeProduct_monic _).ne_zero, primeProduct_single, primeFactors_prime_pow, ih]







def primeDegree (m : MonicPrime K →₀ ℕ) : ℕ :=
  m.sum (fun P e ↦ e * (P : K[X]).natDegree)

def monicDegreeFactorizationEquiv (n : ℕ) :
    {P : K[X] // IsMonicOfDegree P n} ≃
      {m : MonicPrime K →₀ ℕ // primeDegree m = n} where
  toFun P := ⟨primeFactors P, by
    rw [primeDegree, ← primeProduct_natDegree, primeProduct_primeFactors P.2.monic,
      P.2.natDegree_eq]⟩
  invFun m := ⟨primeProduct m.1, ⟨by
    rw [primeProduct_natDegree]
    exact m.2, primeProduct_monic m.1⟩⟩
  left_inv P := Subtype.ext (primeProduct_primeFactors P.2.monic)
  right_inv m := by
    apply Subtype.ext
    change primeFactors (primeProduct m.1) = m.1
    exact primeFactors_primeProduct m.1



 theorem finite_prime_degree (d : ℕ) :
    Finite {P : K[X] // P.Monic ∧ Irreducible P ∧ P.natDegree = d} := by
  letI := finite_isMonicOfDegree (F := K) d
  exact Finite.of_injective
    (fun P : {P : K[X] // P.Monic ∧ Irreducible P ∧ P.natDegree = d} ↦
      (⟨P.1, P.2.2.2, P.2.1⟩ : {Q : K[X] // IsMonicOfDegree Q d}))
    (fun _ _ h ↦ Subtype.ext
      (congrArg (fun Q : {Q : K[X] // IsMonicOfDegree Q d} ↦ Q.1) h))

def primesOfDegree (d : ℕ) : Finset (MonicPrime K) := by
  classical
  letI := finite_prime_degree (K := K) d
  letI := Fintype.ofFinite {P : K[X] // P.Monic ∧ Irreducible P ∧ P.natDegree = d}
  exact Finset.univ.image (fun P : {P : K[X] // P.Monic ∧ Irreducible P ∧ P.natDegree = d} ↦
    (⟨P.1, P.2.1, P.2.2.1⟩ : MonicPrime K))

@[simp] theorem mem_primesOfDegree (d : ℕ) (P : MonicPrime K) :
    P ∈ primesOfDegree d ↔ (P : K[X]).natDegree = d := by
  classical
  simp only [primesOfDegree, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨Q, hQ⟩
    simpa only [← hQ] using Q.2.2.2
  · intro hP
    exact ⟨⟨P.1, P.2.1, P.2.2, hP⟩, rfl⟩

def primesUpTo (n : ℕ) : Finset (MonicPrime K) := by
  classical
  exact (Finset.range (n + 1)).biUnion primesOfDegree











end
end PaleyWeil


