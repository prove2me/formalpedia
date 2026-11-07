-- Prove2me | Definitions.Def_OAI_NumberTheory_DirichletL_Hecke_PrimeExtraction
-- name    : OAI_NumberTheory_DirichletL_Hecke_PrimeExtraction
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T07:14:45.134695+00:00
-- url     : https://prove2.me/theorems/cb15619b-6e29-4179-b5a5-c7acc7d876b2
-- title:
--   Prime Extraction
-- statement:
--   Definitions and structural lemmas for Prime Extraction, from LW56e2 and the credited OpenAI and dependency authors's pinned QRH LW56e2 refinement development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Hecke/PrimeExtraction.lean

import Definitions.Def_OAI_NumberTheory_DirichletL_Hecke_LocalEulerIdentities
import Theorems.Thm_OAI_IdealGaussCRT_traceProdChar_mk
attribute [local simp] OAI.IdealGaussCRT.traceProdChar_mk


set_option autoImplicit false
namespace OAI
noncomputable section
open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic RationalPrimeExtraction ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter
open scoped Topology
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open MulChar AddChar
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter
open MulChar AddChar
open MulChar AddChar
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics
namespace ShortDraftHeckeBridge
end ShortDraftHeckeBridge
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
namespace FiniteSFactor
abbrev O := NumberField.RingOfIntegers (CyclotomicField 3 ℚ)
theorem extract_prime_of_squarefree {I P : Ideal O}
    (hI : I ≠ ⊥) (hP : Prime P) (hsq : Squarefree I) (hdvd : P ∣ I) :
    ∃ J : Ideal O, IsRelPrime P J ∧ I = P * J := by
  let : P.IsMaximal := (Ideal.isPrime_of_prime hP).isMaximal hP.ne_zero
  obtain ⟨J, hcop, hfactor⟩ := Ideal.eq_prime_pow_mul_coprime hI P
  have hmem : P ∈ normalizedFactors I := by
    rw [Ideal.mem_normalizedFactors_iff hI]
    exact ⟨Ideal.isPrime_of_prime hP, (Ideal.dvd_iff_le).mp hdvd⟩
  have hpos : 0 < (normalizedFactors I).count P := Multiset.count_pos.mpr hmem
  have hnodup : (normalizedFactors I).Nodup :=
    (UniqueFactorizationMonoid.squarefree_iff_nodup_normalizedFactors hI).mp hsq
  have hle : (normalizedFactors I).count P ≤ 1 :=
    (Multiset.nodup_iff_count_le_one.mp hnodup) P
  have he : (normalizedFactors I).count P = 1 := by omega
  refine ⟨J, ?_, ?_⟩
  · exact IsCoprime.isRelPrime ((Ideal.isCoprime_iff_gcd).mpr (by simpa using hcop))
  · simpa [he] using hfactor
noncomputable def outsideWeight (S : Finset (Ideal O))
    (w : Ideal O → ℂ) (I : Ideal O) : ℂ := by
  classical
  exact if ∀ P ∈ S, ¬ P ∣ I then w I else 0
noncomputable def fiber (n : ℕ) : Finset (Ideal O) :=
  (Ideal.finite_setOfPred_absNorm_eq (S := O) n).toFinset
theorem mem_fiber {n : ℕ} {I : Ideal O} : I ∈ fiber n ↔ Ideal.absNorm I = n := by
  simp [fiber]
noncomputable def badFiber (P : Ideal O) (m : ℕ) : Finset (Ideal O) := by
  classical
  exact (fiber (Ideal.absNorm P * m)).filter (fun I => Squarefree I ∧ P ∣ I)
noncomputable def goodFiber (P : Ideal O) (m : ℕ) : Finset (Ideal O) := by
  classical
  exact (fiber m).filter (fun J => Squarefree J ∧ ¬ P ∣ J)
theorem mem_badFiber {P : Ideal O} {m : ℕ} {I : Ideal O} :
    I ∈ badFiber P m ↔ Ideal.absNorm I = Ideal.absNorm P * m ∧ Squarefree I ∧ P ∣ I := by
  classical
  simp [badFiber, mem_fiber]
noncomputable def pick (P : Ideal O) (hP : Prime P) (m : ℕ)
    (I : Ideal O) (hI : I ∈ badFiber P m) : Ideal O :=
  Classical.choose (extract_prime_of_squarefree
    ((mem_badFiber.mp hI).2.1.ne_zero) hP
    (mem_badFiber.mp hI).2.1 (mem_badFiber.mp hI).2.2)
open scoped Classical
noncomputable def exceptPrimeCoeff (P : Ideal O) (w : Ideal O → ℂ) (n : ℕ) : ℂ := by
  classical
  exact ∑ I ∈ fiber n, if ¬P ∣ I then w I else 0
open scoped Classical
noncomputable def outsideCoeff (S : Finset (Ideal O))
    (w : Ideal O → ℂ) (n : ℕ) : ℂ :=
  ∑ I ∈ fiber n, outsideWeight S w I
end FiniteSFactor
namespace ShortDraftHeckeBridge
end ShortDraftHeckeBridge
namespace DyadicTransfer
noncomputable def annularCutoff (φ : ℝ → ℂ) (y : ℝ) : ℂ :=
  φ y - φ (2 * y)
noncomputable def expAnnularTest (φ : ℝ → ℂ) (D : ℝ) (k : ℕ) (y : ℝ) : ℂ :=
  annularCutoff φ y * Real.exp (-((2 : ℝ) ^ k / D) * y)
end DyadicTransfer
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
namespace FiniteSFactor
end FiniteSFactor
end
end OAI


