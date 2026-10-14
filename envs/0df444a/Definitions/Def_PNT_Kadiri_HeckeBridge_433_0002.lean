-- Prove2me | Definitions.Def_PNT_Kadiri_HeckeBridge_433_0002
-- name    : PNT_Kadiri_HeckeBridge_433_0002
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-12T12:23:18.512676+00:00
-- url     : https://prove2.me/theorems/9c6b28e6-6072-4ce3-9e59-2cec38fc421d
-- title:
--   Complete Hecke-to-zeta bridge, part 0002
-- statement:
--   Complete proved arithmetic and analytic lemmas connecting the Eisenstein Hecke L-function to ordinary Dirichlet L-functions and the Riemann zeta function. The final bridge transfers Hecke nonvanishing in Re(s) > 7/8 to zeta nonvanishing. Original hypotheses and proof bodies are retained; no unproved theorem is imported. Source modules: OAI.NumberTheory.DirichletL.IdealCharacter, OAI.NumberTheory.DirichletL.QuadraticSieve.CrossSeparation, OAI.NumberTheory.DirichletL.ThetaProduct, OAI.NumberTheory.DirichletL.Arithmetic.IdealMobius, OAI.NumberTheory.DirichletL.Arithmetic.LatticeCount, OAI.NumberTheory.DirichletL.CubicSieve.FirstPassage, OAI.NumberTheory.DirichletL.CubicSieve.PooledRows
-- source:
--   OpenAI/math fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb, Apache-2.0; ported to Lean 4.33.1 and pinned Mathlib 0df444a360eaa60ab8c11dca51a86af692955474.

import Definitions.Def_HeckeSevenEighths
import Definitions.Def_PNT_Kadiri_HeckeBridge_433_0001

/- Complete Hecke-to-Dirichlet and zeta bridge lemmas.
Source: OpenAI/math fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb (Apache-2.0).
-/
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

-- Source module: OAI.NumberTheory.DirichletL.IdealCharacter
section
namespace OAI

namespace SevenEighths.IdealCharacter


open Submodule.IsPrincipal
open scoped Classical

noncomputable section

variable {A : Type*} [CommRing A]

abbrev UnitInvariant (M : Ideal A) (χ : MulChar (A ⧸ M) ℂ) : Prop :=
  ∀ u : Aˣ, χ (Ideal.Quotient.mk M u) = 1

theorem residue_eq_of_associated (M : Ideal A) (χ : MulChar (A ⧸ M) ℂ)
    (hχ : UnitInvariant M χ) {a b : A} (hab : Associated a b) :
    χ (Ideal.Quotient.mk M a) = χ (Ideal.Quotient.mk M b) := by
  obtain ⟨u, rfl⟩ := hab
  rw [map_mul, map_mul, hχ u, mul_one]


section Principal

variable [IsDomain A] [IsPrincipalIdealRing A]

def value (M : Ideal A) (χ : MulChar (A ⧸ M) ℂ) (I : Ideal A) : ℂ :=
  if I = ⊥ then 0 else χ (Ideal.Quotient.mk M (generator I))

omit [IsDomain A] in
theorem value_bot (M : Ideal A) (χ : MulChar (A ⧸ M) ℂ) : value M χ ⊥ = 0 := by
  simp only [value, ite_true]

theorem value_span (M : Ideal A) (χ : MulChar (A ⧸ M) ℂ) (hχ : UnitInvariant M χ)
    {a : A} (ha : a ≠ 0) :
    value M χ (Ideal.span ({a} : Set A)) = χ (Ideal.Quotient.mk M a) := by
  have hI : Ideal.span ({a} : Set A) ≠ ⊥ := by
    exact fun h => ha (Ideal.span_singleton_eq_bot.mp h)
  simp only [value, hI, ite_false]
  exact residue_eq_of_associated M χ hχ (associated_generator_span_self a)

def ofResidue (M : Ideal A) (χ : MulChar (A ⧸ M) ℂ) (hχ : UnitInvariant M χ) :
    Ideal A →*₀ ℂ where
  toFun := value M χ
  map_zero' := value_bot M χ
  map_one' := by
    simpa only [Ideal.span_singleton_one, Ideal.one_eq_top, map_one] using
      value_span M χ hχ (one_ne_zero : (1 : A) ≠ 0)
  map_mul' I J := by
    by_cases hI : I = ⊥
    · subst I
      simp only [Ideal.bot_mul, value_bot, zero_mul]
    by_cases hJ : J = ⊥
    · subst J
      simp only [Ideal.mul_bot, value_bot, mul_zero]
    let a := generator I
    let b := generator J
    have ha : a ≠ 0 := fun h => hI ((eq_bot_iff_generator_eq_zero I).mpr h)
    have hb : b ≠ 0 := fun h => hJ ((eq_bot_iff_generator_eq_zero J).mpr h)
    have hIa : Ideal.span ({a} : Set A) = I := Ideal.span_singleton_generator I
    have hJb : Ideal.span ({b} : Set A) = J := Ideal.span_singleton_generator J
    calc
      value M χ (I * J) = value M χ (Ideal.span ({a * b} : Set A)) := by
        rw [← Ideal.span_singleton_mul_span_singleton, hIa, hJb]
      _ = χ (Ideal.Quotient.mk M (a * b)) := value_span M χ hχ (mul_ne_zero ha hb)
      _ = χ (Ideal.Quotient.mk M a) * χ (Ideal.Quotient.mk M b) := by
        rw [map_mul, map_mul]
      _ = value M χ I * value M χ J := by
        rw [← hIa, ← hJb, value_span M χ hχ ha, value_span M χ hχ hb]

@[simp] theorem ofResidue_bot (M : Ideal A) (χ : MulChar (A ⧸ M) ℂ)
    (hχ : UnitInvariant M χ) : ofResidue M χ hχ ⊥ = 0 := value_bot M χ

theorem ofResidue_span (M : Ideal A) (χ : MulChar (A ⧸ M) ℂ) (hχ : UnitInvariant M χ)
    {a : A} (ha : a ≠ 0) :
    ofResidue M χ hχ (Ideal.span ({a} : Set A)) = χ (Ideal.Quotient.mk M a) :=
  value_span M χ hχ ha

theorem ofResidue_of_generator (M : Ideal A) (χ : MulChar (A ⧸ M) ℂ)
    (hχ : UnitInvariant M χ) {I : Ideal A} (hI : I ≠ ⊥) {a : A}
    (ha : Ideal.span ({a} : Set A) = I) :
    ofResidue M χ hχ I = χ (Ideal.Quotient.mk M a) := by
  have ha0 : a ≠ 0 := by
    intro h
    apply hI
    simpa only [h, Ideal.span_singleton_zero] using ha.symm
  rw [← ha, ofResidue_span M χ hχ ha0]

omit [IsDomain A] [IsPrincipalIdealRing A] in
theorem norm_residue_le_one (M : Ideal A) [Finite (A ⧸ M)]
    (χ : MulChar (A ⧸ M) ℂ) (a : A ⧸ M) : ‖χ a‖ ≤ 1 := by
  let : Fintype (A ⧸ M)ˣ := Fintype.ofFinite _
  by_cases ha : IsUnit a
  · obtain ⟨u, rfl⟩ := ha
    have h := Complex.norm_eq_one_of_mem_rootsOfUnity (χ.apply_mem_rootsOfUnity u)
    have hn : ‖χ (u : A ⧸ M)‖ = 1 := by
      simpa only [MulChar.coe_equivToUnitHom] using h
    exact hn.le
  · rw [MulChar.map_nonunit χ ha, norm_zero]
    exact zero_le_one

theorem norm_ofResidue_le_one (M : Ideal A) [Finite (A ⧸ M)]
    (χ : MulChar (A ⧸ M) ℂ) (hχ : UnitInvariant M χ) (I : Ideal A) :
    ‖ofResidue M χ hχ I‖ ≤ 1 := by
  by_cases hI : I = ⊥
  · rw [hI, ofResidue_bot, norm_zero]
    exact zero_le_one
  · change ‖value M χ I‖ ≤ 1
    simp only [value, hI, ite_false]
    exact norm_residue_le_one M χ _


end Principal

end

end SevenEighths.IdealCharacter

end OAI

end

-- Source module: OAI.NumberTheory.DirichletL.QuadraticSieve.CrossSeparation
section
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
open ActualEisensteinCubic
open ActualEisensteinCubic
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
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Filter Asymptotics
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics Ideal NumberField
open Filter
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory Set
open scoped BigOperators

open scoped BigOperators Classical


open scoped BigOperators Classical

namespace CoprimeMobiusExtension


theorem sum_subset_sign {ι : Type*} [DecidableEq ι] (S : Finset ι) :
    (∑ D ∈ S.powerset, (-1 : ℂ) ^ D.card) = if S = ∅ then 1 else 0 := by
  have hp := Finset.prod_sub (fun _ : ι => (1 : ℂ)) (fun _ => 1) S
  by_cases hS : S = ∅
  · simp [hS]
  · have hc : S.card ≠ 0 := Finset.card_ne_zero.mpr (Finset.nonempty_iff_ne_empty.mpr hS)
    simpa [hS, hc] using hp.symm


end CoprimeMobiusExtension

end

end OAI

end

-- Source module: OAI.NumberTheory.DirichletL.ThetaProduct
section
namespace OAI

noncomputable section
open Filter Asymptotics Set MeasureTheory
open scoped Topology

namespace SevenEighths.ThetaProduct


theorem rectangularPair_hasSum (a b u v : ℝ) (hu : 0 < u) (hv : 0 < v)
    {t : ℝ} (ht : 0 < t) :
    HasSum (fun n : ℤ × ℤ =>
      (Real.exp (-Real.pi * (u * (n.1 + a) ^ 2 + v * (n.2 + b) ^ 2) * t) : ℂ))
      ((rectangularPair a b u v hu hv).f t) := by
  have h₁ := HurwitzZeta.hasSum_int_evenKernel a (mul_pos hu ht)
  have h₂ := HurwitzZeta.hasSum_int_evenKernel b (mul_pos hv ht)
  have hprod := h₁.mul h₂ (h₁.summable.mul_of_nonneg h₂.summable
    (fun _ => (Real.exp_pos _).le) (fun _ => (Real.exp_pos _).le))
  have hid (n : ℤ × ℤ) :
      Real.exp (-Real.pi * (u * (n.1 + a) ^ 2 + v * (n.2 + b) ^ 2) * t) =
      Real.exp (-Real.pi * (n.1 + a) ^ 2 * (u * t)) *
        Real.exp (-Real.pi * (n.2 + b) ^ 2 * (v * t)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  simp_rw [hid]
  simpa only [rectangularPair, product, scaledEvenPair, rescale,
    HurwitzZeta.hurwitzEvenFEPair, Function.comp_apply, Complex.ofReal_mul] using
    (Complex.hasSum_ofReal.mpr hprod)


end SevenEighths.ThetaProduct

end

end OAI

end

-- Source module: OAI.NumberTheory.DirichletL.Arithmetic.IdealMobius
section
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
open ActualEisensteinCubic
open ActualEisensteinCubic
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
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Filter Asymptotics
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics Ideal NumberField
open Filter
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory Set
open scoped BigOperators
open scoped BigOperators Classical

open scoped BigOperators Classical
open ActualEisensteinCubic UniqueFactorizationMonoid

namespace IdealMobiusDivisorSum
abbrev O := ActualEisensteinCubic.O

def idealDivisors (I : Ideal O) : Finset (Ideal O) :=
  (Ideal.finite_setOfPred_absNorm_le (S := O) (Ideal.absNorm I)).toFinset.filter
    (fun J => J ∣ I)

theorem mem_idealDivisors {I J : Ideal O} (hI : I ≠ ⊥) :
    J ∈ idealDivisors I ↔ J ∣ I := by
  simp only [idealDivisors, Finset.mem_filter, Set.Finite.mem_toFinset, Set.mem_ofPred_eq]
  constructor
  · exact And.right
  · intro hJI
    have hn : 0 < Ideal.absNorm I := Nat.pos_iff_ne_zero.mpr
      (fun hz => hI (Ideal.absNorm_eq_zero_iff.mp hz))
    exact ⟨Nat.le_of_dvd hn (map_dvd Ideal.absNorm hJI), hJI⟩

def primeSupport (I : Ideal O) : Finset (Ideal O) := (normalizedFactors I).toFinset

theorem support_prime {I : Ideal O} {P : Ideal O} (hP : P ∈ primeSupport I) : Prime P :=
  prime_of_normalized_factor P (Multiset.mem_toFinset.mp hP)

theorem support_product_ne_zero {I : Ideal O} {S : Finset (Ideal O)}
    (hS : S ⊆ primeSupport I) : (∏ P ∈ S, P) ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr (fun _P hP => (support_prime (hS hP)).ne_zero)

theorem factors_support_product {I : Ideal O} {S : Finset (Ideal O)}
    (hS : S ⊆ primeSupport I) : normalizedFactors (∏ P ∈ S, P) = S.val := by
  have hp : ∀ P ∈ S.val, Prime P := fun P hP => support_prime (hS hP)
  simpa using normalizedFactors_prod_of_prime hp

theorem squarefree_support_product {I : Ideal O} {S : Finset (Ideal O)}
    (hS : S ⊆ primeSupport I) : Squarefree (∏ P ∈ S, P) := by
  apply (squarefree_iff_nodup_normalizedFactors (support_product_ne_zero hS)).mpr
  rw [factors_support_product hS]
  exact S.nodup

theorem support_product_dvd {I : Ideal O} (hI : I ≠ ⊥) {S : Finset (Ideal O)}
    (hS : S ⊆ primeSupport I) : (∏ P ∈ S, P) ∣ I := by
  apply (dvd_iff_normalizedFactors_le_normalizedFactors (support_product_ne_zero hS) hI).mpr
  rw [factors_support_product hS]
  apply (Multiset.le_iff_subset S.nodup).mpr
  intro P hP
  exact Multiset.mem_toFinset.mp (hS hP)

theorem moebius_support_product {I : Ideal O} {S : Finset (Ideal O)}
    (hS : S ⊆ primeSupport I) :
    (moebius (∏ P ∈ S, P) : ℂ) = (-1 : ℂ) ^ S.card := by
  rw [(squarefree_support_product hS).moebius_eq, factors_eq_normalizedFactors,
    factors_support_product hS]
  simp

theorem support_product_injective {I : Ideal O}
    {S T : Finset (Ideal O)} (hS : S ⊆ primeSupport I) (hT : T ⊆ primeSupport I)
    (h : (∏ P ∈ S, P) = ∏ P ∈ T, P) : S = T := by
  have hf := congrArg normalizedFactors h
  rw [factors_support_product hS, factors_support_product hT] at hf
  exact Finset.val_inj.mp hf

theorem squarefree_divisor_support {I J : Ideal O} (hI : I ≠ ⊥)
    (hJ : Squarefree J) (hJI : J ∣ I) : primeSupport J ⊆ primeSupport I := by
  have hf := (dvd_iff_normalizedFactors_le_normalizedFactors hJ.ne_zero hI).mp hJI
  intro P hP
  exact Multiset.mem_toFinset.mpr (Multiset.mem_of_le hf (Multiset.mem_toFinset.mp hP))

theorem squarefree_support_product_self {J : Ideal O} (hJ : Squarefree J) :
    (∏ P ∈ primeSupport J, P) = J := by
  have hn : (normalizedFactors J).Nodup :=
    (squarefree_iff_nodup_normalizedFactors hJ.ne_zero).mp hJ
  have hv : (primeSupport J).val = normalizedFactors J := by
    simpa only [primeSupport, Multiset.toFinset_val] using hn.dedup
  calc
    _ = (primeSupport J).val.prod := (Finset.prod_val _).symm
    _ = (normalizedFactors J).prod := by rw [hv]
    _ = J := Ideal.prod_normalizedFactors_eq_self hJ.ne_zero

theorem squarefree_divisors_eq_image (I : Ideal O) (hI : I ≠ ⊥) :
    (idealDivisors I).filter Squarefree =
      (primeSupport I).powerset.image (fun S => ∏ P ∈ S, P) := by
  ext J
  simp only [Finset.mem_filter, mem_idealDivisors hI, Finset.mem_image, Finset.mem_powerset]
  constructor
  · rintro ⟨hJI, hJ⟩
    exact ⟨primeSupport J, squarefree_divisor_support hI hJ hJI,
      squarefree_support_product_self hJ⟩
  · rintro ⟨S, hS, rfl⟩
    exact ⟨support_product_dvd hI hS, squarefree_support_product hS⟩

theorem primeSupport_empty_iff (I : Ideal O) (hI : I ≠ ⊥) :
    primeSupport I = ∅ ↔ I = ⊤ := by
  constructor
  · intro h
    have hz : normalizedFactors I = 0 := by
      apply Multiset.toFinset_eq_empty.mp
      exact h
    have hp := Ideal.prod_normalizedFactors_eq_self hI
    rw [hz, Multiset.prod_zero] at hp
    simpa only [Ideal.one_eq_top] using hp.symm
  · intro h
    subst I
    simp [primeSupport, ← Ideal.one_eq_top]

theorem sum_moebius_divisors (I : Ideal O) (hI : I ≠ ⊥) :
    (∑ J ∈ idealDivisors I, (moebius J : ℂ)) = if I = ⊤ then 1 else 0 := by
  have hfilter : (∑ J ∈ idealDivisors I, (moebius J : ℂ)) =
      ∑ J ∈ (idealDivisors I).filter Squarefree, (moebius J : ℂ) := by
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro J hJ hnot
    have hn : ¬ Squarefree J := by simpa [hJ] using hnot
    rw [moebius_of_not_squarefree hn, Int.cast_zero]
  rw [hfilter, squarefree_divisors_eq_image I hI, Finset.sum_image]
  · have heq : (∑ S ∈ (primeSupport I).powerset, (moebius (∏ P ∈ S, P) : ℂ)) =
        ∑ S ∈ (primeSupport I).powerset, (-1 : ℂ) ^ S.card := by
      exact Finset.sum_congr rfl (fun S hS => moebius_support_product (Finset.mem_powerset.mp hS))
    rw [heq, CoprimeMobiusExtension.sum_subset_sign]
    simp only [primeSupport_empty_iff I hI]
  · intro S hS T hT hST
    exact support_product_injective (Finset.mem_powerset.mp hS)
      (Finset.mem_powerset.mp hT) hST

end IdealMobiusDivisorSum

open scoped BigOperators Classical

namespace CompletedGauss

section

abbrev O := ActualEisensteinCubic.O
open ActualEisensteinCubic


open ActualEisensteinCubic


end
section

open ActualEisensteinCubic ConcreteTraceCRT

def primeSupport (I : Ideal O) : Finset (Ideal O) :=
  (UniqueFactorizationMonoid.normalizedFactors I).toFinset

abbrev PrimeIndex (I : Ideal O) := {P : Ideal O // P ∈ primeSupport I}

instance primeIndexMaximal (I : Ideal O) (P : PrimeIndex I) : P.val.IsMaximal := by
  have hp := UniqueFactorizationMonoid.prime_of_normalized_factor P.val
    (Multiset.mem_toFinset.mp P.property)
  exact (Ideal.isPrime_of_prime hp).isMaximal hp.ne_zero


end

open ActualEisensteinCubic
open IdealMobiusDivisorSum (idealDivisors mem_idealDivisors sum_moebius_divisors)

def MulFiber (B : Ideal O) := {p : Ideal O × Ideal O // p.1 * p.2 = B}

def mulFiberDivisorEquiv (B : Ideal O) (hB : B ≠ 0) :
    MulFiber B ≃ {D : Ideal O // D ∈ idealDivisors B} := by
  let f : MulFiber B → {D : Ideal O // D ∈ idealDivisors B} :=
    fun p => ⟨p.val.1, (mem_idealDivisors hB).mpr ⟨p.val.2, p.property.symm⟩⟩
  apply Equiv.ofBijective f
  constructor
  · intro p q hpq
    have hfst : p.val.1 = q.val.1 := congrArg Subtype.val hpq
    apply Subtype.ext
    apply Prod.ext hfst
    have hn : p.val.1 ≠ 0 := by
      intro hz
      have he := p.property
      rw [hz, zero_mul] at he
      exact hB he.symm
    apply mul_left_cancel₀ hn
    rw [p.property, hfst, q.property]
  · intro D
    obtain ⟨J, hJ⟩ := (mem_idealDivisors hB).mp D.property
    exact ⟨⟨(D.val, J), hJ.symm⟩, rfl⟩

theorem mulFiber_moebius_sum (B : Ideal O) (hB : B ≠ 0) :
    (∑' p : MulFiber B, (UniqueFactorizationMonoid.moebius p.val.1 : ℂ)) =
      if B = 1 then 1 else 0 := by
  let e := mulFiberDivisorEquiv B hB
  calc
    _ = ∑' D : {D : Ideal O // D ∈ idealDivisors B},
        (UniqueFactorizationMonoid.moebius D.val : ℂ) := by
      exact e.tsum_eq (fun D => (UniqueFactorizationMonoid.moebius D.val : ℂ))
    _ = ∑ D ∈ idealDivisors B, (UniqueFactorizationMonoid.moebius D : ℂ) := by
      rw [tsum_fintype]
      exact (Finset.sum_subtype (idealDivisors B) (fun D => Iff.rfl)
        (fun D => (UniqueFactorizationMonoid.moebius D : ℂ))).symm
    _ = if B = 1 then 1 else 0 := by
      simpa only [Ideal.one_eq_top] using sum_moebius_divisors B hB


end CompletedGauss

end

end OAI

end

-- Source module: OAI.NumberTheory.DirichletL.Arithmetic.LatticeCount
section
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

namespace ShortDraftLatticeCount

def q (x : ℤ × ℤ) : ℤ := x.1 ^ 2 - x.1 * x.2 + x.2 ^ 2

theorem coordinate_squares (a b D : ℤ) (hD : 0 ≤ D)
    (h : a ^ 2 - a * b + b ^ 2 ≤ D) :
    a ^ 2 ≤ 2 * D ∧ b ^ 2 ≤ 2 * D := by
  constructor <;> nlinarith [sq_nonneg (a - 2 * b), sq_nonneg (2 * a - b)]


end ShortDraftLatticeCount


namespace ShortDraftLatticeCount

open ActualEisensteinCoordinates

theorem coords_eval (a b : ℤ) :
    coords (eval a b) = (a, b) := by
  have h := unique_coordinates (eval_coords (eval a b))
  exact Prod.ext h.1 h.2


theorem qO_nonneg (x : O) : 0 ≤ q (coords x) := by
  exact ShortDraft.eisenstein_norm_nonneg (coords x)


def qNat (x : O) : ℕ := (q (coords x)).toNat


end ShortDraftLatticeCount


end

end OAI

end

-- Source module: OAI.NumberTheory.DirichletL.CubicSieve.FirstPassage
section
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
open ActualEisensteinCubic ShortDraftLatticeCount
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
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Filter Asymptotics
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics Ideal NumberField
open Filter
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory Set
open scoped BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open ActualEisensteinCubic UniqueFactorizationMonoid


namespace SecondPassArithmetic

section
abbrev O := ActualEisensteinCubic.O


end


end SecondPassArithmetic

end

end OAI

end

-- Source module: OAI.NumberTheory.DirichletL.CubicSieve.PooledRows
section
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
open ActualEisensteinCubic ShortDraftLatticeCount
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
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Filter Asymptotics
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics Ideal NumberField
open Filter
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory Set
open scoped BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open ActualEisensteinCubic UniqueFactorizationMonoid
open scoped BigOperators

open scoped BigOperators Classical SchwartzMap


open scoped BigOperators Classical
namespace InitialMeanSquare

section
open ActualEisensteinCubic IdealMobiusDivisorSum
abbrev O := ActualEisensteinCubic.O

structure Datum where
  divisor : Ideal O
  shared : Ideal O
  frequency : O
  deriving DecidableEq


end


end InitialMeanSquare

end

end OAI

end


