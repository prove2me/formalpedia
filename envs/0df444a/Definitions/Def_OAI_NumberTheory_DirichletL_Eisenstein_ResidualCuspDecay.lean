-- Prove2me | Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_ResidualCuspDecay
-- name    : OAI_NumberTheory_DirichletL_Eisenstein_ResidualCuspDecay
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-10T21:28:25.810194+00:00
-- url     : https://prove2.me/theorems/059bc1cc-7384-4144-aede-74ee33ab652f
-- title:
--   Residual Cusp Decay
-- statement:
--   Definitions and structural lemmas for Residual Cusp Decay, from LW56e2 and the credited OpenAI and dependency authors's pinned QRH LW56e2 refinement development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Eisenstein/ResidualCuspDecay.lean

import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_BesselMellinTransform
import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_TranslatedFourierResidues
import Theorems.Thm_OAI_CompletedGauss_primaryGenerator_span

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
open scoped BigOperators
open scoped BigOperators Classical SchwartzMap
open scoped BigOperators Classical
namespace CubicEisenstein
open Filter MeasureTheory
open scoped BigOperators Classical Topology
open Finset AddChar MulChar EisensteinEmbedding
local notation "O" => ActualEisensteinCubic.O
def residualCuspDecayRate : ℝ := Real.pi*‖(3:ℂ)*ConcreteTraceCRT.eisLam‖⁻¹/4
end CubicEisenstein
namespace ShortDraftCRT
open scoped BigOperators Classical Matrix
section
variable {R : Type*} [CommRing R]
variable [IsDomain R]
end
variable {R : Type*} [CommRing R] [IsDomain R]
def LiftedRows (M c : R) :=
  {rows : List (R×R) // GoodRows c rows ∧ (∀ph∈rows,M^2∣ph.2) ∧
    IsCoprime (rows.map Prod.fst).prod (M*c)}
end ShortDraftCRT
open scoped BigOperators Classical
namespace ShortDraftCusp
section
open ActualEisensteinCubic CubicJacobiGlobal CubicKubota
local notation "Eis" => ActualEisensteinCubic.O
end
open ActualEisensteinCubic CubicJacobiGlobal CubicKubota
local notation "Eis" => ActualEisensteinCubic.O
end ShortDraftCusp
open scoped BigOperators Classical
namespace CubicEisenstein
open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal CompletedGauss
open PrimaryIdealUnitReindex (GoodIdeal)
local notation "Eis" => ActualEisensteinCubic.O
abbrev PrimeDeletedIdeal (p:Eis):={I:GoodIdeal//¬(Ideal.span {p}:Ideal Eis)∣I.val}
def unramifiedPrimeDeletedSeries (p:Eis) (s:ℂ) (h:Eis):ℂ:=
  ∑'I:PrimeDeletedIdeal p,(Ideal.absNorm I.val.val:ℂ)^(-s)*
    cubicUnitGaussSum h (primaryGenerator I.val.val)
lemma primaryGenerator_pow (I:Ideal Eis) (n:ℕ):
    primaryGenerator (I^n)=primaryGenerator I^n:=
  map_pow primaryGeneratorHom I n
lemma gaussPrimeIdeal_prime (p:Eis) (hp:Prime p):Prime (Ideal.span {p}:Ideal Eis):=
  Ideal.prime_of_isPrime (Ideal.span_singleton_eq_bot.not.mpr hp.ne_zero)
    ((Ideal.span_singleton_prime hp.ne_zero).mpr hp)
def gaussPrimeFactorMap (p:Eis) (hp:Prime p) (hprimary:lambda^2∣p-1)
    (q:ℕ×PrimeDeletedIdeal p):GoodIdeal:=
  ⟨(Ideal.span {p})^q.1*q.2.val.val,by
    rw [primaryGenerator_mul,primaryGenerator_pow,primaryGenerator_span p hp.ne_zero hprimary]
    exact mul_ne_zero (pow_ne_zero _ hp.ne_zero) q.2.val.2⟩
lemma gaussPrimeFactorMap_bijective (p:Eis) (hp:Prime p) (hprimary:lambda^2∣p-1):
    Function.Bijective (gaussPrimeFactorMap p hp hprimary):=by
  let P:Ideal Eis:=Ideal.span {p}
  have hP:Prime P:=gaussPrimeIdeal_prime p hp
  constructor
  · rintro ⟨n,I⟩ ⟨m,J⟩ heq
    have hh:P^n*I.val.val=P^m*J.val.val:=congrArg Subtype.val heq
    have hn:n=m:=by
      have hm:=congrArg (multiplicity P) hh
      rw [prime_power_remainder_multiplicity hP I.2,
        prime_power_remainder_multiplicity hP J.2] at hm
      exact hm
    subst m
    have hIJ:I=J:=Subtype.ext (Subtype.ext
      (mul_left_cancel₀ (pow_ne_zero n hP.ne_zero) hh))
    subst J
    rfl
  · intro I
    obtain ⟨J,hJ,hnot⟩:=(FiniteMultiplicity.of_prime_left hP
      (primaryGenerator_ne_zero_ideal I.val I.2)).exists_eq_pow_mul_and_not_dvd
    have hgood:primaryGenerator J≠0:=by
      intro hzero
      apply I.2
      rw [hJ,primaryGenerator_mul,hzero,mul_zero]
    refine ⟨(multiplicity P I.val,⟨⟨J,hgood⟩,hnot⟩),?_⟩
    exact Subtype.ext hJ.symm
def gaussPrimeFactorEquiv (p:Eis) (hp:Prime p) (hprimary:lambda^2∣p-1):
    ℕ×PrimeDeletedIdeal p≃GoodIdeal:=
  Equiv.ofBijective (gaussPrimeFactorMap p hp hprimary)
    (gaussPrimeFactorMap_bijective p hp hprimary)
end CubicEisenstein
end
end OAI


