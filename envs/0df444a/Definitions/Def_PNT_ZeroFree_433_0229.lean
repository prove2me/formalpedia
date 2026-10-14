-- Prove2me | Definitions.Def_PNT_ZeroFree_433_0229
-- name    : PNT_ZeroFree_433_0229
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-11T11:49:32.144703+00:00
-- url     : https://prove2.me/theorems/294b49d0-2720-4325-bdb6-81d3c002d167
-- title:
--   Zero-free region foundations: Eisenstein.BesselMellinTransform [0229]
-- statement:
--   Definitions and proved supporting lemmas from the following source modules:
--
--   - OAI.NumberTheory.DirichletL.Eisenstein.BesselMellinTransform
--
--   These declarations form part of the analytic and arithmetic foundations of the Dirichlet L-function nonvanishing argument in the half-plane Re(s) > 7/8. The original namespaces and hypotheses are retained. The code is ported to Lean 4.33.1 and the pinned Mathlib environment; every included lemma has a complete proof.
-- source:
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Eisenstein/BesselMellinTransform.lean#L81-L601

import Definitions.Def_PNT_ZeroFree_433_0007
import Definitions.Def_PNT_ZeroFree_433_0009
import Definitions.Def_PNT_ZeroFree_433_0100
import Definitions.Def_PNT_ZeroFree_433_0101
import Definitions.Def_PNT_ZeroFree_433_0148_parallel2
import Definitions.Def_PNT_ZeroFree_433_0217_parallel1
import Definitions.Def_PNT_ZeroFree_433_0221_parallel2
import Definitions.Def_PNT_ZeroFree_433_0229_parallel1
import Definitions.Def_PNT_ZeroFree_433_0229_parallel2

/- Supporting zero-free-region lemmas, grouped by independent dependencies.
https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Eisenstein/BesselMellinTransform.lean
-/
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

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


open scoped BigOperators Classical


open scoped BigOperators Classical
namespace CubicEisenstein

section
open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal
local notation "Eis" => ActualEisensteinCubic.O


private theorem finite_tsum_conductor_pullback {R S:Type*} [AddGroup R] [AddGroup S]
    [Finite R] [Finite S] (f:R→+S) (hf:Function.Surjective f) (F:S→ℂ):
    (∑'x:R,F (f x))=(Nat.card f.ker:ℂ)*∑'y:S,F y:=by
  let:Fintype R:=Fintype.ofFinite _
  let:Fintype S:=Fintype.ofFinite _
  let:Fintype f.ker:=Fintype.ofFinite _
  rw [tsum_fintype,tsum_fintype,←Fintype.sum_fiberwise' f F]
  have hc (y:S):Fintype.card {x:R//f x=y}=Fintype.card f.ker:=
    Fintype.card_congr (AddMonoidHom.fiberEquivKerOfSurjective hf y)
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,hc,Nat.card_eq_fintype_card]
  rw [Finset.mul_sum]


theorem conductorFourier_lift (a b:Eis) (ha:a≠0) (hb:b≠0)
    (F:(Eis⧸Ideal.span {a})→ℂ) (k:Eis):
    conductorFourier a b ha hb F (b*k)=
      (Ideal.absNorm (Ideal.span {b}):ℂ)*
        ∑'x:Eis⧸Ideal.span {a},F x*quotientTrace a ha (Ideal.Quotient.mk _ k*x):=by
  let:Finite (Eis⧸Ideal.span {a*b}):=finite_quotient_span (mul_ne_zero ha hb)
  let:Finite (Eis⧸Ideal.span {a}):=finite_quotient_span ha
  unfold conductorFourier
  calc
    _=∑'x:Eis⧸Ideal.span {a*b},F (conductorReduction a b x)*
        quotientTrace a ha (Ideal.Quotient.mk _ k*conductorReduction a b x):=by
      apply tsum_congr
      intro x
      rw [quotientTrace_conductor_scale a b k ha hb]
    _=_:=by
      have he:=finite_tsum_conductor_pullback (conductorReduction a b).toAddMonoidHom
        (conductorReduction_surjective a b)
        (fun y=>F y*quotientTrace a ha (Ideal.Quotient.mk _ k*y))
      rw [conductorReduction_kernel_card a b ha hb] at he
      exact he

end
section

open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal
local notation "Eis" => ActualEisensteinCubic.O


theorem cubicUnitGaussSum_prime_power_lift (p:Eis) (hp:Prime p)
    (hprimary:lambda^2∣p-1) (n:ℕ) (h:Eis):
    cubicUnitGaussSum (p^n*h) (p^(n+1))=
      (Ideal.absNorm (Ideal.span {p}):ℂ)^n*primeCubicGauss p hp hprimary (n+1) h:=by
  rw [cubicUnitGaussSum_prime_power_fourier p hp hprimary n,
    conductorFourier_lift p (p^n) hp.ne_zero (pow_ne_zero _ hp.ne_zero)]
  have hn:Ideal.absNorm (Ideal.span {p^n})=Ideal.absNorm (Ideal.span {p})^n:=by
    rw [←Ideal.span_singleton_pow,map_pow]
  rw [hn,Nat.cast_pow]
  rfl

end

open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal
local notation "Eis" => ActualEisensteinCubic.O


lemma primeCubicGauss_one_eq (p:Eis) (hp:Prime p) (hprimary:lambda^2∣p-1) (h:Eis):
    primeCubicGauss p hp hprimary 1 h=cubicUnitGaussSum h p:=by
  have he:=cubicUnitGaussSum_prime_power_lift p hp hprimary 0 h
  simpa only [pow_zero,one_mul,pow_one,Nat.zero_add] using he.symm

end CubicEisenstein

end

end OAI

end


