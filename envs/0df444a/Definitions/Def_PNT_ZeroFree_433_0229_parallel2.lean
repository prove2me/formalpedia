-- Prove2me | Definitions.Def_PNT_ZeroFree_433_0229_parallel2
-- name    : PNT_ZeroFree_433_0229_parallel2
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-11T11:38:22.157977+00:00
-- url     : https://prove2.me/theorems/5a97d545-4a80-4bde-bf05-33b779dd019c
-- title:
--   Zero-free region foundations: Eisenstein.BesselMellinTransform [0229_parallel2]
-- statement:
--   Definitions and proved supporting lemmas from the following source modules:
--
--   - OAI.NumberTheory.DirichletL.Eisenstein.BesselMellinTransform
--
--   These declarations form part of the analytic and arithmetic foundations of the Dirichlet L-function nonvanishing argument in the half-plane Re(s) > 7/8. The original namespaces and hypotheses are retained. The code is ported to Lean 4.33.1 and the pinned Mathlib environment; every included lemma has a complete proof.
-- source:
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Eisenstein/BesselMellinTransform.lean#L253-L596

import Definitions.Def_PNT_ZeroFree_433_0004
import Definitions.Def_PNT_ZeroFree_433_0007
import Definitions.Def_PNT_ZeroFree_433_0009
import Definitions.Def_PNT_ZeroFree_433_0017
import Definitions.Def_PNT_ZeroFree_433_0031
import Definitions.Def_PNT_ZeroFree_433_0040
import Definitions.Def_PNT_ZeroFree_433_0046_1_1_1
import Definitions.Def_PNT_ZeroFree_433_0067
import Definitions.Def_PNT_ZeroFree_433_0068_1
import Definitions.Def_PNT_ZeroFree_433_0071
import Definitions.Def_PNT_ZeroFree_433_0074
import Definitions.Def_PNT_ZeroFree_433_0085
import Definitions.Def_PNT_ZeroFree_433_0093
import Definitions.Def_PNT_ZeroFree_433_0094
import Definitions.Def_PNT_ZeroFree_433_0097
import Definitions.Def_PNT_ZeroFree_433_0146_parallel1
import Definitions.Def_PNT_ZeroFree_433_0217_parallel1
import Definitions.Def_PNT_ZeroFree_433_0227_parallel1
import Definitions.Def_PNT_ZeroFree_433_0229_parallel1
import Definitions.Def_PNT_ZeroFree_433_0231_parallel2
import Definitions.Def_PNT_ZeroFree_433_0234_parallel1_1
import Definitions.Def_PNT_ZeroFree_433_0244_parallel1_1

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


lemma quotientTrace_mk (c:Eis) (hc:c≠0) (x:Eis):
    quotientTrace c hc (Ideal.Quotient.mk _ x)=residueAdditive (3*x) c 1:=by
  simp only [quotientTrace,eisTraceModChar,IdealGaussCRT.traceModChar_mk]
  unfold residueAdditive cuspFrequency
  simp only [map_mul,map_one,map_ofNat]
  congr 1
  ring


lemma conductorReduction_kernel_card (a b:Eis) (ha:a≠0) (_hb:b≠0):
    Nat.card (conductorReduction a b).toAddMonoidHom.ker=Ideal.absNorm (Ideal.span {b}):=by
  have hc:=card_ring_eq_card_mul_kernel (conductorReduction a b)
    (conductorReduction_surjective a b)
  change Ideal.absNorm (Ideal.span {a*b})=
    Ideal.absNorm (Ideal.span {a})*Nat.card (conductorReduction a b).toAddMonoidHom.ker at hc
  conv_lhs at hc => rw [←Ideal.span_singleton_mul_span_singleton,map_mul]
  have hpos:0<Ideal.absNorm (Ideal.span {a}):=by
    apply Nat.pos_iff_ne_zero.mpr
    intro hz
    exact ha (Ideal.span_singleton_eq_bot.mp (Ideal.absNorm_eq_zero_iff.mp hz))
  exact (Nat.eq_of_mul_eq_mul_left hpos hc).symm


lemma quotientTrace_conductor_scale (a b k:Eis) (ha:a≠0) (hb:b≠0)
    (x:Eis⧸Ideal.span {a*b}):
    quotientTrace (a*b) (mul_ne_zero ha hb) (Ideal.Quotient.mk _ (b*k)*x)=
      quotientTrace a ha (Ideal.Quotient.mk _ k*conductorReduction a b x):=by
  obtain ⟨d,rfl⟩:=Ideal.Quotient.mk_surjective x
  change quotientTrace (a*b) (mul_ne_zero ha hb)
    (Ideal.Quotient.mk _ (b*k)*Ideal.Quotient.mk _ d)=
    quotientTrace a ha (Ideal.Quotient.mk _ k*Ideal.Quotient.mk _ d)
  rw [←map_mul,←map_mul,quotientTrace_mk,quotientTrace_mk]
  simp only [residueAdditive,cuspFrequency,map_mul,map_one,map_ofNat]
  congr 1
  have hae:=eisEmbedding_ne_zero ha
  have hbe:=eisEmbedding_ne_zero hb
  field_simp


end
section

open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal
local notation "Eis" => ActualEisensteinCubic.O


def primeCubicMulChar (p:Eis) (hp:Prime p) (hprimary:lambda^2∣p-1):
    MulChar (Eis⧸Ideal.span {p}) ℂ:=by
  letI:(Ideal.span {p}:Ideal Eis).IsMaximal:=
    PrincipalIdealRing.isMaximal_of_irreducible hp.irreducible
  have hg:lambda∉(Ideal.span {p}:Ideal Eis):=
    primary_maximal_divisor_good p hprimary _ (Ideal.subset_span (by simp))
  refine {toFun:=fun x=>eisEmbedding (symbol (GaussianShiftedPartition.representative p x) p)
          map_one':=?_,map_mul':=?_,map_nonunit':=?_}
  · have hd:p∣GaussianShiftedPartition.representative p 1-1:=by
      simpa only [map_one] using gaussRep_mk_congr p 1
    rw [symbol_congr hd,symbol_one_numerator p hprimary,map_one]
  · intro x y
    have hd:p∣GaussianShiftedPartition.representative p (x*y)-
        GaussianShiftedPartition.representative p x*GaussianShiftedPartition.representative p y:=by
      apply Ideal.mem_span_singleton.mp
      apply (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mp
      simp only [map_mul,GaussianShiftedPartition.representative_spec]
    rw [symbol_congr hd,symbol_mul_numerator _ _ p hprimary,map_mul]
  · intro x hx
    rw [symbol_prime p hp hprimary,primeValue_eq _ hg,
      GaussianShiftedPartition.representative_spec,MulChar.map_nonunit _ hx,map_zero]

lemma primeCubicMulChar_mk (p:Eis) (hp:Prime p) (hprimary:lambda^2∣p-1) (x:Eis):
    primeCubicMulChar p hp hprimary (Ideal.Quotient.mk _ x)=eisEmbedding (symbol x p):=by
  change eisEmbedding (symbol (GaussianShiftedPartition.representative p
    (Ideal.Quotient.mk _ x)) p)=_
  rw [symbol_congr (gaussRep_mk_congr p x)]

lemma quotientTrace_mk_product (c:Eis) (hc:c≠0) (h d:Eis):
    quotientTrace c hc (Ideal.Quotient.mk _ h*Ideal.Quotient.mk _ d)=
      residueAdditive (3*h) c d:=by
  rw [←map_mul,quotientTrace_mk]
  unfold residueAdditive cuspFrequency
  simp only [map_mul,map_one,map_ofNat]
  congr 1
  ring

lemma conductorReduction_prime_power_unit (p:Eis) (n:ℕ)
    (x:Eis⧸Ideal.span {p*p^n}):
    IsUnit (conductorReduction p (p^n) x)↔IsUnit x:=by
  obtain ⟨d,rfl⟩:=Ideal.Quotient.mk_surjective x
  change IsUnit (Ideal.Quotient.mk (Ideal.span {p}) d)↔
    IsUnit (Ideal.Quotient.mk (Ideal.span {p*p^n}) d)
  rw [isUnit_quotient_span_iff,isUnit_quotient_span_iff,←pow_succ',
    IsCoprime.pow_left_iff (Nat.succ_pos n)]

theorem cubicUnitGaussSum_prime_power_fourier (p:Eis) (hp:Prime p)
    (hprimary:lambda^2∣p-1) (n:ℕ) (h:Eis):
    cubicUnitGaussSum h (p^(n+1))=
      conductorFourier p (p^n) hp.ne_zero (pow_ne_zero _ hp.ne_zero)
        (fun x=>(primeCubicMulChar p hp hprimary^(n+1)) x) h:=by
  let χ:=primeCubicMulChar p hp hprimary
  let f:(Eis⧸Ideal.span {p*p^n})→ℂ:=fun x=>
    (χ^(n+1)) (conductorReduction p (p^n) x)*
      quotientTrace (p*p^n) (mul_ne_zero hp.ne_zero (pow_ne_zero _ hp.ne_zero))
        (Ideal.Quotient.mk _ h*x)
  have hsup:Function.support f⊆{x|IsUnit x}:=by
    intro x hx
    by_contra hn
    have hn':¬IsUnit (conductorReduction p (p^n) x):=
      fun hh=>hn ((conductorReduction_prime_power_unit p n x).mp hh)
    exact hx (by dsimp [f];rw [MulChar.map_nonunit _ hn',zero_mul])
  rw [pow_succ']
  change cubicUnitGaussSum h (p*p^n)=∑'x,f x
  rw [←tsum_subtype_eq_of_support_subset hsup]
  unfold cubicUnitGaussSum
  apply tsum_congr
  intro x
  let d:=GaussianShiftedPartition.representative (p*p^n) x.val
  have hd:Ideal.Quotient.mk (Ideal.span {p*p^n}) d=x.val:=
    GaussianShiftedPartition.representative_spec _ _
  change eisEmbedding (symbol d (p*p^n))*residueAdditive (3*h) (p*p^n) d=f x.val
  rw [←hd]
  dsimp [f]
  change _=(χ^(n+1)) (Ideal.Quotient.mk _ d)*_
  rw [MulChar.pow_apply' _ (Nat.succ_ne_zero n),primeCubicMulChar_mk,
    quotientTrace_mk_product,←pow_succ',cubicSymbol_pow_denominator,map_pow]

theorem cubicUnitGaussSum_prime_power_support (p:Eis) (hp:Prime p)
    (hprimary:lambda^2∣p-1) (n:ℕ) (h:Eis)
    (hne:cubicUnitGaussSum h (p^(n+1))≠0):p^n∣h:=by
  rw [cubicUnitGaussSum_prime_power_fourier p hp hprimary n h] at hne
  exact conductorFourier_support p (p^n) hp.ne_zero (pow_ne_zero _ hp.ne_zero) _ h hne

def primeCubicGauss (p:Eis) (hp:Prime p) (hprimary:lambda^2∣p-1)
    (e:ℕ) (h:Eis):ℂ:=
  ∑'x:Eis⧸Ideal.span {p},(primeCubicMulChar p hp hprimary^e) x*
    quotientTrace p hp.ne_zero (Ideal.Quotient.mk _ h*x)


end

open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal
local notation "Eis" => ActualEisensteinCubic.O

lemma primeCubicMulChar_cube (p:Eis) (hp:Prime p) (hprimary:lambda^2∣p-1):
    primeCubicMulChar p hp hprimary^3=1:=by
  apply DFunLike.ext
  intro x
  by_cases hx:IsUnit x
  · obtain ⟨d,rfl⟩:=Ideal.Quotient.mk_surjective x
    rw [MulChar.pow_apply' _ (by decide),primeCubicMulChar_mk,←map_pow,
      symbol_cube_of_isCoprime d p hprimary ((isUnit_quotient_span_iff p d).mp hx).symm,map_one]
    exact (MulChar.one_apply_coe hx.unit).symm
  · rw [MulChar.map_nonunit _ hx,MulChar.map_nonunit _ hx]

lemma primeCubicMulChar_ne_one (p:Eis) (hp:Prime p) (hprimary:lambda^2∣p-1):
    primeCubicMulChar p hp hprimary≠1:=by
  let:(Ideal.span {p}:Ideal Eis).IsMaximal:=
    PrincipalIdealRing.isMaximal_of_irreducible hp.irreducible
  have hg:lambda∉(Ideal.span {p}:Ideal Eis):=
    primary_maximal_divisor_good p hprimary _ (Ideal.subset_span (by simp))
  intro hchar
  apply cubicChar_ne_one (Ideal.span {p}) hg
  apply DFunLike.ext
  intro x
  by_cases hx:IsUnit x
  · obtain ⟨d,rfl⟩:=Ideal.Quotient.mk_surjective x
    have he:=congrArg (fun χ:MulChar (Eis⧸Ideal.span {p}) ℂ=>χ (Ideal.Quotient.mk _ d)) hchar
    rw [primeCubicMulChar_mk,symbol_prime p hp hprimary,primeValue_eq _ hg] at he
    have hoc:(1:MulChar (Eis⧸Ideal.span {p}) ℂ) (Ideal.Quotient.mk _ d)=1:=
      MulChar.one_apply_coe hx.unit
    have hoo:(1:MulChar (Eis⧸Ideal.span {p}) Eis) (Ideal.Quotient.mk _ d)=1:=
      MulChar.one_apply_coe hx.unit
    rw [hoo]
    apply eisEmbedding_injective
    simpa only [hoc,map_one] using he
  · rw [MulChar.map_nonunit _ hx,MulChar.map_nonunit _ hx]

lemma primeCubicMulChar_order (p:Eis) (hp:Prime p) (hprimary:lambda^2∣p-1):
    orderOf (primeCubicMulChar p hp hprimary)=3:=by
  have hd:=orderOf_dvd_of_pow_eq_one (primeCubicMulChar_cube p hp hprimary)
  rcases (Nat.dvd_prime Nat.prime_three).mp hd with h1|h3
  · exact False.elim (primeCubicMulChar_ne_one p hp hprimary (orderOf_eq_one_iff.mp h1))
  · exact h3

lemma primeCubicMulChar_pow_eq_one (p:Eis) (hp:Prime p) (hprimary:lambda^2∣p-1) (e:ℕ):
    primeCubicMulChar p hp hprimary^e=1↔3∣e:=by
  rw [←orderOf_dvd_iff_pow_eq_one,primeCubicMulChar_order]

lemma primeCubicGauss_mod_three (p:Eis) (hp:Prime p) (hprimary:lambda^2∣p-1) (e:ℕ) (h:Eis):
    primeCubicGauss p hp hprimary e h=primeCubicGauss p hp hprimary (e%3) h:=by
  unfold primeCubicGauss
  have he:=pow_mod_orderOf (primeCubicMulChar p hp hprimary) e
  rw [primeCubicMulChar_order] at he
  rw [he]

lemma primeCubicGauss_eq_gaussSum (p:Eis) (hp:Prime p) (hprimary:lambda^2∣p-1)
    (e:ℕ) (h:Eis) [Fintype (Eis⧸Ideal.span {p})]:
    primeCubicGauss p hp hprimary e h=
      gaussSum (primeCubicMulChar p hp hprimary^e)
        ((quotientTrace p hp.ne_zero).mulShift (Ideal.Quotient.mk _ h)):=by
  simp only [primeCubicGauss,tsum_fintype,gaussSum,AddChar.mulShift_apply]

theorem primeCubicGauss_of_dvd (p:Eis) (hp:Prime p) (hprimary:lambda^2∣p-1)
    (e:ℕ) (h:Eis) (hph:p∣h):
    primeCubicGauss p hp hprimary e h=
      if 3∣e then (Ideal.absNorm (Ideal.span {p}):ℂ)-1 else 0:=by
  let:(Ideal.span {p}:Ideal Eis).IsMaximal:=
    PrincipalIdealRing.isMaximal_of_irreducible hp.irreducible
  let:Field (Eis⧸Ideal.span {p}):=Ideal.Quotient.field _
  let:Fintype (Eis⧸Ideal.span {p}):=Fintype.ofFinite _
  have hh:Ideal.Quotient.mk (Ideal.span {p}) h=0:=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton.mpr hph)
  rw [primeCubicGauss_eq_gaussSum,hh,AddChar.mulShift_zero]
  split_ifs with he
  · rw [(primeCubicMulChar_pow_eq_one p hp hprimary e).mpr he,gaussSum_one_one,
      Nat.card_units,Nat.cast_sub (Nat.succ_le_of_lt Nat.card_pos),Nat.cast_one]
    rfl
  · exact gaussSum_one_right (fun hχ=>he ((primeCubicMulChar_pow_eq_one p hp hprimary e).mp hχ))

theorem primeCubicGauss_trivial_nonzero (p:Eis) (hp:Prime p) (hprimary:lambda^2∣p-1)
    (e:ℕ) (he:3∣e) (h:Eis) (hph:¬p∣h):
    primeCubicGauss p hp hprimary e h=-1:=by
  let:(Ideal.span {p}:Ideal Eis).IsMaximal:=
    PrincipalIdealRing.isMaximal_of_irreducible hp.irreducible
  let:Field (Eis⧸Ideal.span {p}):=Ideal.Quotient.field _
  let:Fintype (Eis⧸Ideal.span {p}):=Fintype.ofFinite _
  have hh:Ideal.Quotient.mk (Ideal.span {p}) h≠0:=by
    intro hh
    exact hph (Ideal.mem_span_singleton.mp (Ideal.Quotient.eq_zero_iff_mem.mp hh))
  rw [primeCubicGauss_eq_gaussSum,(primeCubicMulChar_pow_eq_one p hp hprimary e).mpr he]
  exact gaussSum_one_left (GeneralPrimitiveTrace.eisTraceModChar_breveE_primitive p hp.ne_zero hh)

theorem primeCubicGauss_one_mul_two (p:Eis) (hp:Prime p) (hprimary:lambda^2∣p-1)
    (h:Eis) (hph:¬p∣h):
    primeCubicGauss p hp hprimary 1 h*primeCubicGauss p hp hprimary 2 h=
      (Ideal.absNorm (Ideal.span {p}):ℂ):=by
  let:(Ideal.span {p}:Ideal Eis).IsMaximal:=
    PrincipalIdealRing.isMaximal_of_irreducible hp.irreducible
  let:Field (Eis⧸Ideal.span {p}):=Ideal.Quotient.field _
  let:Fintype (Eis⧸Ideal.span {p}):=Fintype.ofFinite _
  have hh:Ideal.Quotient.mk (Ideal.span {p}) h≠0:=by
    intro hh
    exact hph (Ideal.mem_span_singleton.mp (Ideal.Quotient.eq_zero_iff_mem.mp hh))
  have hψ:((quotientTrace p hp.ne_zero).mulShift (Ideal.Quotient.mk _ h)).IsPrimitive:=
    AddChar.IsPrimitive.of_ne_one (GeneralPrimitiveTrace.eisTraceModChar_breveE_primitive p hp.ne_zero hh)
  have he:=gaussSum_mul_gaussSum_pow_orderOf_sub_one
    (primeCubicMulChar_ne_one p hp hprimary) hψ
  rw [primeCubicMulChar_order] at he
  have hm:=MulChar.val_neg_one_eq_one_of_odd_order (by decide:Odd 3)
    (primeCubicMulChar_cube p hp hprimary)
  rw [hm,one_mul] at he
  change _=(Nat.card (Eis⧸Ideal.span {p}):ℂ)
  simpa only [primeCubicGauss_eq_gaussSum,pow_one,Nat.reduceSub,
    Nat.card_eq_fintype_card] using he


end CubicEisenstein

end

end OAI

end


