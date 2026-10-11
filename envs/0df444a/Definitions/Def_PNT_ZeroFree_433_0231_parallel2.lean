-- Prove2me | Definitions.Def_PNT_ZeroFree_433_0231_parallel2
-- name    : PNT_ZeroFree_433_0231_parallel2
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-11T11:34:55.788898+00:00
-- url     : https://prove2.me/theorems/7d331dab-3004-4c29-9d66-587a968fd19d
-- title:
--   Zero-free region foundations: Eisenstein.ResidualCuspDecay [0231_parallel2]
-- statement:
--   Definitions and proved supporting lemmas from the following source modules:
--
--   - OAI.NumberTheory.DirichletL.Eisenstein.ResidualCuspDecay
--
--   These declarations form part of the analytic and arithmetic foundations of the Dirichlet L-function nonvanishing argument in the half-plane Re(s) > 7/8. The original namespaces and hypotheses are retained. The code is ported to Lean 4.33.1 and the pinned Mathlib environment; every included lemma has a complete proof.
-- source:
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Eisenstein/ResidualCuspDecay.lean#L257-L611

import Definitions.Def_PNT_ZeroFree_433_0004
import Definitions.Def_PNT_ZeroFree_433_0007
import Definitions.Def_PNT_ZeroFree_433_0009
import Definitions.Def_PNT_ZeroFree_433_0017
import Definitions.Def_PNT_ZeroFree_433_0048
import Definitions.Def_PNT_ZeroFree_433_0062
import Definitions.Def_PNT_ZeroFree_433_0067
import Definitions.Def_PNT_ZeroFree_433_0071
import Definitions.Def_PNT_ZeroFree_433_0074
import Definitions.Def_PNT_ZeroFree_433_0075
import Definitions.Def_PNT_ZeroFree_433_0085
import Definitions.Def_PNT_ZeroFree_433_0093
import Definitions.Def_PNT_ZeroFree_433_0094
import Definitions.Def_PNT_ZeroFree_433_0096
import Definitions.Def_PNT_ZeroFree_433_0145_parallel1
import Definitions.Def_PNT_ZeroFree_433_0217_parallel1
import Definitions.Def_PNT_ZeroFree_433_0217_parallel2
import Definitions.Def_PNT_ZeroFree_433_0229_parallel1
import Definitions.Def_PNT_ZeroFree_433_0231_parallel1
import Definitions.Def_PNT_ZeroFree_433_0242_parallel1

/- Supporting zero-free-region lemmas, grouped by independent dependencies.
https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Eisenstein/ResidualCuspDecay.lean
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


namespace ShortDraftCRT
open scoped BigOperators Classical Matrix

section
variable {R : Type*} [CommRing R]


variable [IsDomain R]

theorem fixed_ray_completion_in_sector (M a c : R) (rows rows0 : List (R×R))
    (b0 d0 : R) (hc0 : c≠0) (hc : c∣M)
    (hbase : IsCoprime a c) (hrows : GoodRows c rows)
    (hr : IsCoprime (rows.map Prod.fst).prod (M*c))
    (hlift : ∀ph∈rows,M^2∣ph.2) (hlift0 : ∀ph∈rows0,M^2∣ph.2)
    (hsector : M^2∣(rows.map Prod.fst).prod-(rows0.map Prod.fst).prod)
    (hdet0 : crossNum a c rows0*d0-b0*crossDen c rows0=1) :
    ∃b d : R, crossNum a c rows*d-b*crossDen c rows=1 ∧ M*c∣d-d0 ∧
      (!![crossNum a c rows,b;crossDen c rows,d] : Matrix (Fin 2) (Fin 2) R).map
          (Ideal.Quotient.mk (Ideal.span {M})) =
        (!![crossNum a c rows0,b0;crossDen c rows0,d0] : Matrix (Fin 2) (Fin 2) R).map
          (Ideal.Quotient.mk (Ideal.span {M})) := by
  have hn := crossNum_fixed_sector_congr M a c rows rows0 hc hlift hlift0 hsector
  have hrmod : M∣(rows.map Prod.fst).prod-(rows0.map Prod.fst).prod :=
    (show M∣M^2 by simpa only [pow_two] using (dvd_mul_right M M)).trans hsector
  have hcop := coprime_cross_num_list a c rows hbase hrows
  rw [crossDen_eq_product] at hcop hdet0 ⊢
  obtain ⟨b,d,hd,hdd,hmat⟩ := exists_fixed_matrix_completion M c
    (crossNum a c rows0) (rows0.map Prod.fst).prod d0 b0 hc0 hdet0
    (crossNum a c rows) (rows.map Prod.fst).prod hn hrmod hr hcop.of_mul_right_right
  refine ⟨b,d,hd,hdd,?_⟩
  simpa only [crossDen_eq_product] using hmat

end

variable {R : Type*} [CommRing R] [IsDomain R]

theorem exists_sectorwise_completions {ι Q : Type*} (M c : R) (hc : c≠0)
    (sector : ι→Q) (a r : ι→R)
    (hcop : ∀i,IsCoprime (a i) (c*r i))
    (hr : ∀i,IsCoprime (r i) (M*c))
    (ha : ∀i j,sector i=sector j → M*c∣a i-a j)
    (hrr : ∀i j,sector i=sector j → M∣r i-r j) :
    ∃(b d : ι→R) (C : Q→Matrix (Fin 2) (Fin 2) (R⧸Ideal.span {M})),
      (∀i,a i*d i-b i*(c*r i)=1) ∧
      ∀i,(!![a i,b i;c*r i,d i] : Matrix (Fin 2) (Fin 2) R).map
        (Ideal.Quotient.mk (Ideal.span {M}))=C (sector i) := by
  have hlocal (q : Q) :
      ∃C : Matrix (Fin 2) (Fin 2) (R⧸Ideal.span {M}),
        ∀i,sector i=q → ∃b d : R,a i*d-b*(c*r i)=1 ∧
          (!![a i,b;c*r i,d] : Matrix (Fin 2) (Fin 2) R).map
            (Ideal.Quotient.mk (Ideal.span {M}))=C := by
    by_cases hq : ∃i,sector i=q
    · obtain ⟨j,hj⟩ := hq
      obtain ⟨x,y,hxy⟩ := hcop j
      have hdet : a j*x-(-y)*(c*r j)=1 := by linear_combination hxy
      refine ⟨(!![a j,-y;c*r j,x] : Matrix (Fin 2) (Fin 2) R).map
        (Ideal.Quotient.mk (Ideal.span {M})),?_⟩
      intro i hi
      have hs : sector i=sector j := hi.trans hj.symm
      obtain ⟨b,d,hd,_,he⟩ := exists_fixed_matrix_completion M c (a j) (r j) x (-y)
        hc hdet (a i) (r i) (ha i j hs) (hrr i j hs) (hr i) (hcop i).of_mul_right_right
      exact ⟨b,d,hd,he⟩
    · refine ⟨0,?_⟩
      intro i hi
      exact False.elim (hq ⟨i,hi⟩)
  choose C hC using hlocal
  have hi (i : ι) := hC (sector i) i rfl
  choose b d hd he using hi
  exact ⟨b,d,C,hd,he⟩


theorem exists_uniform_cusp_completions (M a c : R) (hc0 : c≠0)
    (hc : c∣M) (hbase : IsCoprime a c) :
    ∃(b d : LiftedRows M c→R)
      (C : (R⧸Ideal.span {M^2})→Matrix (Fin 2) (Fin 2) (R⧸Ideal.span {M})),
      (∀i,crossNum a c i.val*d i-b i*crossDen c i.val=1) ∧
      ∀i,(!![crossNum a c i.val,b i;crossDen c i.val,d i] : Matrix (Fin 2) (Fin 2) R).map
        (Ideal.Quotient.mk (Ideal.span {M}))=
        C (Ideal.Quotient.mk (Ideal.span {M^2}) (i.val.map Prod.fst).prod) := by
  let sector : LiftedRows M c→R⧸Ideal.span {M^2} :=
    fun i=>Ideal.Quotient.mk (Ideal.span {M^2}) (i.val.map Prod.fst).prod
  have hsector (i j : LiftedRows M c) (hs : sector i=sector j) :
      M^2∣(i.val.map Prod.fst).prod-(j.val.map Prod.fst).prod :=
    Ideal.mem_span_singleton.mp (Ideal.Quotient.eq.mp hs)
  obtain ⟨b,d,C,hd,he⟩ := exists_sectorwise_completions M c hc0 sector
    (fun i=>crossNum a c i.val) (fun i=>(i.val.map Prod.fst).prod)
    (fun i=>by
      simpa only [←crossDen_eq_product] using coprime_cross_num_list a c i.val hbase i.property.1)
    (fun i=>i.property.2.2)
    (fun i j hs=>crossNum_fixed_sector_congr M a c i.val j.val hc
      i.property.2.1 j.property.2.1 (hsector i j hs))
    (fun i j hs=>(show M∣M^2 by simpa only [pow_two] using dvd_mul_right M M).trans
      (hsector i j hs))
  refine ⟨b,d,C,?_,?_⟩
  · intro i
    simpa only [crossDen_eq_product] using hd i
  · intro i
    simpa only [crossDen_eq_product,sector] using he i

theorem eisenstein_uniform_cusp_completions
    (M a c : ActualEisensteinCubic.O) (hM : M≠0) (hc0 : c≠0)
    (hc : c∣M) (hbase : IsCoprime a c) :
    ∃(b d : LiftedRows M c→ActualEisensteinCubic.O)
      (S : Set (Matrix (Fin 2) (Fin 2) (ActualEisensteinCubic.O⧸Ideal.span {M}))),
      S.Finite ∧ S.ncard≤Ideal.absNorm (Ideal.span {M^2}) ∧
      (∀i,crossNum a c i.val*d i-b i*crossDen c i.val=1) ∧
      ∀i,(!![crossNum a c i.val,b i;crossDen c i.val,d i] :
        Matrix (Fin 2) (Fin 2) ActualEisensteinCubic.O).map
          (Ideal.Quotient.mk (Ideal.span {M}))∈S := by
  let : Finite (ActualEisensteinCubic.O⧸Ideal.span {M^2}) :=
    ConcreteTraceCRT.finite_quotient_span (pow_ne_zero _ hM)
  obtain ⟨b,d,C,hd,he⟩ := exists_uniform_cusp_completions M a c hc0 hc hbase
  refine ⟨b,d,Set.range C,Set.finite_range C,?_,hd,?_⟩
  · have hh := Set.ncard_image_le (s := Set.univ) (f := C)
    simpa only [Set.image_univ,Set.ncard_univ,Ideal.absNorm_apply,
      Submodule.cardQuot_apply] using hh
  · intro i
    exact ⟨_,(he i).symm⟩

end ShortDraftCRT

open scoped BigOperators Classical


open scoped BigOperators Classical
namespace CubicEisenstein
open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal CompletedGauss
open PrimaryIdealUnitReindex (GoodIdeal)
local notation "Eis" => ActualEisensteinCubic.O

lemma cubicUnitGaussSum_norm_le (h c:Eis) (hc:c≠0) (hp:lambda^2∣c-1):
    ‖cubicUnitGaussSum h c‖≤Ideal.absNorm (Ideal.span {c}):=by
  let:Finite (Eis⧸Ideal.span {c}):=finite_quotient_span hc
  let:Fintype (Eis⧸Ideal.span {c}):=Fintype.ofFinite _
  let:Fintype (CubicUnitResidue c):=Fintype.ofFinite _
  have hs (r:CubicUnitResidue c):
      ‖eisEmbedding (symbol (GaussianShiftedPartition.representative c r.val) c)‖=1:=by
    apply Complex.norm_eq_one_of_pow_eq_one (n:=3) _ (by decide)
    rw [←map_pow,symbol_cube_of_isCoprime _ c hp _ ,map_one]
    apply IsCoprime.symm
    apply (isUnit_quotient_span_iff c _).mp
    simpa only [GaussianShiftedPartition.representative_spec] using r.2
  rw [cubicUnitGaussSum,tsum_fintype]
  calc
    _≤∑r:CubicUnitResidue c,‖eisEmbedding (symbol (GaussianShiftedPartition.representative c r.val) c)*
      residueAdditive (3*h) c (GaussianShiftedPartition.representative c r.val)‖:=norm_sum_le _ _
    _=(Fintype.card (CubicUnitResidue c):ℝ):=by
      simp only [norm_mul,hs,residueAdditive,breveE_norm,
        Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one]
    _≤(Fintype.card (Eis⧸Ideal.span {c}):ℝ):=by
      exact_mod_cast Fintype.card_subtype_le (fun r=>IsUnit r)
    _=Ideal.absNorm (Ideal.span {c}):=by
      simp only [Ideal.absNorm_apply,Submodule.cardQuot_apply,Nat.card_eq_fintype_card]

theorem unramifiedCubicGaussSeries_summable_norm (s:ℂ) (hs:2<s.re) (h:Eis):
    Summable (fun I:GoodIdeal=>‖(Ideal.absNorm I.val:ℂ)^(-s)*
      cubicUnitGaussSum h (primaryGenerator I.val)‖):=by
  have hs':1<(s-1).re:=by simp only [Complex.sub_re,Complex.one_re];linarith
  apply ((unramifiedNormWeight_summable_norm (s-1) hs').subtype
    (fun I:Ideal Eis=>primaryGenerator I≠0)).of_nonneg_of_le (fun _=>norm_nonneg _)
  intro I
  dsimp only [Function.comp_def]
  simp only [unramifiedNormWeight_shift,norm_mul,Complex.norm_natCast,
    unramifiedNormWeight_of_good s I.val I.2]
  have hg:=cubicUnitGaussSum_norm_le h (primaryGenerator I.val) I.2
    (primaryGenerator_spec I.val I.2).2
  rw [(primaryGenerator_spec I.val I.2).1] at hg
  nlinarith [norm_nonneg ((Ideal.absNorm I.val:ℂ)^(-s))]


def unramifiedPrimeDeletedSeries (p:Eis) (s:ℂ) (h:Eis):ℂ:=
  ∑'I:PrimeDeletedIdeal p,(Ideal.absNorm I.val.val:ℂ)^(-s)*
    cubicUnitGaussSum h (primaryGenerator I.val.val)


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

end


