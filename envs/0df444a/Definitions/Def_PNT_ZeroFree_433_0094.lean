-- Prove2me | Definitions.Def_PNT_ZeroFree_433_0094
-- name    : PNT_ZeroFree_433_0094
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-11T11:22:08.524994+00:00
-- url     : https://prove2.me/theorems/d7b0955e-68f8-45c0-8933-16603694aac4
-- title:
--   Zero-free region foundations: Eisenstein.RamifiedNormWeights [0094]
-- statement:
--   Definitions and proved supporting lemmas from the following source modules:
--
--   - OAI.NumberTheory.DirichletL.Eisenstein.RamifiedNormWeights
--
--   These declarations form part of the analytic and arithmetic foundations of the Dirichlet L-function nonvanishing argument in the half-plane Re(s) > 7/8. The original namespaces and hypotheses are retained. The code is ported to Lean 4.33.1 and the pinned Mathlib environment; every included lemma has a complete proof.
-- source:
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Eisenstein/RamifiedNormWeights.lean#L79-L638

import Definitions.Def_PNT_ZeroFree_433_0093

/- Supporting source modules for the zero-free-region proof.
Ported and checked against Lean 4.33.1 / Mathlib 0df444a.
Original source attribution:
https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Eisenstein/RamifiedNormWeights.lean#L79-L638
-/

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

-- Source module: OAI.NumberTheory.DirichletL.Eisenstein.RamifiedNormWeights
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

open scoped BigOperators Classical

namespace CubicEisenstein

open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal

private def predicateFiberEquiv {R S : Type*} (f : R → S) (P : S → Prop) :
    {x : R // P (f x)} ≃ Σ y : {y : S // P y}, {x : R // f x=y.1} where
  toFun x := ⟨⟨f x.1,x.2⟩,⟨x.1,rfl⟩⟩
  invFun y := ⟨y.2.1,by rw [y.2.2]; exact y.1.2⟩
  left_inv x := rfl
  right_inv y := by
    rcases y with ⟨⟨y,hy⟩,x,hx⟩
    dsimp at hx
    cases hx
    rfl

private def predicateKernelEquiv {R S : Type*} [AddGroup R] [AddGroup S]
    (f : R →+ S) (hf : Function.Surjective f) (P : S → Prop) :
    {x : R // P (f x)} ≃ {y : S // P y} × f.ker :=
  (predicateFiberEquiv f P).trans
    ((Equiv.sigmaCongrRight (fun y : {y : S // P y} =>
      AddMonoidHom.fiberEquivKerOfSurjective hf y.1)).trans (Equiv.sigmaEquivProd _ _))

lemma card_ring_eq_card_mul_kernel {R S : Type*} [Ring R] [Ring S]
    (f : R →+* S) (hf : Function.Surjective f) :
    Nat.card R=Nat.card S*Nat.card f.toAddMonoidHom.ker := by
  have h := Nat.card_congr (predicateKernelEquiv f.toAddMonoidHom hf (fun _ => True))
  simpa only [Nat.card_prod,Nat.card_congr (Equiv.subtypeUnivEquiv (fun _ => True.intro))] using h

lemma card_units_eq_card_mul_kernel {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (hf : Function.Surjective f)
    (hunit : ∀x, IsUnit (f x) ↔ IsUnit x) :
    Nat.card Rˣ=Nat.card Sˣ*Nat.card f.toAddMonoidHom.ker := by
  let e : Rˣ ≃ {x : R // IsUnit (f x)} :=
    (unitsSubtypeEquiv R).trans (Equiv.subtypeEquivRight (fun x => (hunit x).symm))
  calc
    _ = Nat.card ({y : S // IsUnit y} × f.toAddMonoidHom.ker) :=
      Nat.card_congr (e.trans (predicateKernelEquiv f.toAddMonoidHom hf IsUnit))
    _ = Nat.card {y : S // IsUnit y} * Nat.card f.toAddMonoidHom.ker := Nat.card_prod _ _
    _ = _ := by rw [← Nat.card_congr (unitsSubtypeEquiv S)]

lemma card_units_mul_card_target {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (hf : Function.Surjective f)
    (hunit : ∀x, IsUnit (f x) ↔ IsUnit x) :
    Nat.card S*Nat.card Rˣ=Nat.card R*Nat.card Sˣ := by
  rw [card_units_eq_card_mul_kernel f hf hunit,card_ring_eq_card_mul_kernel f hf]
  ring

theorem idealTotient_pow_succ (I : Ideal O) (hI : I ≠ 0) (n : ℕ) :
    idealTotient (I^(n+1))=Ideal.absNorm I^n*idealTotient I := by
  let f : (O ⧸ I^(n+1)) →+* (O ⧸ I) :=
    Ideal.Quotient.factor (Ideal.pow_le_self (Nat.succ_ne_zero n))
  have hf : Function.Surjective f := Ideal.Quotient.factor_surjective _
  have hu (x : O ⧸ I^(n+1)) : IsUnit (f x) ↔ IsUnit x := by
    obtain ⟨x,rfl⟩ := Ideal.Quotient.mk_surjective x
    exact (Ideal.Quotient.isUnit_mk_pow_iff_isUnit_mk I (Nat.succ_ne_zero n)).symm
  have h := card_units_mul_card_target f hf hu
  change Ideal.absNorm I*idealTotient (I^(n+1))=
    Ideal.absNorm (I^(n+1))*idealTotient I at h
  rw [map_pow] at h
  have hpos : 0<Ideal.absNorm I := Nat.pos_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hI)
  apply Nat.eq_of_mul_eq_mul_left hpos
  calc
    _ = Ideal.absNorm I^(n+1)*idealTotient I := h
    _ = _ := by ring

theorem idealTotient_cube (I : Ideal O) (hI : I ≠ 0) :
    idealTotient (I^3)=Ideal.absNorm I^2*idealTotient I :=
  idealTotient_pow_succ I hI 2

def unitsRingEquiv {R S : Type*} [Monoid R] [Monoid S] (e : R ≃* S) : Rˣ ≃ Sˣ :=
  (unitsSubtypeEquiv R).trans
    ((e.toEquiv.subtypeEquiv (fun _x => (MulEquiv.isUnit_map e).symm)).trans
      (unitsSubtypeEquiv S).symm)

theorem idealTotient_mul (I J : Ideal O) (hIJ : IsCoprime I J) :
    idealTotient (I*J)=idealTotient I*idealTotient J := by
  change Nat.card (O ⧸ I*J)ˣ=Nat.card (O ⧸ I)ˣ*Nat.card (O ⧸ J)ˣ
  calc
    _ = Nat.card ((O ⧸ I)ˣ × (O ⧸ J)ˣ) :=
      Nat.card_congr ((unitsRingEquiv
        (Ideal.quotientMulEquivQuotientProd I J hIJ).toMulEquiv).trans MulEquiv.prodUnits.toEquiv)
    _ = _ := Nat.card_prod _ _

theorem card_admissible_cube_product (n : ℕ) (a : O) (ha : a ≠ 0)
    (hcop : IsCoprime a (3:O)) :
    Nat.card (AdmissibleResidue (lambda^(3*n)*a^3)) =
      3^(3*n)*Ideal.absNorm (Ideal.span {a})^2*idealTotient (Ideal.span {a}) := by
  rw [card_admissible_lambda_pow_mul (3*n) (a^3) hcop.pow_left,
    ← Ideal.span_singleton_pow,idealTotient_cube _ (Ideal.span_singleton_eq_bot.not.mpr ha)]
  ring

section
open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal UniqueFactorizationMonoid
open IdealMobiusDivisorSum (idealDivisors mem_idealDivisors sum_moebius_divisors)

lemma isUnit_quotient_iff_sup (I : Ideal O) (x : O) :
    IsUnit (Ideal.Quotient.mk I x) ↔ I ⊔ Ideal.span {x}=⊤ := by
  constructor
  · intro hx
    obtain ⟨b,hb⟩ := isUnit_iff_exists_inv.mp hx
    obtain ⟨b,rfl⟩ := Ideal.Quotient.mk_surjective b
    have hI : x*b-1 ∈ I := by
      apply Ideal.Quotient.eq_zero_iff_mem.mp
      simpa only [map_sub,map_mul,map_one,sub_eq_zero] using hb
    apply (Ideal.eq_top_iff_one _).mpr
    have hx' : x*b ∈ I ⊔ Ideal.span {x} :=
      (le_sup_right : Ideal.span {x} ≤ I ⊔ Ideal.span {x})
        ((Ideal.span {x}).mul_mem_right b (Ideal.subset_span (by simp)))
    convert! (I ⊔ Ideal.span {x}).sub_mem hx' ((le_sup_left : I ≤ I ⊔ Ideal.span {x}) hI) using 1 ; ring
  · intro h
    have h1 : (1:O) ∈ I ⊔ Ideal.span {x} := by rw [h]; trivial
    obtain ⟨a,ha,b,hb,hab⟩ := Submodule.mem_sup.mp h1
    obtain ⟨k,rfl⟩ := Ideal.mem_span_singleton.mp hb
    apply isUnit_iff_exists_inv.mpr
    refine ⟨Ideal.Quotient.mk I k, ?_⟩
    have ha0 := Ideal.Quotient.eq_zero_iff_mem.mpr ha
    have hh := congrArg (Ideal.Quotient.mk I) hab
    simpa only [map_add,map_mul,map_one,ha0,zero_add] using hh

lemma residue_unit_mobius (I : Ideal O) (hI : I ≠ 0) (r : O ⧸ I) :
    (if IsUnit r then (1:ℂ) else 0) =
      ∑ J ∈ idealDivisors I, if Quotient.out r ∈ J then (moebius J:ℂ) else 0 := by
  let G : Ideal O := I ⊔ Ideal.span {Quotient.out r}
  have hG : G ≠ 0 := by
    intro hG
    apply hI
    apply le_antisymm _ bot_le
    calc
      I ≤ G := le_sup_left
      _ = ⊥ := hG
  have hdiv : (idealDivisors I).filter (fun J => Quotient.out r ∈ J)=idealDivisors G := by
    ext J
    simp only [Finset.mem_filter,mem_idealDivisors hI,mem_idealDivisors hG,
      Ideal.dvd_iff_le,G,sup_le_iff,Ideal.span_le,Set.singleton_subset_iff,SetLike.mem_coe]
  rw [← Finset.sum_filter,hdiv,sum_moebius_divisors G hG]
  have hu : IsUnit r ↔ G=⊤ := by
    rw [← Ideal.Quotient.mk_out r]
    exact isUnit_quotient_iff_sup I (Quotient.out r)
  simp only [hu]

lemma sum_indicator_const {R : Type*} [Fintype R] (P : R → Prop) (z : ℂ) :
    (∑ r : R, if P r then z else 0)=(Nat.card {r : R // P r}:ℂ)*z := by
  rw [← Finset.sum_filter]
  simp only [Finset.sum_const,nsmul_eq_mul,Nat.card_eq_fintype_card,Fintype.card_subtype]

lemma card_quotient_multiples (I J : Ideal O) (hI : I ≠ 0) (hIJ : I ≤ J) :
    (Nat.card {r : O ⧸ I // Quotient.out r ∈ J}:ℂ)=
      (Ideal.absNorm I:ℂ)/(Ideal.absNorm J:ℂ) := by
  let f : (O ⧸ I) →+* (O ⧸ J) := Ideal.Quotient.factor hIJ
  have hf : Function.Surjective f := Ideal.Quotient.factor_surjective hIJ
  have hpred (r : O ⧸ I) : Quotient.out r ∈ J ↔ f r=0 := by
    have hfr : f r=Ideal.Quotient.mk J (Quotient.out r) := by
      calc
        f r = f (Ideal.Quotient.mk I (Quotient.out r)) :=
          congrArg f (Ideal.Quotient.mk_out r).symm
        _ = _ := Ideal.Quotient.factor_mk hIJ _
    rw [← Ideal.Quotient.eq_zero_iff_mem,hfr]
  let e : {r : O ⧸ I // Quotient.out r ∈ J} ≃ f.toAddMonoidHom.ker :=
    Equiv.subtypeEquivRight hpred
  have hcard := card_ring_eq_card_mul_kernel f hf
  have hJ : J ≠ 0 := fun h => hI (le_antisymm (h ▸ hIJ) bot_le)
  have hnJ : (Ideal.absNorm J:ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hJ)
  rw [Nat.card_congr e]
  apply (eq_div_iff hnJ).mpr
  have hh : Nat.card f.toAddMonoidHom.ker * Ideal.absNorm J = Ideal.absNorm I :=
    (Nat.mul_comm _ _).trans hcard.symm
  exact_mod_cast hh

theorem idealTotient_moebius (I : Ideal O) (hI : I ≠ 0) :
    (idealTotient I:ℂ)=(Ideal.absNorm I:ℂ)*
      ∑ J ∈ idealDivisors I, (moebius J:ℂ)/(Ideal.absNorm J:ℂ) := by
  let : Finite (O ⧸ I) := I.finiteQuotientOfFreeOfNeBot hI
  let : Fintype (O ⧸ I) := Fintype.ofFinite _
  classical
  have hcount : (idealTotient I:ℂ)=∑ r : O ⧸ I,
      @ite ℂ (IsUnit r) (Classical.propDecidable _) 1 0 := by
    have h := sum_indicator_const (R := O ⧸ I) IsUnit (1:ℂ)
    rw [mul_one] at h
    calc
      _ = (Nat.card {r : O ⧸ I // IsUnit r}:ℂ) := by
        exact_mod_cast Nat.card_congr (unitsSubtypeEquiv (O ⧸ I))
      _ = _ := h.symm
  rw [hcount]
  have hs : (∑ r : O ⧸ I, @ite ℂ (IsUnit r) (Classical.propDecidable _) 1 0) =
      ∑ r : O ⧸ I, ∑ J ∈ idealDivisors I,
        if Quotient.out r ∈ J then (moebius J:ℂ) else 0 := by
    apply Finset.sum_congr rfl
    intro r hr
    exact residue_unit_mobius I hI r
  rw [hs]
  rw [Finset.sum_comm]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro J hJ
  rw [sum_indicator_const,card_quotient_multiples I J hI
    (Ideal.dvd_iff_le.mp ((mem_idealDivisors hI).mp hJ))]
  ring

end

section
open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal UniqueFactorizationMonoid CompletedGauss
open PrimaryIdealUnitReindex (GoodIdeal)

def unramifiedNormWeight (s : ℂ) : Ideal O →*₀ ℂ where
  toFun I := if primaryGenerator I=0 then 0 else (Ideal.absNorm I:ℂ)^(-s)
  map_zero' := by simp
  map_one' := by
    rw [primaryGenerator_one,if_neg one_ne_zero,map_one,Nat.cast_one,Complex.one_cpow]
  map_mul' I J := by
    by_cases hI : primaryGenerator I=0
    · simp [primaryGenerator_mul,hI]
    by_cases hJ : primaryGenerator J=0
    · simp [primaryGenerator_mul,hJ]
    simp only [primaryGenerator_mul,mul_eq_zero,hI,hJ,false_or,ite_false,map_mul,Nat.cast_mul]
    exact Complex.natCast_mul_natCast_cpow _ _ _

lemma unramifiedNormWeight_of_good (s : ℂ) (I : Ideal O) (hI : primaryGenerator I ≠ 0) :
    unramifiedNormWeight s I=(Ideal.absNorm I:ℂ)^(-s) := if_neg hI

lemma unramifiedNormWeight_of_bad (s : ℂ) (I : Ideal O) (hI : primaryGenerator I=0) :
    unramifiedNormWeight s I=0 := if_pos hI

lemma primaryGenerator_injective_good :
    Function.Injective (fun I : GoodIdeal => primaryGenerator I.1) := by
  intro I J h
  dsimp only at h
  apply Subtype.ext
  rw [← (primaryGenerator_spec I.1 I.2).1,← (primaryGenerator_spec J.1 J.2).1,h]

lemma norm_unramifiedNormWeight (s : ℂ) (I : GoodIdeal) :
    ‖unramifiedNormWeight s I.1‖=‖eisEmbedding (primaryGenerator I.1)‖^(-2*s.re) := by
  rw [unramifiedNormWeight_of_good s I.1 I.2]
  have hnorm : ‖eisEmbedding (primaryGenerator I.1)‖^2=(Ideal.absNorm I.1:ℝ) := by
    rw [eisEmbedding_norm_sq_eq_absNorm_span,(primaryGenerator_spec I.1 I.2).1]
  have hn : 0<‖eisEmbedding (primaryGenerator I.1)‖ :=
    norm_pos_iff.mpr (eisEmbedding_ne_zero I.2)
  have hcast : (Ideal.absNorm I.1:ℂ)=((‖eisEmbedding (primaryGenerator I.1)‖^2:ℝ):ℂ) := by
    exact_mod_cast hnorm.symm
  rw [hcast,Complex.norm_cpow_eq_rpow_re_of_pos (sq_pos_of_pos hn)]
  rw [← Real.rpow_natCast_mul hn.le 2]
  congr 1
  simp only [Complex.neg_re,Nat.cast_ofNat]
  ring

theorem unramifiedNormWeight_summable_norm (s : ℂ) (hs : 1<s.re) :
    Summable (fun I : Ideal O => ‖unramifiedNormWeight s I‖) := by
  have hlat := (summable_embedding_rpow (-2*s.re) (by linarith)).comp_injective
    primaryGenerator_injective_good
  have hsub : Summable (fun I : GoodIdeal => ‖unramifiedNormWeight s I.1‖) := by
    simpa only [Function.comp_def, norm_unramifiedNormWeight] using hlat
  have hind := (summable_subtype_iff_indicator (s := {I : Ideal O | primaryGenerator I ≠ 0})
    (f := fun I => ‖unramifiedNormWeight s I‖)).mp hsub
  apply hind.congr
  intro I
  by_cases hI : primaryGenerator I=0
  · simp [Set.indicator,hI,unramifiedNormWeight_of_bad s I hI]
  · simp [Set.indicator,hI]

lemma norm_ideal_moebius_le_one (I : Ideal O) : ‖(moebius I:ℂ)‖≤1 := by
  by_cases hI : Squarefree I
  · simp [hI.moebius_eq]
  · simp [moebius_of_not_squarefree hI]

lemma moebius_unramifiedNormWeight_summable_norm (s : ℂ) (hs : 1<s.re) :
    Summable (fun I : Ideal O => ‖(moebius I:ℂ)*unramifiedNormWeight s I‖) := by
  apply (unramifiedNormWeight_summable_norm s hs).of_nonneg_of_le (fun _ => norm_nonneg _)
  intro I
  rw [norm_mul]
  exact mul_le_of_le_one_left (norm_nonneg _) (norm_ideal_moebius_le_one I)

def unramifiedIdealZeta (s : ℂ) : ℂ := ∑' I : Ideal O, unramifiedNormWeight s I

def unramifiedMobiusSeries (s : ℂ) : ℂ :=
  ∑' I : Ideal O, (moebius I:ℂ)*unramifiedNormWeight s I

end

open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal UniqueFactorizationMonoid CompletedGauss
open IdealMobiusDivisorSum (idealDivisors mem_idealDivisors sum_moebius_divisors)

theorem unramifiedMobiusSeries_mul_zeta (s : ℂ) (hs : 1<s.re) :
    unramifiedMobiusSeries s*unramifiedIdealZeta s=1 := by
  let F : Ideal O × Ideal O → ℂ := fun p =>
    (moebius p.1:ℂ)*unramifiedNormWeight s (p.1*p.2)
  have hprod := (moebius_unramifiedNormWeight_summable_norm s hs).mul_norm
    (unramifiedNormWeight_summable_norm s hs)
  have hF : Summable F := by
    apply hprod.of_norm.congr
    intro p
    dsimp only [F]
    rw [map_mul]
    ring
  have hfiber (B : Ideal O) : (∑' p : MulFiber B,F p.1)=if B=1 then 1 else 0 := by
    by_cases hB : B=0
    · subst B
      have hz (p : MulFiber 0) : F p.1=0 := by simp only [F,p.2,map_zero,mul_zero]
      simp only [hz,tsum_zero,zero_ne_one,ite_false]
    · calc
        _ = (∑' p : MulFiber B,(moebius p.1.1:ℂ))*unramifiedNormWeight s B := by
          rw [← tsum_mul_right]
          apply tsum_congr
          intro p
          simp only [F,p.2]
        _ = _ := by
          rw [mulFiber_moebius_sum B hB]
          split_ifs with hB1
          · subst B; simp only [map_one,mul_one]
          · simp only [zero_mul]
  have hsum := hF.hasSum.tsum_fiberwise (fun p : Ideal O × Ideal O => p.1*p.2)
  change HasSum (fun B : Ideal O => ∑' p : MulFiber B,F p.1) (∑' p,F p) at hsum
  simp_rw [hfiber] at hsum
  have hFone : (∑' p,F p)=1 := by simpa using hsum.tsum_eq.symm
  calc
    _ = ∑' p : Ideal O × Ideal O,
        ((moebius p.1:ℂ)*unramifiedNormWeight s p.1)*unramifiedNormWeight s p.2 :=
      tsum_mul_tsum_of_summable_norm (moebius_unramifiedNormWeight_summable_norm s hs)
        (unramifiedNormWeight_summable_norm s hs)
    _ = ∑' p,F p := by
      apply tsum_congr
      intro p
      simp only [F,map_mul]
      ring
    _ = 1 := hFone

theorem unramifiedIdealZeta_ne_zero (s : ℂ) (hs : 1<s.re) : unramifiedIdealZeta s ≠ 0 := by
  intro hz
  have h := unramifiedMobiusSeries_mul_zeta s hs
  rw [hz,mul_zero] at h
  exact zero_ne_one h

theorem unramifiedMobiusSeries_eq_inv (s : ℂ) (hs : 1<s.re) :
    unramifiedMobiusSeries s=(unramifiedIdealZeta s)⁻¹ := by
  have h := unramifiedMobiusSeries_mul_zeta s hs
  calc
    _ = (unramifiedMobiusSeries s*unramifiedIdealZeta s)*(unramifiedIdealZeta s)⁻¹ := by
      field_simp [unramifiedIdealZeta_ne_zero s hs]
    _ = _ := by rw [h,one_mul]

lemma unramifiedNormWeight_shift (s : ℂ) (I : Ideal O) :
    unramifiedNormWeight (s-1) I=(Ideal.absNorm I:ℂ)*unramifiedNormWeight s I := by
  by_cases hg : primaryGenerator I=0
  · rw [unramifiedNormWeight_of_bad _ I hg,unramifiedNormWeight_of_bad _ I hg,mul_zero]
  · rw [unramifiedNormWeight_of_good _ I hg,unramifiedNormWeight_of_good _ I hg]
    have hn : (Ideal.absNorm I:ℂ) ≠ 0 := Nat.cast_ne_zero.mpr
      (Ideal.absNorm_eq_zero_iff.not.mpr (primaryGenerator_ne_zero_ideal I hg))
    rw [show -(s-1)=(1:ℂ)+(-s) by ring,Complex.cpow_add _ _ hn,Complex.cpow_one]

lemma mulFiber_totient_sum (B : Ideal O) (hB : B ≠ 0) :
    (∑' p : MulFiber B,(moebius p.1.1:ℂ)*(Ideal.absNorm p.1.2:ℂ))=(idealTotient B:ℂ) := by
  let e := mulFiberDivisorEquiv B hB
  have hp (p : MulFiber B) :
      (moebius p.1.1:ℂ)*(Ideal.absNorm p.1.2:ℂ)=
        (Ideal.absNorm B:ℂ)*((moebius p.1.1:ℂ)/(Ideal.absNorm p.1.1:ℂ)) := by
    have hI : p.1.1 ≠ 0 := by
      intro hz
      have hh := p.2
      rw [hz,zero_mul] at hh
      exact hB hh.symm
    have hn : (Ideal.absNorm p.1.1:ℂ) ≠ 0 :=
      Nat.cast_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hI)
    have heq : (Ideal.absNorm B:ℂ)=(Ideal.absNorm p.1.1:ℂ)*(Ideal.absNorm p.1.2:ℂ) := by
      calc
        _ = (Ideal.absNorm (p.1.1*p.1.2):ℂ) := congrArg (fun I => (Ideal.absNorm I:ℂ)) p.2.symm
        _ = _ := by rw [map_mul,Nat.cast_mul]
    rw [heq]
    field_simp
  calc
    _ = ∑' p : MulFiber B,(Ideal.absNorm B:ℂ)*
        ((moebius p.1.1:ℂ)/(Ideal.absNorm p.1.1:ℂ)) := tsum_congr hp
    _ = (Ideal.absNorm B:ℂ)*
        ∑' D : {D : Ideal O // D ∈ idealDivisors B},
          ((moebius D.1:ℂ)/(Ideal.absNorm D.1:ℂ)) := by
      rw [← tsum_mul_left]
      exact e.tsum_eq (fun D => (Ideal.absNorm B:ℂ)*((moebius D.1:ℂ)/(Ideal.absNorm D.1:ℂ)))
    _ = (Ideal.absNorm B:ℂ)*
        ∑ D ∈ idealDivisors B,((moebius D:ℂ)/(Ideal.absNorm D:ℂ)) := by
      rw [tsum_fintype]
      apply congrArg (fun z : ℂ => (Ideal.absNorm B:ℂ)*z)
      exact (Finset.sum_subtype (idealDivisors B) (fun _ => Iff.rfl)
        (fun D => (moebius D:ℂ)/(Ideal.absNorm D:ℂ))).symm
    _ = _ := (idealTotient_moebius B hB).symm

def unramifiedTotientSeries (s : ℂ) : ℂ :=
  ∑' I : Ideal O,(idealTotient I:ℂ)*unramifiedNormWeight s I

theorem unramifiedTotientSeries_product (s : ℂ) (hs : 2<s.re) :
    unramifiedTotientSeries s=unramifiedMobiusSeries s*unramifiedIdealZeta (s-1) := by
  have hs1 : 1<s.re := by linarith
  have hs2 : 1<(s-1).re := by simp only [Complex.sub_re,Complex.one_re]; linarith
  let F : Ideal O × Ideal O → ℂ := fun p =>
    (moebius p.1:ℂ)*(Ideal.absNorm p.2:ℂ)*unramifiedNormWeight s (p.1*p.2)
  have hprod := (moebius_unramifiedNormWeight_summable_norm s hs1).mul_norm
    (unramifiedNormWeight_summable_norm (s-1) hs2)
  have heq (p : Ideal O × Ideal O) :
      ((moebius p.1:ℂ)*unramifiedNormWeight s p.1)*unramifiedNormWeight (s-1) p.2=F p := by
    simp only [F,unramifiedNormWeight_shift,map_mul]
    ring
  have hF : Summable F := hprod.of_norm.congr heq
  have hfiber (B : Ideal O) : (∑' p : MulFiber B,F p.1)=
      (idealTotient B:ℂ)*unramifiedNormWeight s B := by
    by_cases hB : B=0
    · subst B
      have hz (p : MulFiber 0) : F p.1=0 := by simp only [F,p.2,map_zero,mul_zero]
      simp only [hz,tsum_zero,map_zero,mul_zero]
    · calc
        _ = (∑' p : MulFiber B,(moebius p.1.1:ℂ)*(Ideal.absNorm p.1.2:ℂ))*
            unramifiedNormWeight s B := by
          rw [← tsum_mul_right]
          apply tsum_congr
          intro p
          simp only [F,p.2]
        _ = _ := by rw [mulFiber_totient_sum B hB]
  have hsum := hF.hasSum.tsum_fiberwise (fun p : Ideal O × Ideal O => p.1*p.2)
  change HasSum (fun B : Ideal O => ∑' p : MulFiber B,F p.1) (∑' p,F p) at hsum
  simp_rw [hfiber] at hsum
  calc
    _ = ∑' p,F p := hsum.tsum_eq
    _ = _ := by
      rw [unramifiedMobiusSeries,unramifiedIdealZeta,
        tsum_mul_tsum_of_summable_norm (moebius_unramifiedNormWeight_summable_norm s hs1)
          (unramifiedNormWeight_summable_norm (s-1) hs2)]
      exact tsum_congr (fun p => (heq p).symm)

theorem unramifiedTotientSeries_quotient (s : ℂ) (hs : 2<s.re) :
    unramifiedTotientSeries s=unramifiedIdealZeta (s-1)/unramifiedIdealZeta s := by
  rw [unramifiedTotientSeries_product s hs,unramifiedMobiusSeries_eq_inv s (by linarith),div_eq_mul_inv]
  ring

lemma idealTotient_le_absNorm (I : Ideal O) (hI : I ≠ 0) :
    idealTotient I ≤ Ideal.absNorm I := by
  let : Finite (O ⧸ I) := I.finiteQuotientOfFreeOfNeBot hI
  change Nat.card (O ⧸ I)ˣ ≤ Nat.card (O ⧸ I)
  exact Nat.card_le_card_of_injective (Units.val : (O ⧸ I)ˣ → O ⧸ I) Units.val_injective

theorem unramifiedTotientSeries_summable_norm (s : ℂ) (hs : 2<s.re) :
    Summable (fun I : Ideal O => ‖(idealTotient I:ℂ)*unramifiedNormWeight s I‖) := by
  have hs1 : 1<(s-1).re := by simp only [Complex.sub_re,Complex.one_re]; linarith
  apply (unramifiedNormWeight_summable_norm (s-1) hs1).of_nonneg_of_le
    (fun _ => norm_nonneg _)
  intro I
  by_cases hI : I=0
  · subst I; simp only [map_zero,mul_zero,norm_zero,le_refl]
  · rw [norm_mul,Complex.norm_natCast,unramifiedNormWeight_shift,norm_mul,Complex.norm_natCast]
    exact mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (idealTotient_le_absNorm I hI)) (norm_nonneg _)

end CubicEisenstein

open scoped BigOperators Classical SchwartzMap
namespace CanonicalQuadraticSieve

section
open ActualEisensteinCubic ConcreteTraceCRT CompletedGauss QuadraticSquarefreeKernel

theorem originalPairLow_squarefree_tsum
    (I J : Ideal O) (hI : Admissible I) (hJ : Admissible J)
    (W : SchwartzMap ℝ ℂ) (M K : ℝ) (hM : 0 < M) :
    (∑' lengthScale : Ideal O, originalPairLow I J W M K lengthScale) =
      ∑' B : {B : Ideal O // Admissible B},
        if (Ideal.absNorm B.val : ℝ) ≤ K then
          (quadraticRow I (primaryGenerator B.val) * quadraticRow J (primaryGenerator B.val)) *
            ∑' A : {A : Ideal O // Supported A},
              (idealZeroMask I (primaryGenerator A.val) * idealZeroMask J (primaryGenerator A.val)) *
                W (((Ideal.absNorm A.val : ℝ) ^ 2 * (Ideal.absNorm B.val : ℝ)) / M)
        else 0 := by
  let F : ({A : Ideal O // Supported A} × {B : Ideal O // Admissible B}) → ℂ := fun p =>
    if (Ideal.absNorm p.2.val : ℝ) ≤ K then
      (idealZeroMask I (primaryGenerator p.1.val) * idealZeroMask J (primaryGenerator p.1.val)) *
      (quadraticRow I (primaryGenerator p.2.val) * quadraticRow J (primaryGenerator p.2.val)) *
      W (((Ideal.absNorm p.1.val : ℝ) ^ 2 * (Ideal.absNorm p.2.val : ℝ)) / M) else 0
  have hterm (p : {A : Ideal O // Supported A} × {B : Ideal O // Admissible B}) :
      originalPairLow I J W M K (p.1.val ^ 2 * p.2.val) = F p := by
    have hs : Supported (p.1.val ^ 2 * p.2.val) :=
      (supported_mul_iff _ _).mpr ⟨(supported_sq_iff _).mpr p.1.property, admissible_supported p.2.property⟩
    unfold originalPairLow
    rw [(squarePart_mul_squarefree p.1.property.1 p.2.property.2.1).2]
    by_cases hk : (Ideal.absNorm p.2.val : ℝ) ≤ K
    · rw [if_pos hk]
      unfold originalPairSource
      rw [if_pos hs, canonical_quadraticRow_star I hI,
        canonical_quadraticRow_primary_squarefree I hI, canonical_quadraticRow_primary_squarefree J hJ]
      simp only [F, if_pos hk, map_mul, map_pow, Nat.cast_mul, Nat.cast_pow]
      ring
    · simp only [if_neg hk, F]
  have hsub : Summable (fun lengthScale : {lengthScale : Ideal O // Supported lengthScale} => originalPairLow I J W M K lengthScale.val) :=
    (originalPairLow_summable I J W M K hM).subtype _
  have hp0 : Summable (fun p : {A : Ideal O // Supported A} × {B : Ideal O // Admissible B} =>
      originalPairLow I J W M K (p.1.val ^ 2 * p.2.val)) :=
    supportedSquarefreeEquiv.symm.summable_iff.mpr hsub
  have hp : Summable F := hp0.congr hterm
  have he : (∑' lengthScale : {lengthScale : Ideal O // Supported lengthScale}, originalPairLow I J W M K lengthScale.val) =
      ∑' lengthScale : Ideal O, originalPairLow I J W M K lengthScale := by
    apply tsum_subtype_eq_of_support_subset
    intro lengthScale hL
    by_contra hs
    change ¬Supported lengthScale at hs
    exact hL (by simp [originalPairLow, originalPairSource, hs])
  calc
    _ = ∑' lengthScale : {lengthScale : Ideal O // Supported lengthScale}, originalPairLow I J W M K lengthScale.val := he.symm
    _ = ∑' p : {A : Ideal O // Supported A} × {B : Ideal O // Admissible B},
        originalPairLow I J W M K (p.1.val ^ 2 * p.2.val) :=
      (supportedSquarefreeEquiv.symm.tsum_eq (fun lengthScale => originalPairLow I J W M K lengthScale.val)).symm
    _ = ∑' p, F p := tsum_congr hterm
    _ = ∑' p : {B : Ideal O // Admissible B} × {A : Ideal O // Supported A}, F (p.2, p.1) :=
      (Equiv.prodComm _ _).tsum_eq (fun p => F (p.2, p.1))
    _ = ∑' B : {B : Ideal O // Admissible B}, ∑' A : {A : Ideal O // Supported A}, F (A, B) :=
      hp.prod_symm.tsum_prod
    _ = _ := by
      apply tsum_congr
      intro B
      by_cases hk : (Ideal.absNorm B.val : ℝ) ≤ K
      · rw [if_pos hk, ← tsum_mul_left]
        apply tsum_congr
        intro A
        simp only [F, if_pos hk]
        ring
      · simp only [F, if_neg hk, tsum_zero]

end

open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge CompletedGauss

theorem idealZeroMask_span_eq (D : Ideal O) (x y : O) (hxy : Ideal.span {x} = Ideal.span {y}) :
    idealZeroMask D x = idealZeroMask D y := by
  have hm (P : Ideal O) : x ∈ P ↔ y ∈ P := by
    constructor
    · intro h
      exact (Ideal.span_singleton_le_iff_mem P).mp (hxy ▸ (Ideal.span_singleton_le_iff_mem P).mpr h)
    · intro h
      exact (Ideal.span_singleton_le_iff_mem P).mp (hxy.symm ▸ (Ideal.span_singleton_le_iff_mem P).mpr h)
  unfold idealZeroMask
  simp_rw [hm]

theorem idealZeroMask_mul (I J : Ideal O) (hI : I ≠ 0) (hJ : J ≠ 0) (z : O) :
    idealZeroMask (I * J) z = idealZeroMask I z * idealZeroMask J z := by
  have he : (∃ P ∈ UniqueFactorizationMonoid.normalizedFactors (I * J), z ∈ P) ↔
      (∃ P ∈ UniqueFactorizationMonoid.normalizedFactors I, z ∈ P) ∨
        (∃ P ∈ UniqueFactorizationMonoid.normalizedFactors J, z ∈ P) := by
    simp only [UniqueFactorizationMonoid.normalizedFactors_mul hI hJ, Multiset.mem_add,
      or_and_right, exists_or]
  unfold idealZeroMask
  simp only [he]
  by_cases h₁ : ∃ P ∈ UniqueFactorizationMonoid.normalizedFactors I, z ∈ P <;>
    by_cases h₂ : ∃ P ∈ UniqueFactorizationMonoid.normalizedFactors J, z ∈ P <;> simp [h₁, h₂]

theorem jointMask_generator (I J : Ideal O) (hI : Admissible I) (hJ : Admissible J) (lengthScale : Ideal O) :
    rowCoprimeMask (fun P : gcdMaskPrimes (I * J) => P.val) Finset.univ (idealGenerator lengthScale) =
      if Supported lengthScale then idealZeroMask I (primaryGenerator lengthScale) * idealZeroMask J (primaryGenerator lengthScale) else 0 := by
  rw [gcdMaskPrimes_mask, idealZeroMask_mul I J hI.1 hJ.1, badPrime_mask, span_idealGenerator]
  by_cases hL : Supported lengthScale
  · rw [if_pos hL, if_pos hL, one_mul]
    have hs : Ideal.span {idealGenerator lengthScale} = Ideal.span {primaryGenerator lengthScale} :=
      (span_idealGenerator lengthScale).trans (primaryGenerator_spec lengthScale (supported_primaryGenerator_ne_zero lengthScale hL)).1.symm
    rw [idealZeroMask_span_eq I _ _ hs, idealZeroMask_span_eq J _ _ hs]
  · simp only [if_neg hL, zero_mul]

theorem jointMask_zero (I J : Ideal O) :
    rowCoprimeMask (fun P : gcdMaskPrimes (I * J) => P.val) Finset.univ 0 = 0 := by
  rw [gcdMaskPrimes_mask, badPrime_mask]
  have h : ¬Supported (Ideal.span {(0 : O)}) := by
    intro h
    exact h.1 (by simp)
  rw [if_neg h, zero_mul]

end CanonicalQuadraticSieve

end

end OAI

end


