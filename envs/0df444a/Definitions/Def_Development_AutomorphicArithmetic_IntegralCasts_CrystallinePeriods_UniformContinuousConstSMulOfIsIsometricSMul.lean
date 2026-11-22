-- Prove2me | Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_UniformContinuousConstSMulOfIsIsometricSMul
-- name    : Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_UniformContinuousConstSMulOfIsIsometricSMul
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T16:46:17.904853+00:00
-- url     : https://prove2.me/theorems/89851769-499f-4b6d-9846-52e6f9422872
-- title:
--   Uniform Continuous Const SMul Of Is Isometric SMul
-- statement:
--   Definitions and structural lemmas for Uniform Continuous Const SMul Of Is Isometric SMul, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CrystallinePeriods/UniformContinuousConstSMulOfIsIsometricSMul.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Ideal Filter Topology
namespace Reformulated.AutPerF
universe u v
class IsUnitBall {C : Type u} [NormedField C] (O : ValuationSubring C) : Prop where
  mem_iff : ∀ x : C, x ∈ O ↔ ‖x‖ ≤ 1
def unitBall (C : Type u) [NormedField C] [IsUltrametricDist C] : ValuationSubring C :=
  (NormedField.valuation (K := C)).valuationSubring
instance (C : Type u) [NormedField C] [IsUltrametricDist C] : IsUnitBall (unitBall C) :=
  ⟨fun x => by
    rw [unitBall, Valuation.mem_valuationSubring_iff, NormedField.valuation_apply,
      ← NNReal.coe_le_coe]
    rfl⟩
namespace IsUnitBall
variable {C : Type u} [NormedField C] (O : ValuationSubring C) [IsUnitBall O]
variable {O} in
theorem norm_le_one (x : O) : ‖(x : C)‖ ≤ 1 := (mem_iff x.1).1 x.2
variable {O} in
theorem dvd_iff_norm_le (x y : O) : x ∣ y ↔ ‖(y : C)‖ ≤ ‖(x : C)‖ := by
  constructor
  · rintro ⟨c, rfl⟩
    push_cast
    rw [norm_mul]
    exact mul_le_of_le_one_right (norm_nonneg _) (norm_le_one c)
  · intro h
    by_cases hx : (x : C) = 0
    · rw [hx, norm_zero, norm_le_zero_iff] at h
      rw [show y = 0 from Subtype.ext h]
      exact dvd_zero _
    · refine ⟨⟨(y : C) / x, (mem_iff _).2 ?_⟩, Subtype.ext ?_⟩
      · rw [norm_div]; exact div_le_one_of_le₀ h (norm_nonneg _)
      · push_cast; field_simp
variable {O} in
theorem isUnit_iff_norm_eq_one (x : O) : IsUnit x ↔ ‖(x : C)‖ = 1 := by
  rw [isUnit_iff_dvd_one, dvd_iff_norm_le]
  push_cast
  rw [norm_one]
  exact ⟨fun h => le_antisymm (norm_le_one x) h, fun h => h.ge⟩
variable (p : ℕ)
theorem mem_span_pow_iff (n : ℕ) (x : O) :
    x ∈ (span {(p : O)} ^ n • ⊤ : Submodule O O) ↔ ‖(x : C)‖ ≤ ‖(p : C)‖ ^ n := by
  rw [smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton,
    dvd_iff_norm_le]
  push_cast
  rw [norm_pow]
variable [hp : Fact (‖(p : C)‖ < 1)]
instance : Fact ¬IsUnit (p : O) :=
  ⟨by rw [isUnit_iff_norm_eq_one]; exact_mod_cast hp.out.ne⟩
instance [CompleteSpace C] : IsAdicComplete (span {(p : O)}) O where
  haus' x hx := by
    have ht := tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg (p : C)) hp.out
    have : ‖(x : C)‖ ≤ 0 := ge_of_tendsto' ht fun n => by
      have := hx n
      rwa [SModEq.zero, mem_span_pow_iff] at this
    exact Subtype.ext (norm_le_zero_iff.1 this)
  prec' f hf := by
    have ht := tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg (p : C)) hp.out
    have h1 : ∀ m n, m ≤ n → dist (f m : C) (f n) ≤ ‖(p : C)‖ ^ m := fun m n h => by
      have := hf h
      rw [SModEq.sub_mem, mem_span_pow_iff] at this
      rw [dist_eq_norm]
      exact_mod_cast this
    have hc : CauchySeq fun n => (f n : C) := cauchySeq_of_le_tendsto_0' _ h1 ht
    obtain ⟨L, hL⟩ := cauchySeq_tendsto_of_complete hc
    have hL1 : ‖L‖ ≤ 1 := le_of_tendsto' hL.norm fun n => norm_le_one (f n)
    refine ⟨⟨L, (mem_iff L).2 hL1⟩, fun n => ?_⟩
    rw [SModEq.sub_mem, mem_span_pow_iff]
    have : dist (f n : C) L ≤ ‖(p : C)‖ ^ n :=
      le_of_tendsto (tendsto_const_nhds.dist hL)
        (eventually_atTop.2 ⟨n, fun m hm => h1 n m hm⟩)
    rw [dist_eq_norm] at this
    exact_mod_cast this
instance [CharZero C] [NeZero p] : IsLocalization.Away (p : O) C where
  map_units := by
    rintro ⟨_, n, rfl⟩
    simp only [map_pow, map_natCast]
    exact (IsUnit.mk0 _ (Nat.cast_ne_zero.2 (NeZero.ne p))).pow n
  surj z := by
    have ht := (tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg (p : C)) hp.out).const_mul ‖z‖
    rw [mul_zero] at ht
    obtain ⟨n, hn⟩ := (ht.eventually_le_const zero_lt_one).exists
    refine ⟨⟨⟨z * p ^ n, (mem_iff _).2 (by rwa [norm_mul, norm_pow])⟩, ⟨_, n, rfl⟩⟩, ?_⟩
    simp only [map_pow, map_natCast]
    rfl
  exists_of_eq h := ⟨1, by rw [show _ = _ from Subtype.ext h]⟩
def awayEquiv [CharZero C] [NeZero p] : Localization.Away (p : O) ≃ₐ[O] C :=
  IsLocalization.algEquiv (Submonoid.powers (p : O)) _ _
omit hp in
instance [IsAlgClosed C] : IsAlgClosed (FractionRing O) :=
  IsAlgClosed.of_ringEquiv C _ (FractionRing.algEquiv O C).symm.toRingEquiv
@[simp] theorem awayEquiv_algebraMap [CharZero C] [NeZero p] (x : O) :
    awayEquiv O p (algebraMap O _ x) = (x : C) := (awayEquiv O p).commutes x
omit hp in
variable {O} in

def restrict {C' : Type*} [NormedField C'] (O' : ValuationSubring C') [IsUnitBall O']
    (f : C →+* C') (hf : ∀ x, ‖f x‖ ≤ ‖x‖) : O →+* O' :=
  (f.comp O.subtype).codRestrict O' fun x => (mem_iff _).2 ((hf _).trans (norm_le_one x))
omit hp in
variable {O} in
@[simp] theorem coe_restrict {C' : Type*} [NormedField C'] (O' : ValuationSubring C')
    [IsUnitBall O'] (f : C →+* C') (hf : ∀ x, ‖f x‖ ≤ ‖x‖) (x : O) :
    (restrict O' f hf x : C') = f x := rfl
section Action
variable (G : Type v) [Monoid G] [MulSemiringAction G C] [IsIsometricSMul G C]
omit hp in
theorem norm_smul_eq (g : G) (x : C) : ‖g • x‖ = ‖x‖ := by
  simpa using (isometry_smul C g).dist_eq x 0
omit hp in

instance : MulSemiringAction G O where
  smul g x := ⟨g • (x : C), (mem_iff _).2 (by rw [norm_smul_eq]; exact norm_le_one x)⟩
  one_smul x := Subtype.ext (one_smul G (x : C))
  mul_smul g h x := Subtype.ext (mul_smul g h (x : C))
  smul_zero g := Subtype.ext (smul_zero g)
  smul_add g x y := Subtype.ext (smul_add g (x : C) y)
  smul_one g := Subtype.ext (smul_one g)
  smul_mul g x y := Subtype.ext (smul_mul' g (x : C) y)
omit hp in
variable {O G} in
@[simp] theorem coe_smul (g : G) (x : O) : ((g • x : O) : C) = g • (x : C) := rfl
end Action
end IsUnitBall
section Completion
variable (G : Type v) [Monoid G] (E : Type u) [NormedField E] [MulSemiringAction G E]
  [IsIsometricSMul G E]
instance (priority := 100) uniformContinuousConstSMul_of_isIsometricSMul :
    UniformContinuousConstSMul G E :=
  ⟨fun g => (isometry_smul E g).uniformContinuous⟩
open UniformSpace in

instance completionMulSemiringAction : MulSemiringAction G (Completion E) where
  __ := (inferInstance : DistribMulAction G (Completion E))
  smul_one g := by rw [← Completion.coe_one, ← Completion.coe_smul, smul_one]
  smul_mul g x y := by
    refine Completion.induction_on₂ x y
      (isClosed_eq ((continuous_fst.fun_mul continuous_snd).fun_const_smul g)
        ((continuous_fst.fun_const_smul g).fun_mul (continuous_snd.fun_const_smul g)))
      fun a b => ?_
    rw [← Completion.coe_mul, ← Completion.coe_smul, ← Completion.coe_smul,
      ← Completion.coe_smul, smul_mul', Completion.coe_mul]
open UniformSpace in
instance completionIsIsometricSMul : IsIsometricSMul G (Completion E) :=
  ⟨fun g => (isometry_smul E g).completion_map⟩
end Completion
section PadicComplex
variable (p : ℕ) [Fact p.Prime]
instance : IsUnitBall (PadicComplexInt p) :=
  ⟨fun x => by
    rw [PadicComplexInt, Valuation.mem_valuationSubring_iff, PadicComplex.norm_eq_norm,
      Valuation.norm_def, ← NNReal.coe_one, NNReal.coe_le_coe, PadicComplex.RankOne.hom_eq_embedding,
      Valuation.embedding_restrict]⟩
instance : Fact (‖(p : ℂ_[p])‖ < 1) :=
  ⟨by
    rw [← PadicComplex.coe_natCast, PadicComplex.norm_extends,
      ← map_natCast (algebraMap ℚ_[p] (PadicAlgCl p))]
    exact (PadicAlgCl.norm_extends p p).trans_lt Padic.norm_p_lt_one⟩
instance (K : Type*) [Field K] [Algebra ℚ_[p] K] [Algebra K (PadicAlgCl p)]
    [IsScalarTower ℚ_[p] K (PadicAlgCl p)] :
    IsIsometricSMul (PadicAlgCl p ≃ₐ[K] PadicAlgCl p) (PadicAlgCl p) :=
  ⟨fun g => Isometry.of_dist_eq fun x y => by
    rw [dist_eq_norm, dist_eq_norm, ← smul_sub]
    exact (spectralNorm_eq_of_equiv (g.restrictScalars ℚ_[p]) (x - y)).symm⟩
def padicIntToComplexInt : ℤ_[p] →+* PadicComplexInt p :=
  ((algebraMap ℚ_[p] ℂ_[p]).comp (algebraMap ℤ_[p] ℚ_[p])).codRestrict _ fun x =>
    (IsUnitBall.mem_iff _).2 (by
      rw [RingHom.comp_apply, norm_algebraMap']; exact x.norm_le_one)
@[simp] theorem coe_padicIntToComplexInt (x : ℤ_[p]) :
    (padicIntToComplexInt p x : ℂ_[p]) = algebraMap ℚ_[p] ℂ_[p] x := rfl
example : Fact ¬IsUnit (p : PadicComplexInt p) := inferInstance
example : IsAdicComplete (span {(p : PadicComplexInt p)}) (PadicComplexInt p) := inferInstance
example : IsDomain (PadicComplexInt p) := inferInstance
example : ValuationRing (PadicComplexInt p) := inferInstance
example : CharZero (PadicComplexInt p) := inferInstance
example : IsAlgClosed (FractionRing (PadicComplexInt p)) := inferInstance
example : MulSemiringAction (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) (PadicComplexInt p) :=
  inferInstance
example (K : IntermediateField ℚ_[p] (PadicAlgCl p)) :
    MulSemiringAction (PadicAlgCl p ≃ₐ[K] PadicAlgCl p) (PadicComplexInt p) := inferInstance
end PadicComplex
section CK
variable (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
def AlgCl : Type u := AlgebraicClosure K
namespace AlgCl
instance : Field (AlgCl K) := inferInstanceAs (Field (AlgebraicClosure K))
instance : Algebra K (AlgCl K) := inferInstanceAs (Algebra K (AlgebraicClosure K))
instance : IsAlgClosure K (AlgCl K) := inferInstanceAs (IsAlgClosure K (AlgebraicClosure K))
instance : IsAlgClosed (AlgCl K) := IsAlgClosure.isAlgClosed K
instance : Algebra.IsAlgebraic K (AlgCl K) := IsAlgClosure.isAlgebraic
instance : NontriviallyNormedField (AlgCl K) := spectralNorm.nontriviallyNormedField K (AlgCl K)
instance : NormedAlgebra K (AlgCl K) := spectralNorm.normedAlgebra K (AlgCl K)
instance : IsUltrametricDist (AlgCl K) :=
  IsUltrametricDist.isUltrametricDist_of_forall_norm_add_le_max_norm
    (isNonarchimedean_spectralNorm (K := K) (L := AlgCl K))
instance [CharZero K] : CharZero (AlgCl K) :=
  (RingHom.charZero_iff (algebraMap K (AlgCl K)).injective).mp inferInstance
instance (F : Type*) [Field F] [Algebra K F] [Algebra F (AlgCl K)] [IsScalarTower K F (AlgCl K)] :
    IsIsometricSMul (AlgCl K ≃ₐ[F] AlgCl K) (AlgCl K) :=
  ⟨fun g => Isometry.of_dist_eq fun x y => by
    rw [dist_eq_norm, dist_eq_norm, ← smul_sub]
    exact (spectralNorm_eq_of_equiv (g.restrictScalars K) (x - y)).symm⟩
end AlgCl
abbrev GalK : Type u := AlgCl K ≃ₐ[K] AlgCl K
abbrev CK : Type u := UniformSpace.Completion (AlgCl K)
namespace CK
instance : NontriviallyNormedField (CK K) where
  __ := (inferInstance : NormedField (CK K))
  non_trivial := by
    obtain ⟨x, hx⟩ := NontriviallyNormedField.non_trivial (α := AlgCl K)
    exact ⟨x, by simpa using hx⟩
instance : IsUltrametricDist (CK K) := IsUltrametricDist.of_normedAlgebra K
instance [CharZero K] : CharZero (CK K) :=
  (RingHom.charZero_iff (algebraMap K (CK K)).injective).mp inferInstance
instance [CharZero K] : IsAlgClosed (CK K) :=
  IsAlgClosed.of_denseRange (K := AlgCl K) UniformSpace.Completion.denseRange_coe
instance (p : ℕ) [hp : Fact (‖(p : K)‖ < 1)] : Fact (‖(p : CK K)‖ < 1) :=
  ⟨by rw [← map_natCast (algebraMap K (CK K)), norm_algebraMap']; exact hp.out⟩
end CK
abbrev OCK : ValuationSubring (CK K) := unitBall (CK K)
def OCK.ofInteger : unitBall K →+* OCK K :=
  IsUnitBall.restrict _ (algebraMap K (CK K)) fun x => (norm_algebraMap' _ x).le
example (p : ℕ) [Fact (‖(p : K)‖ < 1)] : Fact ¬IsUnit (p : OCK K) := inferInstance
example (p : ℕ) [Fact (‖(p : K)‖ < 1)] : IsAdicComplete (span {(p : OCK K)}) (OCK K) :=
  inferInstance
example [CharZero K] : CharZero (OCK K) := inferInstance
example [CharZero K] : IsAlgClosed (FractionRing (OCK K)) := inferInstance
example : ValuationRing (OCK K) := inferInstance
example : MulSemiringAction (GalK K) (OCK K) := inferInstance
end CK
end Reformulated.AutPerF


