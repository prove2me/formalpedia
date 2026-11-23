-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CmTypePeriodNormIntegral
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_CmTypePeriodNormIntegral
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T14:53:22.817176+00:00
-- url     : https://prove2.me/theorems/3eed341b-fc25-40a0-9803-c7fbb3e0a2ad
-- title:
--   Cm Type Period Norm Integral
-- statement:
--   Definitions and structural lemmas for Cm Type Period Norm Integral, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CmTypePeriodNormIntegral.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_ConjugateOrderData
import Theorems.Thm_GlobalTheory_CMVal_coe_latticeSub
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.CMVal.coe_latticeSub


set_option autoImplicit false
open NumberField IsDedekindDomain TensorProduct GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations
open Classical
noncomputable section
namespace GlobalTheory.CMExtend
section Mult
variable {E : Type} [Field E] [NumberField E]
theorem exists_natMul_isIntegral (x : E) : ∃ m : ℕ, m ≠ 0 ∧ IsIntegral ℤ ((m : E) * x) := by
  obtain ⟨y, hy, hi⟩ := IsAlgebraic.exists_integral_multiple (R := ℤ)
    ((IsFractionRing.isAlgebraic_iff ℤ ℚ E).2 (Algebra.IsAlgebraic.isAlgebraic x))
  refine ⟨y.natAbs, Int.natAbs_ne_zero.2 hy, ?_⟩
  rcases Int.natAbs_eq y with h | h
  · rw [h, zsmul_eq_mul] at hi
    simpa using hi
  · rw [h, zsmul_eq_mul] at hi
    have := hi.neg
    simpa using this
theorem exists_natMul_mem_orderC {c : Ideal (OF E)} (hc : c ≠ ⊥) (x : E) :
    ∃ n : ℕ, n ≠ 0 ∧ (n : E) * x ∈ orderC c := by
  obtain ⟨m, hm, hint⟩ := exists_natMul_isIntegral x
  have hk0 : Ideal.absNorm c ≠ 0 := fun h => hc (Ideal.absNorm_eq_zero_iff.1 h)
  obtain ⟨y, hy⟩ : ∃ y : 𝓞 E, algebraMap (𝓞 E) E y = (m : E) * x :=
    ⟨⟨(m : E) * x, (mem_integralClosure_iff ℤ E).2 hint⟩, rfl⟩
  refine ⟨Ideal.absNorm c * m, mul_ne_zero hk0 hm, ?_⟩
  refine mem_orderC.2 ⟨0, algebraMap (OF E) (𝓞 E) ((Ideal.absNorm c : ℕ) : OF E) * y,
    Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ (Ideal.absNorm_mem c)), ?_⟩
  rw [map_zero, zero_add, map_mul, hy, map_natCast, map_natCast, Nat.cast_mul, mul_assoc]
end Mult
section Ext
variable {E : Type} [Field E] [NumberField E] {c : Ideal (OF E)}
variable {K A : Type} [Field K] [CharZero K] [Ring A] [Algebra K A]
def mulN (hc : c ≠ ⊥) (x : E) : ℕ := Classical.choose (exists_natMul_mem_orderC hc x)
theorem mulN_ne_zero (hc : c ≠ ⊥) (x : E) : mulN hc x ≠ 0 :=
  (Classical.choose_spec (exists_natMul_mem_orderC hc x)).1
theorem mulN_mem (hc : c ≠ ⊥) (x : E) : (mulN hc x : E) * x ∈ orderC c :=
  (Classical.choose_spec (exists_natMul_mem_orderC hc x)).2
variable (K) in

def extFun (hc : c ≠ ⊥) (g : orderC c →+* A) (x : E) : A :=
  ((mulN hc x : K))⁻¹ • g ⟨(mulN hc x : E) * x, mulN_mem hc x⟩
theorem map_natMul (g : orderC c →+* A) (n : ℕ) (z : orderC c) : g ((n : orderC c) * z) = (n : K) • g z := by
  rw [map_mul, map_natCast, Nat.cast_smul_eq_nsmul, nsmul_eq_mul]
theorem extFun_eq (hc : c ≠ ⊥) (g : orderC c →+* A) {x : E} {m : ℕ} (hm : m ≠ 0) (h : (m : E) * x ∈ orderC c) :
    extFun K hc g x = ((m : K))⁻¹ • g ⟨(m : E) * x, h⟩ := by
  have hm0 : (m : K) ≠ 0 := Nat.cast_ne_zero.2 hm
  have hn0 : (mulN hc x : K) ≠ 0 := Nat.cast_ne_zero.2 (mulN_ne_zero hc x)
  have key : (m : K) • g ⟨(mulN hc x : E) * x, mulN_mem hc x⟩ = (mulN hc x : K) • g ⟨(m : E) * x, h⟩ := by
    rw [← map_natMul, ← map_natMul]
    congr 1
    apply Subtype.ext
    simp only [Subring.coe_mul, Subring.coe_natCast]
    ring
  calc extFun K hc g x = ((mulN hc x : K))⁻¹ • ((m : K)⁻¹ • ((m : K) • g ⟨(mulN hc x : E) * x, mulN_mem hc x⟩)) := by
        rw [inv_smul_smul₀ hm0]; rfl
    _ = ((mulN hc x : K))⁻¹ • ((m : K)⁻¹ • ((mulN hc x : K) • g ⟨(m : E) * x, h⟩)) := by rw [key]
    _ = ((m : K))⁻¹ • g ⟨(m : E) * x, h⟩ := by
        rw [smul_comm ((m : K)⁻¹) ((mulN hc x : K)), inv_smul_smul₀ hn0]
variable (K) in

def extHom (hc : c ≠ ⊥) (g : orderC c →+* A) : E →+* A where
  toFun := extFun K hc g
  map_one' := by
    rw [extFun_eq hc g one_ne_zero (by simpa using (orderC c).one_mem)]
    simp only [Nat.cast_one, inv_one, one_smul]
    convert g.map_one using 2
    apply Subtype.ext; simp
  map_mul' x y := by
    have hx := mulN_mem hc x
    have hy := mulN_mem hc y
    have hxy : ((mulN hc x * mulN hc y : ℕ) : E) * (x * y) ∈ orderC c := by
      convert mul_mem hx hy using 1; push_cast; ring
    rw [extFun_eq hc g (mul_ne_zero (mulN_ne_zero hc x) (mulN_ne_zero hc y)) hxy]
    have e : (⟨((mulN hc x * mulN hc y : ℕ) : E) * (x * y), hxy⟩ : orderC c) =
        ⟨(mulN hc x : E) * x, hx⟩ * ⟨(mulN hc y : E) * y, hy⟩ := by
      apply Subtype.ext; simp only [Subring.coe_mul]; push_cast; ring
    rw [e, map_mul]
    show _ = (((mulN hc x : K))⁻¹ • g ⟨(mulN hc x : E) * x, hx⟩) * (((mulN hc y : K))⁻¹ • g ⟨(mulN hc y : E) * y, hy⟩)
    rw [smul_mul_smul_comm]
    push_cast
    rw [mul_inv]
  map_zero' := by
    rw [extFun_eq hc g one_ne_zero (by simpa using (orderC c).zero_mem)]
    convert smul_zero _ using 2
    convert g.map_zero using 2
    apply Subtype.ext; simp
  map_add' x y := by
    have hx := mulN_mem hc x
    have hy := mulN_mem hc y
    have hx0 : (mulN hc x : K) ≠ 0 := Nat.cast_ne_zero.2 (mulN_ne_zero hc x)
    have hy0 : (mulN hc y : K) ≠ 0 := Nat.cast_ne_zero.2 (mulN_ne_zero hc y)
    have e : ((mulN hc x * mulN hc y : ℕ) : E) * (x + y) =
        (((mulN hc y : ℕ) : orderC c) * ⟨(mulN hc x : E) * x, hx⟩ + ((mulN hc x : ℕ) : orderC c) * ⟨(mulN hc y : E) * y, hy⟩ :
          orderC c) := by
      simp only [Subring.coe_add, Subring.coe_mul, Subring.coe_natCast]; push_cast; ring
    have hxy : ((mulN hc x * mulN hc y : ℕ) : E) * (x + y) ∈ orderC c := by rw [e]; exact Subtype.property _
    rw [extFun_eq hc g (mul_ne_zero (mulN_ne_zero hc x) (mulN_ne_zero hc y)) hxy]
    have e' : (⟨((mulN hc x * mulN hc y : ℕ) : E) * (x + y), hxy⟩ : orderC c) =
        ((mulN hc y : ℕ) : orderC c) * ⟨(mulN hc x : E) * x, hx⟩ + ((mulN hc x : ℕ) : orderC c) * ⟨(mulN hc y : E) * y, hy⟩ :=
      Subtype.ext e
    rw [e', map_add, map_natMul (K := K), map_natMul (K := K)]
    show _ = ((mulN hc x : K))⁻¹ • g ⟨(mulN hc x : E) * x, hx⟩ + ((mulN hc y : K))⁻¹ • g ⟨(mulN hc y : E) * y, hy⟩
    rw [smul_add, smul_smul, smul_smul]
    congr 2
    · push_cast; field_simp
    · push_cast; field_simp
end Ext
def baseChangeRingHom (O : Type) [CommRing O] (K : Type) [Field K] [Algebra O K] (H : Type) [AddCommGroup H] [Module O H] :
    Module.End O H →+* Module.End K (K ⊗[O] H) where
  toFun f := f.baseChange K
  map_one' := LinearMap.baseChange_one O H
  map_mul' f g := LinearMap.baseChange_mul f g
  map_zero' := LinearMap.baseChange_zero
  map_add' f g := LinearMap.baseChange_add f g
end GlobalTheory.CMExtend


