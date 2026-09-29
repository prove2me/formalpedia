-- Prove2me | solution 1 for AlgebraicCurve.IsFrobeniusEndo.finrankAlong_pow_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/179d6b10-dfc0-58e6-9b58-420130fd2f28

import Mathlib
import Definitions.Def_AlgebraicCurve_FrobeniusEndo
import Theorems.Thm_AlgebraicCurve_finrank_frobeniusSubfield_eq_of_transcendental
import Theorems.Thm_AlgebraicCurve_finrankAlong_comp
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_IsFrobeniusEndo_finrankAlong_pow_eq

set_option autoImplicit false

noncomputable section

namespace P2mFrobDeg

open AlgebraicCurve

section General

variable {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']

theorem finrankAlong_eq_finrank_fieldRange (φ : F →ₐ[K] F') :
    finrankAlong K φ = Module.finrank φ.toRingHom.fieldRange F' := by
  unfold finrankAlong
  letI := algebraAlong φ
  refine Algebra.finrank_eq_of_equiv_equiv φ.toRingHom.rangeRestrictFieldEquiv (RingEquiv.refl F') ?_
  ext x
  rfl

end General

section Pow

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem isFrobeniusEndo_pow {φ : F →ₐ[K] F} {q : ℕ} (h : IsFrobeniusEndo q φ) (n : ℕ) :
    IsFrobeniusEndo (q ^ n) (φ ^ n) := by
  induction n with
  | zero => exact ⟨fun x => ⟨x, by simp⟩, fun y => ⟨y, by simp⟩⟩
  | succ n ih =>
    refine ⟨fun x => ?_, fun y => ?_⟩
    · obtain ⟨w, hw⟩ := h.pow_mem_range x
      obtain ⟨y, hy⟩ := ih.pow_mem_range w
      refine ⟨y, ?_⟩
      rw [pow_succ', AlgHom.mul_apply, hy, map_pow, hw, ← pow_mul, ← pow_succ']
    · obtain ⟨z, hz⟩ := ih.mem_range_pow y
      obtain ⟨x, hx⟩ := h.mem_range_pow z
      refine ⟨x, ?_⟩
      rw [pow_succ', AlgHom.mul_apply, hz, map_pow, hx, ← pow_mul, ← pow_succ']

theorem fieldRange_eq_of_isFrobeniusEndo {φ : F →ₐ[K] F} (p : ℕ) [Fact p.Prime] [CharP F p]
    {m : ℕ} (h : IsFrobeniusEndo (p ^ m) φ) :
    φ.toRingHom.fieldRange = (iterateFrobenius F p m).fieldRange := by
  ext y
  simp only [RingHom.mem_fieldRange, iterateFrobenius_def]
  constructor
  · rintro ⟨x, rfl⟩
    obtain ⟨z, hz⟩ := h.mem_range_pow x
    exact ⟨z, hz.symm⟩
  · rintro ⟨x, rfl⟩
    exact h.pow_mem_range x

end Pow

section PrimeField

variable (F : Type*) [Field F] (p : ℕ) [Fact p.Prime] [CharP F p]

def frobeniusZMod : letI := ZMod.algebra F p; F →ₐ[ZMod p] F :=
  letI := ZMod.algebra F p
  { frobenius F p with
    commutes' := fun a => by
      simp only [RingHom.toMonoidHom_eq_coe, OneHom.toFun_eq_coe, MonoidHom.toOneHom_coe,
        MonoidHom.coe_coe, frobenius_def]
      rw [← map_pow, ZMod.pow_card] }

theorem frobeniusZMod_pow_toRingHom (m : ℕ) :
    (letI := ZMod.algebra F p; (frobeniusZMod F p ^ m).toRingHom) = iterateFrobenius F p m := by
  letI := ZMod.algebra F p
  ext x
  rw [iterateFrobenius_def]
  show (frobeniusZMod F p ^ m) x = x ^ p ^ m
  induction m generalizing x with
  | zero => simp
  | succ m ih =>
    rw [pow_succ, AlgHom.mul_apply, ih]
    show (x ^ p) ^ p ^ m = _
    rw [← pow_mul, ← pow_succ']

variable {K : Type*} [Field K] [Algebra K F] [PerfectField K] [CharP K p]

theorem finrankAlong_frobeniusZMod (t : F) (htr : Transcendental K t)
    [FiniteDimensional (IntermediateField.adjoin K ({t} : Set F)) F] :
    (letI := ZMod.algebra F p; finrankAlong (ZMod p) (frobeniusZMod F p)) = p := by
  letI := ZMod.algebra F p
  rw [finrankAlong_eq_finrank_fieldRange]
  exact AlgebraicCurve.finrank_frobeniusSubfield_eq_of_transcendental p t htr

theorem finrankAlong_frobeniusZMod_pow (t : F) (htr : Transcendental K t)
    [FiniteDimensional (IntermediateField.adjoin K ({t} : Set F)) F] (m : ℕ) :
    (letI := ZMod.algebra F p; finrankAlong (ZMod p) (frobeniusZMod F p ^ m)) = p ^ m := by
  letI := ZMod.algebra F p
  induction m with
  | zero =>
    rw [pow_zero, pow_zero, finrankAlong_eq_finrank_fieldRange]
    have htop : (1 : F →ₐ[ZMod p] F).toRingHom.fieldRange = ⊤ :=
      RingHom.fieldRange_eq_top_iff.mpr fun x => ⟨x, rfl⟩
    rw [htop]
    exact (Algebra.finrank_eq_of_equiv_equiv (R₀ := (⊤ : Subfield F)) (S₀ := F) (R₁ := F)
      (S₁ := F) Subfield.topEquiv (RingEquiv.refl F) (by ext; rfl)).trans (Module.finrank_self F)
  | succ m ih =>
    rw [pow_succ, show frobeniusZMod F p ^ m * frobeniusZMod F p =
      (frobeniusZMod F p ^ m).comp (frobeniusZMod F p) from rfl,
      AlgebraicCurve.finrankAlong_comp, finrankAlong_frobeniusZMod F p t htr, ih, pow_succ']

theorem finrank_fieldRange_iterateFrobenius (t : F) (htr : Transcendental K t)
    [FiniteDimensional (IntermediateField.adjoin K ({t} : Set F)) F] (m : ℕ) :
    Module.finrank (iterateFrobenius F p m).fieldRange F = p ^ m := by
  have h := finrankAlong_frobeniusZMod_pow F p t htr m
  letI := ZMod.algebra F p
  rw [finrankAlong_eq_finrank_fieldRange, frobeniusZMod_pow_toRingHom] at h
  exact h

end PrimeField

section Degree

variable {K F : Type*} [Field K] [Field F] [Algebra K F] [PerfectField K]
variable (p : ℕ) [Fact p.Prime] [CharP K p]

theorem finrankAlong_pow_eq
    (hF : ∃ t : F, Transcendental K t ∧
      FiniteDimensional (IntermediateField.adjoin K ({t} : Set F)) F)
    {φ : F →ₐ[K] F} {r : ℕ} (h : IsFrobeniusEndo (p ^ r) φ) (n : ℕ) :
    finrankAlong K (φ ^ n) = (p ^ r) ^ n := by
  obtain ⟨t, htr, hfin⟩ := hF
  haveI := hfin
  haveI : CharP F p := (RingHom.charP_iff_charP (algebraMap K F) p).mp inferInstance
  have hn : IsFrobeniusEndo (p ^ (r * n)) (φ ^ n) := by
    rw [pow_mul]; exact isFrobeniusEndo_pow h n
  rw [finrankAlong_eq_finrank_fieldRange, fieldRange_eq_of_isFrobeniusEndo p hn, ← pow_mul]
  exact finrank_fieldRange_iterateFrobenius F p t htr (r * n)

end Degree

end P2mFrobDeg

end

theorem solution
    {K F : Type*} [Field K] [Field F] [Algebra K F] [PerfectField K]
    (p : ℕ) [Fact p.Prime] [CharP K p]
    (hF : ∃ t : F, Transcendental K t ∧
      FiniteDimensional (IntermediateField.adjoin K ({t} : Set F)) F)
    {φ : F →ₐ[K] F} {r : ℕ} (h : AlgebraicCurve.IsFrobeniusEndo (p ^ r) φ) (n : ℕ) :
    AlgebraicCurve.finrankAlong K (φ ^ n) = (p ^ r) ^ n :=
  P2mFrobDeg.finrankAlong_pow_eq p hF h n

end S_AlgebraicCurve_IsFrobeniusEndo_finrankAlong_pow_eq
end P2MW
export P2MW.S_AlgebraicCurve_IsFrobeniusEndo_finrankAlong_pow_eq (solution)
