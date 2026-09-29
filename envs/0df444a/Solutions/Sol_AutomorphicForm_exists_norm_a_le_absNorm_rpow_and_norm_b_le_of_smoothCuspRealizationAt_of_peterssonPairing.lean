-- Prove2me | solution 1 for AutomorphicForm.exists_norm_a_le_absNorm_rpow_and_norm_b_le_of_smoothCuspRealizationAt_of_peterssonPairing
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/fd980ced-0ecc-5e87-8d51-f07adb1c3fef

import Definitions.Def_AutomorphicForm_PeterssonIntegral
import Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import Definitions.Def_AutomorphicForm_HeckeEigenfunction
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_norm_a_le_absNorm_rpow_and_norm_b_le_of_smoothCuspRealizationAt_of_peterssonPairing

set_option autoImplicit false

open NumberField
open NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm.WindowedSiegel
open IsDedekindDomain NumberField.TateGlobal

open MeasureTheory NumberField.AdelicHaar AutomorphicForm

attribute [local instance] NumberField.AdelicHaar.glBorel

open scoped ComplexConjugate

namespace PeterssonCoefficientBound

section Generic

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

private theorem norm_mul_self_le (P : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ) (W : Submodule ℂ V)
    (hherm : ∀ x ∈ W, ∀ y ∈ W, conj (P x y) = P y x)
    (hpos : ∀ x ∈ W, 0 ≤ (P x x).re)
    {x y : V} (hx : x ∈ W) (hy : y ∈ W) :
    ‖P x y‖ * ‖P x y‖ ≤ (P x x).re * (P y y).re := by
  let c : PreInnerProductSpace.Core ℂ W :=
    { inner := fun a b => P (b : V) (a : V)
      conj_inner_symm := fun a b => hherm _ a.2 _ b.2
      re_inner_nonneg := fun a => hpos _ a.2
      add_left := fun a b z => by
        change P (z : V) ((a : V) + (b : V)) = P (z : V) (a : V) + P (z : V) (b : V)
        exact map_add _ _ _
      smul_left := fun a b r => by
        change P (b : V) (r • (a : V)) = conj r * P (b : V) (a : V)
        rw [LinearMap.map_smulₛₗ, smul_eq_mul] }
  have h := @InnerProductSpace.Core.inner_mul_inner_self_le ℂ W _ _ _ c ⟨x, hx⟩ ⟨y, hy⟩
  change ‖P y x‖ * ‖P x y‖ ≤ RCLike.re (P x x) * RCLike.re (P y y) at h
  have e : ‖P y x‖ = ‖P x y‖ := by
    rw [← hherm x hx y hy]
    exact RCLike.norm_conj _
  rw [e] at h
  simpa using h

variable {A : Type*} [CommRing A]

private theorem scalar_mul_comm (a : Aˣ) (g : GL (Fin 2) A) :
    Matrix.GeneralLinearGroup.scalar (Fin 2) a * g = g * Matrix.GeneralLinearGroup.scalar (Fin 2) a := by
  have hz : Matrix.GeneralLinearGroup.scalar (Fin 2) a ∈ Subgroup.center (GL (Fin 2) A) :=
    Matrix.GeneralLinearGroup.mem_center_iff_val_mem_range_scalar.mpr ⟨a, rfl⟩
  exact ((Subgroup.mem_center_iff.mp hz) g).symm

private theorem det_scalar_two (a : Aˣ) :
    Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.scalar (Fin 2) a) = a * a := by
  rw [Matrix.GeneralLinearGroup.det_scalar, Fintype.card_fin, pow_two]

private theorem det_diagOne (a : Aˣ) : Matrix.GeneralLinearGroup.det (diagOne a) = a := by
  ext
  rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two, diagOne_coe_apply, diagOne_coe_apply,
    diagOne_coe_apply, diagOne_coe_apply]
  simp

private theorem le_rpow_natCeil {N x : ℝ} (hN : 2 ≤ N) : x ≤ N ^ ((⌈x⌉₊ : ℕ) : ℝ) := by
  rw [Real.rpow_natCast]
  calc x ≤ (⌈x⌉₊ : ℝ) := Nat.le_ceil x
    _ ≤ ((2 : ℕ) ^ ⌈x⌉₊ : ℕ) := by exact_mod_cast (Nat.lt_two_pow_self).le
    _ = (2 : ℝ) ^ ⌈x⌉₊ := by push_cast; ring
    _ ≤ N ^ ⌈x⌉₊ := pow_le_pow_left₀ (by norm_num) hN _

end Generic

section Pairing

variable (F : Type) [Field F] [NumberField F]

private theorem pairing_eq (s : ℝ) (S : Set (AdelicGL2 (𝓞 F) F)) (x y : AdelicGL2 (𝓞 F) F → ℂ) :
    peterssonIntegral F s S x y =
      ∫ w in S, x w * conj (y w) * ((ideleNorm F (Matrix.GeneralLinearGroup.det w) ^ (-s) : ℝ) : ℂ)
        ∂(adelicGLHaar (Fin 2) (𝓞 F) F) := rfl

private theorem pairing_conj (s : ℝ) (S : Set (AdelicGL2 (𝓞 F) F)) (x y : AdelicGL2 (𝓞 F) F → ℂ) :
    conj (peterssonIntegral F s S x y) = peterssonIntegral F s S y x := by
  rw [pairing_eq, pairing_eq, ← integral_conj]
  congr 1
  funext w
  rw [map_mul, map_mul, Complex.conj_conj, Complex.conj_ofReal]
  ring

private theorem pairing_self_eq (s : ℝ) (S : Set (AdelicGL2 (𝓞 F) F)) (f : AdelicGL2 (𝓞 F) F → ℂ) :
    peterssonIntegral F s S f f =
      ((∫ w in S, ‖f w‖ ^ 2 * ideleNorm F (Matrix.GeneralLinearGroup.det w) ^ (-s) ∂(adelicGLHaar (Fin 2) (𝓞 F) F) : ℝ) :
        ℂ) := by
  rw [pairing_eq]
  have h : ∀ w : AdelicGL2 (𝓞 F) F,
      f w * conj (f w) * ((ideleNorm F (Matrix.GeneralLinearGroup.det w) ^ (-s) : ℝ) : ℂ) =
        ((‖f w‖ ^ 2 * ideleNorm F (Matrix.GeneralLinearGroup.det w) ^ (-s) : ℝ) : ℂ) := fun w => by
    rw [Complex.mul_conj, Complex.ofReal_mul, Complex.normSq_eq_norm_sq, Complex.ofReal_pow]
  simp_rw [h]
  exact integral_ofReal

private theorem pairing_self_re_nonneg (s : ℝ) (S : Set (AdelicGL2 (𝓞 F) F)) (f : AdelicGL2 (𝓞 F) F → ℂ) :
    0 ≤ (peterssonIntegral F s S f f).re := by
  rw [pairing_self_eq, Complex.ofReal_re]
  exact integral_nonneg fun w => mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (ideleNorm_pos _).le _)

private theorem two_le_absNorm (v : HeightOneSpectrum (𝓞 F)) : 2 ≤ Ideal.absNorm v.asIdeal := by
  have h0 : Ideal.absNorm v.asIdeal ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]
    exact v.ne_bot
  have h1 : Ideal.absNorm v.asIdeal ≠ 1 := by
    rw [Ne, Ideal.absNorm_eq_one_iff]
    exact v.isPrime.ne_top
  omega

end Pairing

section OffExceptional

variable (F : Type) [Field F] [NumberField F]

private theorem bounds_of_not_mem_exceptionalSet
    (pins : CarrierPins F) (Φ : HeckeEigensystem F ℂ) (R' : SmoothCuspRealizationAt F pins Φ) (s : ℝ)
    (P : (AdelicGL2 (𝓞 F) F → ℂ) →ₗ[ℂ] (AdelicGL2 (𝓞 F) F → ℂ) →ₗ⋆[ℂ] ℂ)
    (hPcov : ∀ g : AdelicGL2 (𝓞 F) F, ∀ x y : AdelicGL2 (𝓞 F) F → ℂ,
      x ∈ Submodule.span ℂ (Set.range fun h : AdelicGL2 (𝓞 F) F => fun z => R'.toFun (z * h)) →
      y ∈ Submodule.span ℂ (Set.range fun h : AdelicGL2 (𝓞 F) F => fun z => R'.toFun (z * h)) →
      P (fun z => x (z * g)) (fun z => y (z * g)) =
        ((ideleNorm F (Matrix.GeneralLinearGroup.det g) ^ s : ℝ) : ℂ) * P x y)
    (hherm : ∀ x ∈ Submodule.span ℂ (Set.range fun h : AdelicGL2 (𝓞 F) F => fun z => R'.toFun (z * h)),
      ∀ y ∈ Submodule.span ℂ (Set.range fun h : AdelicGL2 (𝓞 F) F => fun z => R'.toFun (z * h)),
      conj (P x y) = P y x)
    (hpos : ∀ x ∈ Submodule.span ℂ (Set.range fun h : AdelicGL2 (𝓞 F) F => fun z => R'.toFun (z * h)),
      0 ≤ (P x x).re)
    (hne : P R'.toFun R'.toFun ≠ 0)
    (v : HeightOneSpectrum (𝓞 F)) (hv : v ∉ R'.exceptionalSet)
    (hgen : pins.gen v = diagOne (uniformizerIdele F v))
    (hnormv : ideleNorm F (uniformizerIdele F v) = ((Ideal.absNorm v.asIdeal : ℕ) : ℝ)⁻¹) :
    ‖Φ.a v‖ ≤ (((Ideal.absNorm v.asIdeal : ℕ) : ℝ) + 1) * ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-s / 2) ∧
    ‖Φ.b v‖ = ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-s) := by

  have memV : ∀ h : AdelicGL2 (𝓞 F) F, (fun z => R'.toFun (z * h)) ∈
      Submodule.span ℂ (Set.range fun h : AdelicGL2 (𝓞 F) F => fun z => R'.toFun (z * h)) :=
    fun h => Submodule.subset_span ⟨h, rfl⟩
  have fmem : R'.toFun ∈ Submodule.span ℂ (Set.range fun h : AdelicGL2 (𝓞 F) F => fun z => R'.toFun (z * h)) := by
    simpa using memV 1

  set N : ℝ := ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) with hN
  have hN2 : 2 ≤ N := by
    rw [hN]
    exact_mod_cast two_le_absNorm F v
  have hNpos : 0 < N := by linarith

  have hreal : (((P R'.toFun R'.toFun).re : ℝ) : ℂ) = P R'.toFun R'.toFun :=
    Complex.conj_eq_iff_re.mp (hherm _ fmem _ fmem)
  have hc₀pos : 0 < (P R'.toFun R'.toFun).re := by
    rcases (hpos _ fmem).eq_or_lt with h | h
    · exact absurd (by rw [← hreal, ← h, Complex.ofReal_zero]) hne
    · exact h
  have hnormff : ‖P R'.toFun R'.toFun‖ = (P R'.toFun R'.toFun).re := by
    rw [← hreal, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc₀pos, Complex.ofReal_re]

  have hcovff : ∀ g : AdelicGL2 (𝓞 F) F, P (fun z => R'.toFun (z * g)) (fun z => R'.toFun (z * g)) =
      ((ideleNorm F (Matrix.GeneralLinearGroup.det g) ^ s : ℝ) : ℂ) * P R'.toFun R'.toFun :=
    fun g => hPcov g _ _ fmem fmem

  have hlev : ∀ w ∈ pins.U Φ.level, ideleNorm F (Matrix.GeneralLinearGroup.det w) ^ s = 1 := by
    intro w hw
    have hfun : (fun z => R'.toFun (z * w)) = R'.toFun := funext fun z => R'.level_invariant z w hw
    have h := hcovff w
    rw [hfun] at h
    have h2 : ((ideleNorm F (Matrix.GeneralLinearGroup.det w) ^ s : ℝ) : ℂ) = 1 :=
      (mul_right_cancel₀ hne (h.symm.trans (one_mul _).symm))
    exact_mod_cast h2

  obtain ⟨reps, hsys, heig⟩ := R'.hecke_eigen v hv

  have hdet_reps : ∀ i, ideleNorm F (Matrix.GeneralLinearGroup.det (reps i)) ^ s = N ^ (-s) := by
    intro i
    obtain ⟨u₁, hu₁, u₂, hu₂, heq⟩ := HeckePair.mem_doubleCoset_iff.mp (hsys.mem_doubleCoset i)
    have e1 : Matrix.GeneralLinearGroup.det (reps i) =
        Matrix.GeneralLinearGroup.det u₁ * uniformizerIdele F v * Matrix.GeneralLinearGroup.det u₂ := by
      rw [← heq, map_mul, map_mul, hgen, det_diagOne]
    rw [e1, ideleNorm_mul, ideleNorm_mul,
      Real.mul_rpow (mul_nonneg (ideleNorm_pos _).le (ideleNorm_pos _).le) (ideleNorm_pos _).le,
      Real.mul_rpow (ideleNorm_pos _).le (ideleNorm_pos _).le, hlev u₁ hu₁, hlev u₂ hu₂, one_mul, mul_one, hnormv,
      Real.inv_rpow hNpos.le, Real.rpow_neg hNpos.le]

  have hsum : (∑ i, fun z => R'.toFun (z * reps i)) = Φ.a v • R'.toFun := by
    funext z
    rw [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    exact heig z
  have hPsum : Φ.a v * P R'.toFun R'.toFun = ∑ i, P (fun z => R'.toFun (z * reps i)) R'.toFun := by
    have h := congrArg (fun x => P x R'.toFun) hsum
    simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul] at h
    exact h.symm

  have hterm : ∀ i, ‖P (fun z => R'.toFun (z * reps i)) R'.toFun‖ ≤ N ^ (-s / 2) * (P R'.toFun R'.toFun).re := by
    intro i
    have hcs := norm_mul_self_le P _ hherm hpos (memV (reps i)) fmem
    have huu : (P (fun z => R'.toFun (z * reps i)) (fun z => R'.toFun (z * reps i))).re = N ^ (-s) * (P R'.toFun R'.toFun).re := by
      rw [hcovff (reps i), hdet_reps i, Complex.re_ofReal_mul]
    rw [huu] at hcs
    have hb : 0 ≤ N ^ (-s / 2) * (P R'.toFun R'.toFun).re := mul_nonneg (Real.rpow_nonneg hNpos.le _) hc₀pos.le
    have hhalf : N ^ (-s / 2) * N ^ (-s / 2) = N ^ (-s) := by
      rw [← Real.rpow_add hNpos]
      ring_nf
    have hsq : ‖P (fun z => R'.toFun (z * reps i)) R'.toFun‖ * ‖P (fun z => R'.toFun (z * reps i)) R'.toFun‖ ≤
        (N ^ (-s / 2) * (P R'.toFun R'.toFun).re) * (N ^ (-s / 2) * (P R'.toFun R'.toFun).re) := by
      calc _ ≤ N ^ (-s) * (P R'.toFun R'.toFun).re * (P R'.toFun R'.toFun).re := hcs
        _ = (N ^ (-s / 2) * (P R'.toFun R'.toFun).re) * (N ^ (-s / 2) * (P R'.toFun R'.toFun).re) := by rw [← hhalf]; ring
    exact (mul_self_le_mul_self_iff (norm_nonneg _) hb).mpr hsq

  have hA : ‖Φ.a v‖ ≤ (N + 1) * N ^ (-s / 2) := by
    have h1 : ‖Φ.a v‖ * (P R'.toFun R'.toFun).re ≤ (N + 1) * N ^ (-s / 2) * (P R'.toFun R'.toFun).re := by
      calc ‖Φ.a v‖ * (P R'.toFun R'.toFun).re = ‖Φ.a v * P R'.toFun R'.toFun‖ := by rw [norm_mul, hnormff]
        _ = ‖∑ i, P (fun z => R'.toFun (z * reps i)) R'.toFun‖ := by rw [hPsum]
        _ ≤ ∑ i, ‖P (fun z => R'.toFun (z * reps i)) R'.toFun‖ := norm_sum_le _ _
        _ ≤ ∑ _i : Fin (Ideal.absNorm v.asIdeal + 1), N ^ (-s / 2) * (P R'.toFun R'.toFun).re := Finset.sum_le_sum fun i _ => hterm i
        _ = (N + 1) * N ^ (-s / 2) * (P R'.toFun R'.toFun).re := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hN]
          push_cast
          ring
    exact le_of_mul_le_mul_right h1 hc₀pos

  have hcen := R'.central_eigen v hv
  rw [hgen, det_diagOne] at hcen
  have hcomm : ∀ w : AdelicGL2 (𝓞 F) F,
      w * centralScalar (𝓞 F) F (uniformizerIdele F v) = centralScalar (𝓞 F) F (uniformizerIdele F v) * w :=
    fun w => (scalar_mul_comm _ w).symm
  have hfunz : (fun w => R'.toFun (w * centralScalar (𝓞 F) F (uniformizerIdele F v))) = Φ.b v • R'.toFun := by
    funext w
    rw [Pi.smul_apply, smul_eq_mul, hcomm w]
    exact hcen w
  have hdetz : Matrix.GeneralLinearGroup.det (centralScalar (𝓞 F) F (uniformizerIdele F v)) =
      uniformizerIdele F v * uniformizerIdele F v := det_scalar_two _
  have hbb : ‖Φ.b v‖ * ‖Φ.b v‖ = N ^ (-s) * N ^ (-s) := by
    have h := hcovff (centralScalar (𝓞 F) F (uniformizerIdele F v))
    rw [hfunz, P.map_smul (Φ.b v) R'.toFun, LinearMap.smul_apply, (P R'.toFun).map_smulₛₗ (Φ.b v) R'.toFun, hdetz,
      ideleNorm_mul, hnormv, smul_eq_mul, smul_eq_mul, ← mul_assoc] at h
    have h2 : Φ.b v * conj (Φ.b v) = (((N⁻¹ * N⁻¹) ^ s : ℝ) : ℂ) := mul_right_cancel₀ hne h
    rw [Complex.mul_conj, Complex.ofReal_inj, Complex.normSq_eq_norm_sq] at h2
    rw [← pow_two, h2, Real.mul_rpow (inv_nonneg.mpr hNpos.le) (inv_nonneg.mpr hNpos.le), Real.inv_rpow hNpos.le,
      Real.rpow_neg hNpos.le]
  have hB : ‖Φ.b v‖ = N ^ (-s) := by
    have h0 : 0 ≤ N ^ (-s) := Real.rpow_nonneg hNpos.le _
    rcases mul_self_eq_mul_self_iff.mp hbb with h | h
    · exact h
    · have hz : ‖Φ.b v‖ = 0 := le_antisymm (by linarith [norm_nonneg (Φ.b v)]) (norm_nonneg _)
      linarith
  exact ⟨hA, hB⟩

end OffExceptional

end PeterssonCoefficientBound

open PeterssonCoefficientBound in
theorem solution
    (F : Type) [Field F] [NumberField F] (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 F) F))
    (π' : HeckeEigensystem F ℂ)
    (R' : SmoothCuspRealizationAt F
      (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v) (adelicBox F))
      π'.toRawCentral)
    (s : ℝ)
    (S : Set (AdelicGL2 (𝓞 F) F))
    (hpair :
      (∀ g : AdelicGL2 (𝓞 F) F, ∀ x y : AdelicGL2 (𝓞 F) F → ℂ,
        x ∈ Submodule.span ℂ (Set.range fun h : AdelicGL2 (𝓞 F) F => fun z => R'.toFun (z * h)) →
        y ∈ Submodule.span ℂ (Set.range fun h : AdelicGL2 (𝓞 F) F => fun z => R'.toFun (z * h)) →
        peterssonIntegral F s S (fun z => x (z * g)) (fun z => y (z * g)) =
          ((NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det g) ^ s : ℝ) : ℂ) *
            peterssonIntegral F s S x y) ∧
      peterssonIntegral F s S R'.toFun R'.toFun ≠ 0 ∧
      (R'.centralChar = R'.centralChar →
        (∀ g : AdelicGL2 (𝓞 F) F, ∀ x y : AdelicGL2 (𝓞 F) F → ℂ,
          x ∈ Submodule.span ℂ (Set.range fun h : AdelicGL2 (𝓞 F) F => fun z => R'.toFun (z * h)) ⊔
              Submodule.span ℂ (Set.range fun h : AdelicGL2 (𝓞 F) F => fun z => R'.toFun (z * h)) →
          y ∈ Submodule.span ℂ (Set.range fun h : AdelicGL2 (𝓞 F) F => fun z => R'.toFun (z * h)) →
          peterssonIntegral F s S (fun z => x (z * g)) (fun z => y (z * g)) =
            ((NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det g) ^ s : ℝ) : ℂ) *
              peterssonIntegral F s S x y) ∧
        ∃ P : (AdelicGL2 (𝓞 F) F → ℂ) →ₗ[ℂ] (AdelicGL2 (𝓞 F) F → ℂ) →ₗ⋆[ℂ] ℂ,
          (∀ g : AdelicGL2 (𝓞 F) F, ∀ x y : AdelicGL2 (𝓞 F) F → ℂ,
            x ∈ Submodule.span ℂ (Set.range fun h : AdelicGL2 (𝓞 F) F => fun z => R'.toFun (z * h)) ⊔
                Submodule.span ℂ (Set.range fun h : AdelicGL2 (𝓞 F) F => fun z => R'.toFun (z * h)) →
            y ∈ Submodule.span ℂ (Set.range fun h : AdelicGL2 (𝓞 F) F => fun z => R'.toFun (z * h)) →
            P (fun z => x (z * g)) (fun z => y (z * g)) =
              ((NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det g) ^ s : ℝ) : ℂ) * P x y) ∧
          (∃ y ∈ Submodule.span ℂ (Set.range fun h : AdelicGL2 (𝓞 F) F => fun z => R'.toFun (z * h)),
            P y y ≠ 0) ∧
          ∀ x y : AdelicGL2 (𝓞 F) F → ℂ,
            x ∈ Submodule.span ℂ (Set.range fun h : AdelicGL2 (𝓞 F) F => fun z => R'.toFun (z * h)) ⊔
                Submodule.span ℂ (Set.range fun h : AdelicGL2 (𝓞 F) F => fun z => R'.toFun (z * h)) →
            y ∈ Submodule.span ℂ (Set.range fun h : AdelicGL2 (𝓞 F) F => fun z => R'.toFun (z * h)) →
            P x y = peterssonIntegral F s S x y))
    (hnorm : ∀ v : HeightOneSpectrum (𝓞 F),
      ideleNorm F (uniformizerIdele F v) = ((Ideal.absNorm v.asIdeal : ℕ) : ℝ)⁻¹) :
    ∃ κ : ℝ, 0 ≤ κ ∧ ∀ v : HeightOneSpectrum (𝓞 F),
      ‖π'.a v‖ ≤ ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ κ ∧ ‖π'.b v‖ ≤ ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ κ := by

  obtain ⟨-, hne, hP⟩ := hpair
  obtain ⟨-, P, hPcov, -, hPagree⟩ := hP rfl
  have hPcov' : ∀ g : AdelicGL2 (𝓞 F) F, ∀ x y : AdelicGL2 (𝓞 F) F → ℂ,
      x ∈ Submodule.span ℂ (Set.range fun h : AdelicGL2 (𝓞 F) F => fun z => R'.toFun (z * h)) →
      y ∈ Submodule.span ℂ (Set.range fun h : AdelicGL2 (𝓞 F) F => fun z => R'.toFun (z * h)) →
      P (fun z => x (z * g)) (fun z => y (z * g)) =
        ((ideleNorm F (Matrix.GeneralLinearGroup.det g) ^ s : ℝ) : ℂ) * P x y :=
    fun g x y hx hy => hPcov g x y (Submodule.mem_sup_left hx) hy
  have hherm : ∀ x ∈ Submodule.span ℂ (Set.range fun h : AdelicGL2 (𝓞 F) F => fun z => R'.toFun (z * h)),
      ∀ y ∈ Submodule.span ℂ (Set.range fun h : AdelicGL2 (𝓞 F) F => fun z => R'.toFun (z * h)),
      conj (P x y) = P y x := fun x hx y hy => by
    rw [hPagree x y (Submodule.mem_sup_left hx) hy, hPagree y x (Submodule.mem_sup_left hy) hx]
    exact pairing_conj F s S x y
  have hpos : ∀ x ∈ Submodule.span ℂ (Set.range fun h : AdelicGL2 (𝓞 F) F => fun z => R'.toFun (z * h)),
      0 ≤ (P x x).re := fun x hx => by
    rw [hPagree x x (Submodule.mem_sup_left hx) hx]
    exact pairing_self_re_nonneg F s S x
  have fmem : R'.toFun ∈ Submodule.span ℂ (Set.range fun h : AdelicGL2 (𝓞 F) F => fun z => R'.toFun (z * h)) := by
    simpa using (Submodule.subset_span ⟨1, rfl⟩ :
      (fun z => R'.toFun (z * 1)) ∈ Submodule.span ℂ (Set.range fun h : AdelicGL2 (𝓞 F) F => fun z => R'.toFun (z * h)))
  have hneP : P R'.toFun R'.toFun ≠ 0 := by
    rw [hPagree _ _ (Submodule.mem_sup_left fmem) fmem]
    exact hne

  have hoff : ∀ v : HeightOneSpectrum (𝓞 F), v ∉ R'.exceptionalSet →
      ‖π'.toRawCentral.a v‖ ≤
          (((Ideal.absNorm v.asIdeal : ℕ) : ℝ) + 1) * ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-s / 2) ∧
        ‖π'.toRawCentral.b v‖ = ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-s) :=
    fun v hv => bounds_of_not_mem_exceptionalSet F _ _ R' s P hPcov' hherm hpos hneP v hv rfl (hnorm v)

  refine ⟨|s| + 2 + ∑ w ∈ R'.exceptionalSet, ((⌈‖π'.a w‖⌉₊ + ⌈‖π'.b w‖⌉₊ : ℕ) : ℝ),
    add_nonneg (add_nonneg (abs_nonneg s) zero_le_two) (Finset.sum_nonneg fun w _ => Nat.cast_nonneg _),
    fun v => ?_⟩
  have hN2 : (2 : ℝ) ≤ ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) := by exact_mod_cast two_le_absNorm F v
  have hN1 : (1 : ℝ) ≤ ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) := by linarith
  have hNpos : (0 : ℝ) < ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) := by linarith
  have hsum0 : 0 ≤ ∑ w ∈ R'.exceptionalSet, ((⌈‖π'.a w‖⌉₊ + ⌈‖π'.b w‖⌉₊ : ℕ) : ℝ) :=
    Finset.sum_nonneg fun w _ => Nat.cast_nonneg _
  by_cases hv : v ∈ R'.exceptionalSet
  ·
    have hle : ((⌈‖π'.a v‖⌉₊ + ⌈‖π'.b v‖⌉₊ : ℕ) : ℝ) ≤
        ∑ w ∈ R'.exceptionalSet, ((⌈‖π'.a w‖⌉₊ + ⌈‖π'.b w‖⌉₊ : ℕ) : ℝ) :=
      Finset.single_le_sum (f := fun w => ((⌈‖π'.a w‖⌉₊ + ⌈‖π'.b w‖⌉₊ : ℕ) : ℝ)) (fun w _ => Nat.cast_nonneg _) hv
    push_cast at hle
    have ha0 : (0 : ℝ) ≤ ⌈‖π'.a v‖⌉₊ := Nat.cast_nonneg _
    have hb0 : (0 : ℝ) ≤ ⌈‖π'.b v‖⌉₊ := Nat.cast_nonneg _
    have hs0 := abs_nonneg s
    constructor
    · calc ‖π'.a v‖ ≤ ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ ((⌈‖π'.a v‖⌉₊ : ℕ) : ℝ) := le_rpow_natCeil hN2
        _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hN1 (by push_cast; linarith)
    · calc ‖π'.b v‖ ≤ ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ ((⌈‖π'.b v‖⌉₊ : ℕ) : ℝ) := le_rpow_natCeil hN2
        _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hN1 (by push_cast; linarith)
  ·
    obtain ⟨ha, hb⟩ := hoff v hv
    have hκ : |s| + 2 ≤ |s| + 2 + ∑ w ∈ R'.exceptionalSet, ((⌈‖π'.a w‖⌉₊ + ⌈‖π'.b w‖⌉₊ : ℕ) : ℝ) :=
      le_add_of_nonneg_right hsum0
    rw [AutomorphicForm.HeckeEigensystem.toRawCentral_a] at ha
    rw [AutomorphicForm.HeckeEigensystem.toRawCentral_b, norm_mul, norm_inv, AutomorphicForm.HeckeEigensystem.cNorm,
      Complex.norm_natCast] at hb

    have hb' : ‖π'.b v‖ = ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) * ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-s) := by
      have h := congrArg (fun t => ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) * t) hb
      rwa [← mul_assoc, mul_inv_cancel₀ hNpos.ne', one_mul] at h
    constructor
    · refine ha.trans (le_trans ?_ (Real.rpow_le_rpow_of_exponent_le hN1 hκ))
      calc (((Ideal.absNorm v.asIdeal : ℕ) : ℝ) + 1) * ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-s / 2)
          ≤ ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (2 : ℝ) * ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ |s| :=
            mul_le_mul (by rw [Real.rpow_two]; nlinarith)
              (Real.rpow_le_rpow_of_exponent_le hN1 (by linarith [neg_le_abs s, abs_nonneg s]))
              (Real.rpow_nonneg hNpos.le _) (Real.rpow_nonneg hNpos.le _)
        _ = ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (|s| + 2) := by
            rw [← Real.rpow_add hNpos]
            ring_nf
    · rw [hb']
      refine le_trans ?_ (Real.rpow_le_rpow_of_exponent_le hN1 hκ)
      calc ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) * ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-s)
          = ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (1 + -s) := by
            rw [Real.rpow_add hNpos, Real.rpow_one]
        _ ≤ ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (|s| + 2) :=
            Real.rpow_le_rpow_of_exponent_le hN1 (by linarith [neg_le_abs s, abs_nonneg s])

end S_AutomorphicForm_exists_norm_a_le_absNorm_rpow_and_norm_b_le_of_smoothCuspRealizationAt_of_peterssonPairing
end P2MW
export P2MW.S_AutomorphicForm_exists_norm_a_le_absNorm_rpow_and_norm_b_le_of_smoothCuspRealizationAt_of_peterssonPairing (solution)
