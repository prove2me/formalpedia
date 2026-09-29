-- Prove2me | solution 1 for AlgebraicGeometry.FramedPolarisedAbelianScheme.isThetaAdapted_of_isReframe_inter
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/abf6f4e7-5666-5366-b3ce-d96ed40f55ca

import Definitions.Def_AlgebraicGeometry_ThetaReframe
import Definitions.Def_AlgebraicGeometry_ThetaLevelGroup
import Definitions.Def_AlgebraicGeometry_ProjSpace
import Theorems.Thm_AlgebraicGeometry_Polarisation_ThetaPt_act_add_and_act_baseScalar_smul
import Theorems.Thm_AlgebraicGeometry_Polarisation_SchrodingerFrame_act_ofScalar_mul_lift_mul_dualLift_sigma
import Theorems.Thm_AlgebraicGeometry_Polarisation_ThetaPt_exists_forall_act_eq_baseScalar_addChar_smul_of_forall_addMonoidHom
import Theorems.Thm_AlgebraicGeometry_ThetaLevel_schrodMat_one_and_schrodMat_mul
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_FramedPolarisedAbelianScheme_isThetaAdapted_of_isReframe_inter

set_option autoImplicit false

noncomputable section

attribute [local instance] MvPolynomial.gradedAlgebra

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.Polarisation
open scoped BigOperators

namespace K77TH3
namespace CL2

section MulFam

variable {S : Type} [CommRing S] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of S)) (L : RelativeGroupLaw S f) (𝓛 : A.Modules)
  {R : Type} [CommRing R] (t : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of S))

abbrev Sec : Type := Γ((Scheme.Modules.pullback (pullback.fst f t)).obj 𝓛, ⊤)

theorem baseScalar_add (r r' : R) : baseScalar f t (r + r') = baseScalar f t r + baseScalar f t r' :=
  map_add (baseScalarHom f t) r r'
theorem baseScalar_mul (r r' : R) : baseScalar f t (r * r') = baseScalar f t r * baseScalar f t r' :=
  map_mul (baseScalarHom f t) r r'
theorem baseScalar_zero : baseScalar f t 0 = 0 := map_zero (baseScalarHom f t)
theorem baseScalar_one : baseScalar f t 1 = 1 := map_one (baseScalarHom f t)
theorem baseScalar_sum {ι : Type} (s : Finset ι) (r : ι → R) :
    baseScalar f t (∑ i ∈ s, r i) = ∑ i ∈ s, baseScalar f t (r i) := map_sum (baseScalarHom f t) r s
theorem baseScalar_pow (r : R) (m : ℕ) : baseScalar f t (r ^ m) = baseScalar f t r ^ m := map_pow (baseScalarHom f t) r m

def mulFam {m : ℕ} (M : Matrix (Fin m) (Fin m) R) (τ : Fin m → Sec f 𝓛 t) : Fin m → Sec f 𝓛 t :=
  fun j => ∑ i, baseScalar f t (M i j) • τ i

theorem mulFam_apply {m : ℕ} (M : Matrix (Fin m) (Fin m) R) (τ : Fin m → Sec f 𝓛 t) (j : Fin m) :
    mulFam f 𝓛 t M τ j = ∑ i, baseScalar f t (M i j) • τ i := rfl

theorem mulFam_one {m : ℕ} (τ : Fin m → Sec f 𝓛 t) : mulFam f 𝓛 t 1 τ = τ := by
  funext j
  rw [mulFam_apply, Finset.sum_eq_single j]
  · rw [Matrix.one_apply_eq, baseScalar_one, one_smul]
  · intro i _ hij; rw [Matrix.one_apply_ne hij, baseScalar_zero, zero_smul]
  · intro h; exact absurd (Finset.mem_univ _) h

theorem mulFam_mul {m : ℕ} (M M' : Matrix (Fin m) (Fin m) R) (τ : Fin m → Sec f 𝓛 t) :
    mulFam f 𝓛 t (M * M') τ = mulFam f 𝓛 t M' (mulFam f 𝓛 t M τ) := by
  funext j
  simp only [mulFam_apply, Matrix.mul_apply, baseScalar_sum, baseScalar_mul, Finset.sum_smul, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun i _ => ?_
  rw [mul_comm]

def actHom (θ : ThetaPt f L 𝓛 t) : Sec f 𝓛 t →+ Sec f 𝓛 t where
  toFun := θ.act
  map_zero' := by
    have h := (ThetaPt.act_add_and_act_baseScalar_smul f L 𝓛 t θ).1 0 0
    rw [add_zero] at h
    exact left_eq_add.mp h
  map_add' := (ThetaPt.act_add_and_act_baseScalar_smul f L 𝓛 t θ).1

@[scoped simp] theorem actHom_apply (θ : ThetaPt f L 𝓛 t) (s : Sec f 𝓛 t) : actHom f L 𝓛 t θ s = θ.act s := rfl

theorem act_smul' (θ : ThetaPt f L 𝓛 t) (r : R) (s : Sec f 𝓛 t) :
    θ.act (baseScalar f t r • s) = baseScalar f t r • θ.act s :=
  (ThetaPt.act_add_and_act_baseScalar_smul f L 𝓛 t θ).2 r s

theorem act_mulFam {m : ℕ} (θ : ThetaPt f L 𝓛 t) (M : Matrix (Fin m) (Fin m) R) (τ : Fin m → Sec f 𝓛 t) (j : Fin m) :
    θ.act (mulFam f 𝓛 t M τ j) = mulFam f 𝓛 t M (fun i => θ.act (τ i)) j := by
  rw [mulFam_apply, mulFam_apply, ← actHom_apply, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [actHom_apply, act_smul']

end MulFam

end K77TH3.CL2
p2m_reactivate "P2MW.S_AlgebraicGeometry_FramedPolarisedAbelianScheme_isThetaAdapted_of_isReframe_inter.K77TH3 P2MW.S_AlgebraicGeometry_FramedPolarisedAbelianScheme_isThetaAdapted_of_isReframe_inter.K77TH3.CL2"
p2m_reactivate "P2MW.S_AlgebraicGeometry_FramedPolarisedAbelianScheme_isThetaAdapted_of_isReframe_inter.K77TH3"

namespace K77TH3
namespace CL2

section Schrod

variable {S : Type} [CommRing S] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of S)) (L : RelativeGroupLaw S f) (𝓛 : A.Modules)
  {R : Type} [CommRing R] (t : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of S))
  {g : ℕ} (δ : Fin g → ℕ) [∀ i, NeZero (δ i)] (d : ℕ) [NeZero d] (ω : R) {n : ℕ} (e : Fin n ≃ ThetaLevel.HH δ)

theorem mulFam_schrodMat_theta (h : ThetaLevel.HH δ) (τ : Fin n → Sec f 𝓛 t) (j : Fin n) :
    mulFam f 𝓛 t (ThetaLevel.schrodMat δ d R ω e (ThetaLevel.Heis.theta h)) τ j = τ (e.symm (e j + h)) := by
  rw [mulFam_apply, Finset.sum_eq_single (e.symm (e j + h))]
  · rw [ThetaLevel.schrodMat_apply]
    simp only [ThetaLevel.Heis.theta_h, ThetaLevel.Heis.theta_a, ThetaLevel.Heis.theta_k, Equiv.apply_symm_apply,
      if_true, ThetaLevel.pair_zero_left, add_zero, ThetaLevel.omegaPow_zero, baseScalar_one, one_smul]
  · intro i _ hi
    rw [ThetaLevel.schrodMat_apply, if_neg, baseScalar_zero, zero_smul]
    intro hei
    exact hi (e.injective (by rw [Equiv.apply_symm_apply]; exact hei))
  · intro hh; exact absurd (Finset.mem_univ _) hh

theorem mulFam_schrodMat_eta (k : ThetaLevel.HH δ) (τ : Fin n → Sec f 𝓛 t) (j : Fin n) :
    mulFam f 𝓛 t (ThetaLevel.schrodMat δ d R ω e (ThetaLevel.Heis.eta k)) τ j =
      baseScalar f t (ThetaLevel.omegaPow d R ω (ThetaLevel.pair δ d k (e j))) • τ j := by
  rw [mulFam_apply, Finset.sum_eq_single j]
  · rw [ThetaLevel.schrodMat_apply]
    simp only [ThetaLevel.Heis.eta_h, ThetaLevel.Heis.eta_a, ThetaLevel.Heis.eta_k, add_zero, if_true, zero_add]
  · intro i _ hi
    rw [ThetaLevel.schrodMat_apply, if_neg, baseScalar_zero, zero_smul]
    simp only [ThetaLevel.Heis.eta_h, add_zero]
    exact fun hei => hi (e.injective hei)
  · intro hh; exact absurd (Finset.mem_univ _) hh

theorem act_sigma_eq_mulFam (hω : ω ^ (2 * d) = 1) (F : SchrodingerFrame f L 𝓛 t δ) (z : ThetaLevel.Heis δ d)
    (χ : AddChar (ThetaLevel.HH δ) R) (hχ : ∀ y, χ y = ThetaLevel.thetaChar δ d R ω z.k y)
    (c : Rˣ) (hc : (c : R) = ThetaLevel.omegaPow d R ω z.a) (j : Fin n) :
    (ThetaPt.ofScalar c * F.lift z.h * F.dualLift χ).act (F.σ (e j)) =
      mulFam f 𝓛 t (ThetaLevel.schrodMat δ d R ω e z) (fun i => F.σ (e i)) j := by
  rw [SchrodingerFrame.act_ofScalar_mul_lift_mul_dualLift_sigma f L 𝓛 t δ d ω hω F z χ hχ c hc (e j), mulFam_apply,
    Finset.sum_eq_single (e.symm (e j + z.h))]
  · rw [ThetaLevel.schrodMat_apply, Equiv.apply_symm_apply, if_pos rfl]
  · intro i _ hi
    rw [ThetaLevel.schrodMat_apply, if_neg, baseScalar_zero, zero_smul]
    intro hei
    exact hi (e.injective (by rw [Equiv.apply_symm_apply]; exact hei))
  · intro hh; exact absurd (Finset.mem_univ _) hh

omit [∀ i, NeZero (δ i)] [NeZero d] in
theorem map_omegaPow {B : Type} [CommRing B] (φ : B →+* R) (ωB : B) (a : ZMod (2 * d)) :
    φ (ThetaLevel.omegaPow d B ωB a) = ThetaLevel.omegaPow d R (φ ωB) a := by
  simp [ThetaLevel.omegaPow, map_pow]

omit [∀ i, NeZero (δ i)] [NeZero d] in
theorem schrodMat_map {B : Type} [CommRing B] (φ : B →+* R) (ωB : B) (z : ThetaLevel.Heis δ d) :
    (ThetaLevel.schrodMat δ d B ωB e z).map φ = ThetaLevel.schrodMat δ d R (φ ωB) e z := by
  ext i j
  rw [Matrix.map_apply, ThetaLevel.schrodMat_apply, ThetaLevel.schrodMat_apply]
  split_ifs <;> simp [map_omegaPow]

end Schrod
p2m_reactivate "P2MW.S_AlgebraicGeometry_FramedPolarisedAbelianScheme_isThetaAdapted_of_isReframe_inter.K77TH3 P2MW.S_AlgebraicGeometry_FramedPolarisedAbelianScheme_isThetaAdapted_of_isReframe_inter.K77TH3.CL2"

section Pairing

variable {g : ℕ} (δ : Fin g → ℕ) [∀ i, NeZero (δ i)] (N : ℕ) {R : Type} [CommRing R]

theorem pow_eq_pow_mod {M : Type} [Monoid M] (x : M) {m : ℕ} (hx : x ^ m = 1) (a : ℕ) : x ^ a = x ^ (a % m) := by
  conv_lhs => rw [← Nat.mod_add_div a m, pow_add, pow_mul, hx, one_pow, mul_one]

theorem exists_forall_pow_eq_omegaPow_pair (hδd : ∏ i, δ i = N + 1) (ζ ω : R) (hζ : ζ ^ (N + 1) = 1) (hω : ω ^ 2 = ζ)
    (c : ThetaLevel.HH δ →+ ZMod (N + 1)) :
    ∃ k : ThetaLevel.HH δ, ∀ y : ThetaLevel.HH δ,
      ζ ^ (c y).val = ThetaLevel.omegaPow (N + 1) R ω (ThetaLevel.pair δ (N + 1) k y) := by
  classical
  have hdvd : ∀ i, δ i ∣ N + 1 := fun i => hδd ▸ Finset.dvd_prod_of_mem δ (Finset.mem_univ i)
  have hqmul : ∀ i, δ i * ((N + 1) / δ i) = N + 1 := fun i => Nat.mul_div_cancel' (hdvd i)

  have hsingle : ∀ (i : Fin g) (x : ZMod (δ i)),
      (Pi.single i x : ThetaLevel.HH δ) = x.val • (Pi.single i (1 : ZMod (δ i)) : ThetaLevel.HH δ) := by
    intro i x
    ext j
    rw [Pi.smul_apply]
    by_cases hj : j = i
    · subst hj; simp [nsmul_eq_mul]
    · simp [Pi.single_apply, hj]

  have hqdvd : ∀ i, (N + 1) / δ i ∣ (c (Pi.single i 1)).val := by
    intro i
    have hz : (δ i : ℕ) • (Pi.single i (1 : ZMod (δ i)) : ThetaLevel.HH δ) = 0 := by
      ext j
      rw [Pi.smul_apply, Pi.zero_apply]
      by_cases hj : j = i
      · subst hj; simp
      · simp [Pi.single_apply, hj]
    have h0 : ((δ i * (c (Pi.single i 1)).val : ℕ) : ZMod (N + 1)) = 0 := by
      rw [Nat.cast_mul, ZMod.natCast_zmod_val, ← nsmul_eq_mul, ← map_nsmul, hz, map_zero]
    rw [ZMod.natCast_eq_zero_iff] at h0
    obtain ⟨m, hm⟩ := h0
    refine ⟨m, Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero (NeZero.ne (δ i))) ?_⟩
    rw [hm, ← mul_assoc, hqmul i]
  refine ⟨fun i => (((c (Pi.single i 1)).val / ((N + 1) / δ i) : ℕ) : ZMod (δ i)), fun y => ?_⟩
  have hcy : c y = ((∑ i, (c (Pi.single i 1)).val * (y i).val : ℕ) : ZMod (N + 1)) := by
    conv_lhs => rw [← Finset.univ_sum_single y, map_sum]
    rw [Nat.cast_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hsingle i (y i), map_nsmul, nsmul_eq_mul, Nat.cast_mul, ZMod.natCast_zmod_val, mul_comm]
  have hpair : ThetaLevel.pair δ (N + 1) (fun i => (((c (Pi.single i 1)).val / ((N + 1) / δ i) : ℕ) : ZMod (δ i))) y =
      ((2 * ∑ i, (c (Pi.single i 1)).val * (y i).val : ℕ) : ZMod (2 * (N + 1))) := by
    rw [ThetaLevel.pair, Finset.mul_sum, Nat.cast_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hy : (y i : ZMod (δ i)) = (((y i).val : ℕ) : ZMod (δ i)) := (ZMod.natCast_zmod_val _).symm
    conv_lhs => rw [hy, ← Nat.cast_mul, ThetaLevel.iota_natCast δ (N + 1) i (Dvd.dvd.mul_left (hdvd i) 2), ← Nat.cast_mul]
    congr 1
    rw [Nat.mul_div_assoc 2 (hdvd i), mul_assoc, ← mul_assoc ((N + 1) / δ i), Nat.mul_div_cancel' (hqdvd i)]
  rw [hcy, hpair, ZMod.val_natCast, ← pow_eq_pow_mod ζ hζ,
    ThetaLevel.omegaPow_natCast (N + 1) R ω (by rw [pow_mul, hω, hζ]), pow_mul, hω]

end Pairing
p2m_reactivate "P2MW.S_AlgebraicGeometry_FramedPolarisedAbelianScheme_isThetaAdapted_of_isReframe_inter.K77TH3 P2MW.S_AlgebraicGeometry_FramedPolarisedAbelianScheme_isThetaAdapted_of_isReframe_inter.K77TH3.CL2"

end K77TH3.CL2
p2m_reactivate "P2MW.S_AlgebraicGeometry_FramedPolarisedAbelianScheme_isThetaAdapted_of_isReframe_inter.K77TH3 P2MW.S_AlgebraicGeometry_FramedPolarisedAbelianScheme_isThetaAdapted_of_isReframe_inter.K77TH3.CL2"
p2m_reactivate "P2MW.S_AlgebraicGeometry_FramedPolarisedAbelianScheme_isThetaAdapted_of_isReframe_inter.K77TH3 P2MW.S_AlgebraicGeometry_FramedPolarisedAbelianScheme_isThetaAdapted_of_isReframe_inter.K77TH3.CL2"

namespace K77TH3
namespace CL2

section Framed

variable {g N n : ℕ} {S : Type} [CommRing S] (X : FramedPolarisedAbelianScheme g N n S)

def fsharp (r : S) : Γ(X.A, ⊤) := (X.f.appLE ⊤ ⊤ le_top).hom ((Scheme.ΓSpecIso (CommRingCat.of S)).inv.hom r)

theorem fsharp_def (r : S) : fsharp X r = (X.f.appLE ⊤ ⊤ le_top).hom ((Scheme.ΓSpecIso (CommRingCat.of S)).inv.hom r) := rfl

theorem fsharp_one : fsharp X 1 = 1 := by simp [fsharp]
theorem fsharp_zero : fsharp X 0 = 0 := by simp [fsharp]

theorem appLE_top_eq_appTop : X.f.appLE ⊤ ⊤ le_top = X.f.appTop := (Scheme.Hom.app_eq_appLE X.f).symm

def plsTop (s : Γ(X.pol, ⊤)) : Sec X.f X.pol (𝟙 (Spec (CommRingCat.of S))) :=
  Scheme.Modules.pullbackLocalSection (pullback.fst X.f (𝟙 (Spec (CommRingCat.of S)))) s

theorem fst_app_fsharp (r : S) :
    (pullback.fst X.f (𝟙 (Spec (CommRingCat.of S)))).app ⊤ (fsharp X r) =
      baseScalar X.f (𝟙 (Spec (CommRingCat.of S))) r := by
  unfold baseScalar fsharp
  rw [appLE_top_eq_appTop]
  have hc : pullback.snd X.f (𝟙 (Spec (CommRingCat.of S))) = pullback.fst X.f (𝟙 _) ≫ X.f := by
    rw [pullback.condition, Category.comp_id]
  rw [hc, Scheme.Hom.comp_appTop]
  rfl

theorem plsTop_smul (r : S) (s : Γ(X.pol, ⊤)) :
    plsTop X (fsharp X r • s) = baseScalar X.f (𝟙 (Spec (CommRingCat.of S))) r • plsTop X s := by
  have h : plsTop X (fsharp X r • s) =
      (((pullback.fst X.f (𝟙 (Spec (CommRingCat.of S)))).app ⊤ (fsharp X r)) •
        (Scheme.Modules.pullbackLocalSection (pullback.fst X.f (𝟙 (Spec (CommRingCat.of S)))) s) :
          Γ((Scheme.Modules.pullback (pullback.fst X.f (𝟙 (Spec (CommRingCat.of S))))).obj X.pol,
            (pullback.fst X.f (𝟙 (Spec (CommRingCat.of S)))) ⁻¹ᵁ ⊤)) :=
    Scheme.Modules.pullbackLocalSection_smul _ _ _
  rw [h, fst_app_fsharp]
  rfl

theorem plsTop_add (s s' : Γ(X.pol, ⊤)) : plsTop X (s + s') = plsTop X s + plsTop X s' :=
  Scheme.Modules.pullbackLocalSection_add _ _ _

theorem plsTop_sum {m : ℕ} (s : Fin m → Γ(X.pol, ⊤)) : plsTop X (∑ j, s j) = ∑ j, plsTop X (s j) :=
  Scheme.Modules.pullbackLocalSection_sum _ _ _

theorem plsTop_sum_fsharp_smul {m : ℕ} (c : Fin m → S) (s : Fin m → Γ(X.pol, ⊤)) :
    plsTop X (∑ j, fsharp X (c j) • s j) = ∑ j, baseScalar X.f (𝟙 (Spec (CommRingCat.of S))) (c j) • plsTop X (s j) := by
  rw [plsTop_sum]
  exact Finset.sum_congr rfl fun j _ => plsTop_smul X (c j) (s j)

end Framed
p2m_reactivate "P2MW.S_AlgebraicGeometry_FramedPolarisedAbelianScheme_isThetaAdapted_of_isReframe_inter.K77TH3 P2MW.S_AlgebraicGeometry_FramedPolarisedAbelianScheme_isThetaAdapted_of_isReframe_inter.K77TH3.CL2"

section Coeff

variable {S : Type} [CommRing S] {ι : Type} [Fintype ι] {m : ℕ} (e : Fin m ≃ ι)

def coeffMap (T : Matrix (Fin m) (Fin m) S) (c : ι → S) : ι → S :=
  fun x => ∑ y, T (e.symm x) (e.symm y) * c y

theorem coeffMap_apply (T : Matrix (Fin m) (Fin m) S) (c : ι → S) (x : ι) :
    coeffMap e T c x = ∑ y, T (e.symm x) (e.symm y) * c y := rfl

theorem coeffMap_mul (T T' : Matrix (Fin m) (Fin m) S) (c : ι → S) :
    coeffMap e (T * T') c = coeffMap e T (coeffMap e T' c) := by
  funext x
  simp only [coeffMap_apply, Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  rw [← Equiv.sum_comp e.symm (fun l => ∑ y, T (e.symm x) l * T' l (e.symm y) * c y)]
  refine Finset.sum_congr rfl fun z _ => Finset.sum_congr rfl fun y _ => ?_
  ring

theorem coeffMap_one (c : ι → S) : coeffMap e 1 c = c := by
  funext x
  rw [coeffMap_apply, Finset.sum_eq_single x]
  · rw [Matrix.one_apply_eq, one_mul]
  · intro y _ hy
    rw [Matrix.one_apply_ne (fun h => hy (e.symm.injective h).symm), zero_mul]
  · intro h; exact absurd (Finset.mem_univ _) h

theorem coeffMap_bijective (T : Matrix (Fin m) (Fin m) S) (hT : IsUnit T) : Function.Bijective (coeffMap e T) := by
  obtain ⟨u, rfl⟩ := hT
  refine Function.bijective_iff_has_inverse.mpr ⟨coeffMap e (↑u⁻¹ : Matrix (Fin m) (Fin m) S), fun c => ?_, fun c => ?_⟩
  · show coeffMap e (↑u⁻¹) (coeffMap e (↑u) c) = c
    rw [← coeffMap_mul, Units.inv_mul, coeffMap_one]
  · show coeffMap e (↑u) (coeffMap e (↑u⁻¹) c) = c
    rw [← coeffMap_mul, Units.mul_inv, coeffMap_one]

end Coeff
p2m_reactivate "P2MW.S_AlgebraicGeometry_FramedPolarisedAbelianScheme_isThetaAdapted_of_isReframe_inter.K77TH3 P2MW.S_AlgebraicGeometry_FramedPolarisedAbelianScheme_isThetaAdapted_of_isReframe_inter.K77TH3.CL2"

end K77TH3.CL2
p2m_reactivate "P2MW.S_AlgebraicGeometry_FramedPolarisedAbelianScheme_isThetaAdapted_of_isReframe_inter.K77TH3 P2MW.S_AlgebraicGeometry_FramedPolarisedAbelianScheme_isThetaAdapted_of_isReframe_inter.K77TH3.CL2"
p2m_reactivate "P2MW.S_AlgebraicGeometry_FramedPolarisedAbelianScheme_isThetaAdapted_of_isReframe_inter.K77TH3 P2MW.S_AlgebraicGeometry_FramedPolarisedAbelianScheme_isThetaAdapted_of_isReframe_inter.K77TH3.CL2"

namespace K77TH3
namespace CL2

section Chars

variable {g : ℕ} (δ : Fin g → ℕ) [∀ i, NeZero (δ i)] (d : ℕ) [NeZero d] {R : Type} [CommRing R] (ω : R)

def chi (hω : ω ^ (2 * d) = 1) (k : ThetaLevel.HH δ) : AddChar (ThetaLevel.HH δ) R where
  toFun := ThetaLevel.thetaChar δ d R ω k
  map_zero_eq_one' := by simp [ThetaLevel.thetaChar, ThetaLevel.pair_zero_right, ThetaLevel.omegaPow_zero]
  map_add_eq_mul' a b := by
    simp [ThetaLevel.thetaChar, ThetaLevel.pair_add_right, ThetaLevel.omegaPow_add d R ω hω]

@[scoped simp] theorem chi_apply (hω : ω ^ (2 * d) = 1) (k y : ThetaLevel.HH δ) :
    chi δ d ω hω k y = ThetaLevel.thetaChar δ d R ω k y := rfl

omit [∀ i, NeZero (δ i)] [NeZero d] in
theorem isUnit_omegaPow (hω : ω ^ (2 * d) = 1) (hd : 2 * d ≠ 0) (a : ZMod (2 * d)) :
    IsUnit (ThetaLevel.omegaPow d R ω a) := by
  unfold ThetaLevel.omegaPow
  exact (IsUnit.of_pow_eq_one hω hd).pow _

end Chars
p2m_reactivate "P2MW.S_AlgebraicGeometry_FramedPolarisedAbelianScheme_isThetaAdapted_of_isReframe_inter.K77TH3 P2MW.S_AlgebraicGeometry_FramedPolarisedAbelianScheme_isThetaAdapted_of_isReframe_inter.K77TH3.CL2"

end K77TH3.CL2
p2m_reactivate "P2MW.S_AlgebraicGeometry_FramedPolarisedAbelianScheme_isThetaAdapted_of_isReframe_inter.K77TH3 P2MW.S_AlgebraicGeometry_FramedPolarisedAbelianScheme_isThetaAdapted_of_isReframe_inter.K77TH3.CL2"
p2m_reactivate "P2MW.S_AlgebraicGeometry_FramedPolarisedAbelianScheme_isThetaAdapted_of_isReframe_inter.K77TH3 P2MW.S_AlgebraicGeometry_FramedPolarisedAbelianScheme_isThetaAdapted_of_isReframe_inter.K77TH3.CL2"

open K77TH3.CL2 in
theorem solution
    (g N n : ℕ) (δ : Fin g → ℕ) [hδ : ∀ i, NeZero (δ i)] (hδd : ∏ i, δ i = N + 1)
    (e : Fin (N + 1) ≃ ((i : Fin g) → ZMod (δ i)))
    (B : Type) [CommRing B] (hd : IsUnit ((N + 1 : ℕ) : B))
    (ζ : B) (hζ : ζ ^ (N + 1) = 1) (hζu : ∀ j : ℕ, 0 < j → j < N + 1 → IsUnit (1 - ζ ^ j))
    (ω : B) (hω : ω ^ 2 = ζ)
    {S : Type} [CommRing S] (φB : B →+* S) (γ : (ThetaLevel.Heis.Gam (δ := δ) (d := N + 1)))
    (X X' : FramedPolarisedAbelianScheme g N n S)
    (hre : X.IsReframe ((Matrix.transpose (ThetaLevel.inter δ (N + 1) B ω e ((γ)⁻¹).1)).map φB) X') (hX : X.IsThetaAdapted δ e) :
    X'.IsThetaAdapted δ e := by
  classical
  obtain ⟨P', h₁, h₂, rfl, hσ⟩ := hre
  obtain ⟨F, hF⟩ := hX

  have hF' : ∀ i, F.σ (e i) = plsTop X (X.frame.σ i) := hF
  set T : Matrix (Fin (N + 1)) (Fin (N + 1)) B := ThetaLevel.inter δ (N + 1) B ω e ((γ)⁻¹).1 with hTdef
  have hσ' : ∀ i, plsTop X (P'.σ i) = ∑ j, baseScalar X.f (𝟙 _) (φB (T j i)) • F.σ (e j) := by
    intro i
    rw [hσ i]
    change plsTop X (∑ j, fsharp X (((Matrix.transpose T).map φB) i j) • X.frame.σ j) = _
    rw [plsTop_sum_fsharp_smul]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hF' j, Matrix.map_apply, Matrix.transpose_apply]

  have hωS2 : φB ω ^ 2 = φB ζ := by rw [← map_pow, hω]
  have hζS : φB ζ ^ (N + 1) = 1 := by rw [← map_pow, hζ, map_one]
  have hωS : φB ω ^ (2 * (N + 1)) = 1 := by rw [pow_mul, hωS2, hζS]
  have hζuS : ∀ j : ℕ, 0 < j → j < N + 1 → IsUnit (1 - φB ζ ^ j) := by
    intro j hj hj'
    have := (hζu j hj hj').map φB
    rwa [map_sub, map_one, map_pow] at this
  have h2d : 2 * (N + 1) ≠ 0 := by omega
  by_cases hT : ∃ U : Matrix (Fin (N + 1)) (Fin (N + 1)) B, ThetaLevel.IsIntertwiner δ (N + 1) B ω e ((γ)⁻¹).1 U
  swap
  ·
    have h1 : T = 1 := by rw [hTdef]; exact ThetaLevel.inter_of_not_exists δ (N + 1) B ω e _ hT
    refine ⟨F, fun i => ?_⟩
    change F.σ (e i) = plsTop X (P'.σ i)
    rw [hσ' i, Finset.sum_eq_single i]
    · rw [h1, Matrix.one_apply_eq, map_one, baseScalar_one, one_smul]
    · intro j _ hj; rw [h1, Matrix.one_apply_ne hj, map_zero, baseScalar_zero, zero_smul]
    · intro h; exact absurd (Finset.mem_univ _) h

  obtain ⟨hTu, hTint⟩ := (show ThetaLevel.IsIntertwiner δ (N + 1) B ω e ((γ)⁻¹).1 T from
    hTdef ▸ ThetaLevel.isIntertwiner_inter δ (N + 1) B ω e _ hT)
  set TS : Matrix (Fin (N + 1)) (Fin (N + 1)) S := T.map φB with hTS
  have hTSu : IsUnit TS := by rw [hTS]; exact hTu.map (RingHom.mapMatrix φB : Matrix _ _ B →+* Matrix _ _ S)
  have hTSint : ∀ z, TS * ThetaLevel.schrodMat δ (N + 1) S (φB ω) e z =
      ThetaLevel.schrodMat δ (N + 1) S (φB ω) e (((γ)⁻¹).1 z) * TS := by
    intro z
    have := congrArg (fun M : Matrix (Fin (N + 1)) (Fin (N + 1)) B => M.map φB) (hTint z)
    simpa only [Matrix.map_mul, schrodMat_map, hTS] using this

  set τ : Fin (N + 1) → Sec X.f X.pol (𝟙 (Spec (CommRingCat.of S))) := fun i => F.σ (e i) with hτ
  set σfin : Fin (N + 1) → Sec X.f X.pol (𝟙 (Spec (CommRingCat.of S))) := mulFam X.f X.pol (𝟙 _) TS τ with hσfin
  set σ' : ThetaLevel.HH δ → Sec X.f X.pol (𝟙 (Spec (CommRingCat.of S))) := fun y => σfin (e.symm y) with hσ'def

  set Θ : ThetaLevel.Heis δ (N + 1) → ThetaPt X.f X.L X.pol (𝟙 (Spec (CommRingCat.of S))) := fun w =>
    ThetaPt.ofScalar (isUnit_omegaPow (N + 1) (φB ω) hωS h2d w.a).unit * F.lift w.h *
      F.dualLift (chi δ (N + 1) (φB ω) hωS w.k) with hΘ

  have key : ∀ (z : ThetaLevel.Heis δ (N + 1)) (j : Fin (N + 1)),
      (Θ (((γ)⁻¹).1 z)).act (σfin j) = mulFam X.f X.pol (𝟙 _) (ThetaLevel.schrodMat δ (N + 1) S (φB ω) e z) σfin j := by
    intro z j
    rw [hσfin, act_mulFam]
    have hact : (fun i => (Θ (((γ)⁻¹).1 z)).act (τ i)) =
        mulFam X.f X.pol (𝟙 _) (ThetaLevel.schrodMat δ (N + 1) S (φB ω) e (((γ)⁻¹).1 z)) τ := by
      funext i
      rw [hτ, hΘ]
      exact act_sigma_eq_mulFam X.f X.L X.pol (𝟙 _) δ (N + 1) (φB ω) e hωS F (((γ)⁻¹).1 z)
        (chi δ (N + 1) (φB ω) hωS (((γ)⁻¹).1 z).k) (fun y => rfl) _ (IsUnit.unit_spec _) i
    rw [hact, ← mulFam_mul, ← hTSint z, mulFam_mul]

  have lift_act' : ∀ h y, (Θ (((γ)⁻¹).1 (ThetaLevel.Heis.theta h))).act (σ' y) = σ' (h + y) := by
    intro h y
    rw [hσ'def]
    change (Θ (((γ)⁻¹).1 (ThetaLevel.Heis.theta h))).act (σfin (e.symm y)) = σfin (e.symm (h + y))
    rw [key, mulFam_schrodMat_theta, Equiv.apply_symm_apply, add_comm y h]

  obtain ⟨kk, hkk⟩ : ∃ kk : (ThetaLevel.HH δ →+ ZMod (N + 1)) → ThetaLevel.HH δ,
      ∀ c y, φB ζ ^ (c y).val = ThetaLevel.omegaPow (N + 1) S (φB ω) (ThetaLevel.pair δ (N + 1) (kk c) y) :=
    ⟨fun c => (exists_forall_pow_eq_omegaPow_pair δ N hδd (φB ζ) (φB ω) hζS hωS2 c).choose,
      fun c => (exists_forall_pow_eq_omegaPow_pair δ N hδd (φB ζ) (φB ω) hζS hωS2 c).choose_spec⟩
  have hη : ∀ (c : ThetaLevel.HH δ →+ ZMod (N + 1)) (y : ThetaLevel.HH δ),
      (Θ (((γ)⁻¹).1 (ThetaLevel.Heis.eta (kk c)))).act (σ' y) = baseScalar X.f (𝟙 _) (φB ζ ^ (c y).val) • σ' y := by
    intro c y
    rw [hσ'def]
    change (Θ (((γ)⁻¹).1 (ThetaLevel.Heis.eta (kk c)))).act (σfin (e.symm y)) = _ • σfin (e.symm y)
    rw [key, mulFam_schrodMat_eta, Equiv.apply_symm_apply, hkk]

  have hdual := fun χ => ThetaPt.exists_forall_act_eq_baseScalar_addChar_smul_of_forall_addMonoidHom
    X.f X.L X.pol (𝟙 _) N (φB ζ) hζS hζuS δ e σ' (fun c => Θ (((γ)⁻¹).1 (ThetaLevel.Heis.eta (kk c)))) hη χ

  have basis' : Function.Bijective fun cv : ThetaLevel.HH δ → S => ∑ y, baseScalar X.f (𝟙 _) (cv y) • σ' y := by
    have hcomb : (fun cv : ThetaLevel.HH δ → S => ∑ y, baseScalar X.f (𝟙 _) (cv y) • σ' y) =
        (fun cv : ThetaLevel.HH δ → S => ∑ x, baseScalar X.f (𝟙 _) (cv x) • F.σ x) ∘ coeffMap e TS := by
      funext cv
      simp only [Function.comp_apply]
      rw [hσ'def]
      change ∑ y, baseScalar X.f (𝟙 _) (cv y) • σfin (e.symm y) = ∑ x, baseScalar X.f (𝟙 _) (coeffMap e TS cv x) • F.σ x
      simp only [hσfin, mulFam_apply, hτ, coeffMap_apply, Finset.smul_sum, smul_smul, baseScalar_sum, baseScalar_mul,
        Finset.sum_smul]
      rw [Finset.sum_comm]
      rw [← Equiv.sum_comp e (fun x => ∑ y, (baseScalar X.f (𝟙 _) (TS (e.symm x) (e.symm y)) *
        baseScalar X.f (𝟙 _) (cv y)) • F.σ x)]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun y _ => ?_
      rw [Equiv.symm_apply_apply, mul_comm]
    rw [hcomb]
    exact F.basis.comp (coeffMap_bijective e TS hTSu)

  refine ⟨⟨σ', basis', fun h => Θ (((γ)⁻¹).1 (ThetaLevel.Heis.theta h)), fun χ => (hdual χ).choose, lift_act',
    fun χ y => (hdual χ).choose_spec y⟩, fun i => ?_⟩
  change σ' (e i) = plsTop X (P'.σ i)
  rw [hσ' i, hσ'def]
  change σfin (e.symm (e i)) = _
  rw [Equiv.symm_apply_apply, hσfin, mulFam_apply]
  rfl

end
p2m_reactivate "P2MW.S_AlgebraicGeometry_FramedPolarisedAbelianScheme_isThetaAdapted_of_isReframe_inter.K77TH3 P2MW.S_AlgebraicGeometry_FramedPolarisedAbelianScheme_isThetaAdapted_of_isReframe_inter.K77TH3.CL2"

end S_AlgebraicGeometry_FramedPolarisedAbelianScheme_isThetaAdapted_of_isReframe_inter
end P2MW
export P2MW.S_AlgebraicGeometry_FramedPolarisedAbelianScheme_isThetaAdapted_of_isReframe_inter (solution)
