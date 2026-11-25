-- Prove2me | Definitions.Def_GroundTheory_PAdicHodge_UntiltGalois
-- name    : GroundTheory_PAdicHodge_UntiltGalois
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-25T09:46:37.136906+00:00
-- url     : https://prove2.me/theorems/4595f1ce-7e49-46c2-ab17-b75350d0918e
-- title:
--   Untilt Galois
-- statement:
--   Definitions and structural lemmas for Untilt Galois, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/UntiltGalois.lean

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_UntiltPerfectoid
import Theorems.Thm_GroundTheory_PAdicHodge_IsPerfectoidField_exists_mem_ker_fontaineTheta_isUnit_coeff_one
import Theorems.Thm_GroundTheory_PAdicHodge_IsPerfectoidField_ker_fontaineTheta_eq_span
import Theorems.Thm_GroundTheory_PAdicHodge_IsPerfectoidField_surjective_fontaineTheta
import Theorems.Thm_GroundTheory_PAdicHodge_fontaineTheta_map_preTiltMap
import Theorems.Thm_GroundTheory_PAdicHodge_norm_tiltMap
import Theorems.Thm_GroundTheory_PAdicHodge_tiltIntermediateField_untiltField
import Theorems.Thm_GroundTheory_PAdicHodge_tiltMap_algebraMap
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.PAdicHodge.tiltMap_algebraMap


set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
namespace GroundTheory.PAdicHodge
variable {K C : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
  [NontriviallyNormedField C] [IsUltrametricDist C] [NormedAlgebra K C]
variable {p : ℕ} [Fact p.Prime] [IsPerfectoidField K p] [IsPerfectoidField C p]
local notation "K♭" => Tilt K NormedField.valuation (normInteger K) normInteger_integers p
local notation "C♭" => Tilt C NormedField.valuation (normInteger C) normInteger_integers p
local notation "𝒪K♭" => PreTilt (normInteger K) p
local notation "𝒪C♭" => PreTilt (normInteger C) p
section Norm
theorem norm_tiltAlgEquiv_apply (N : IntermediateField K♭ C♭) [FiniteDimensional K♭ N]
    (σ : N ≃ₐ[K♭] N) (x : N) : ‖((σ x : N) : C♭)‖ = ‖(x : C♭)‖ := by
  change ‖σ x‖ = ‖x‖
  rw [NormedAlgebra.norm_eq_spectralNorm K♭, NormedAlgebra.norm_eq_spectralNorm K♭,
    ← spectralNorm_eq_of_equiv σ]
theorem norm_tiltAlgEquiv_toAlgHom_apply (N : IntermediateField K♭ C♭) [FiniteDimensional K♭ N]
    (σ : N ≃ₐ[K♭] N) (x : N) : ‖((σ.toAlgHom x : N) : C♭)‖ = ‖(x : C♭)‖ :=
  norm_tiltAlgEquiv_apply N σ x
end Norm
section IntegerHom
theorem exists_algebraMap_eq_of_mem {N : IntermediateField K♭ C♭} {x : C♭} (hx : x ∈ N)
    (hx1 : ‖x‖ ≤ 1) : ∃ a : 𝒪C♭, a ∈ integerTilt K C p N ∧ algebraMap 𝒪C♭ C♭ a = x := by
  obtain ⟨a, rfl⟩ := norm_le_one_iff_exists_algebraMap.1 hx1
  exact ⟨a, hx, rfl⟩
def integerTiltHom (N : IntermediateField K♭ C♭) (σ : N →ₐ[K♭] N)
    (hσ : ∀ x : N, ‖((σ x : N) : C♭)‖ = ‖(x : C♭)‖) :
    integerTilt K C p N →+* integerTilt K C p N :=
  have hex : ∀ a : integerTilt K C p N, ∃ a' : 𝒪C♭, a' ∈ integerTilt K C p N ∧
      algebraMap 𝒪C♭ C♭ a' = ((σ ⟨algebraMap 𝒪C♭ C♭ a, a.2⟩ : N) : C♭) := fun a =>
    exists_algebraMap_eq_of_mem (σ _).2 (by
      rw [hσ]; change ‖algebraMap 𝒪C♭ C♭ a‖ ≤ 1
      rw [norm_algebraMap_preTilt]; exact preTilt_norm_le_one _)
  { toFun := fun a => ⟨(hex a).choose, (hex a).choose_spec.1⟩
    map_one' := by
      apply Subtype.ext; apply IsFractionRing.injective 𝒪C♭ C♭
      rw [(hex 1).choose_spec.2]
      have : (⟨algebraMap 𝒪C♭ C♭ ((1 : integerTilt K C p N) : 𝒪C♭), (1 : integerTilt K C p N).2⟩ :
          N) = 1 := by
        apply Subtype.ext; simp
      rw [this, map_one]; simp
    map_mul' := fun a b => by
      apply Subtype.ext; apply IsFractionRing.injective 𝒪C♭ C♭
      rw [(hex (a * b)).choose_spec.2]
      change _ = algebraMap 𝒪C♭ C♭ ((hex a).choose * (hex b).choose)
      rw [map_mul, (hex a).choose_spec.2, (hex b).choose_spec.2]
      have : (⟨algebraMap 𝒪C♭ C♭ ((a * b : integerTilt K C p N) : 𝒪C♭), (a * b).2⟩ : N) =
          ⟨algebraMap 𝒪C♭ C♭ a, a.2⟩ * ⟨algebraMap 𝒪C♭ C♭ b, b.2⟩ := by
        apply Subtype.ext; simp
      rw [this, map_mul]; rfl
    map_zero' := by
      apply Subtype.ext; apply IsFractionRing.injective 𝒪C♭ C♭
      rw [(hex 0).choose_spec.2]
      have : (⟨algebraMap 𝒪C♭ C♭ ((0 : integerTilt K C p N) : 𝒪C♭), (0 : integerTilt K C p N).2⟩ :
          N) = 0 := by
        apply Subtype.ext; simp
      rw [this, map_zero]; simp
    map_add' := fun a b => by
      apply Subtype.ext; apply IsFractionRing.injective 𝒪C♭ C♭
      rw [(hex (a + b)).choose_spec.2]
      change _ = algebraMap 𝒪C♭ C♭ ((hex a).choose + (hex b).choose)
      rw [map_add, (hex a).choose_spec.2, (hex b).choose_spec.2]
      have : (⟨algebraMap 𝒪C♭ C♭ ((a + b : integerTilt K C p N) : 𝒪C♭), (a + b).2⟩ : N) =
          ⟨algebraMap 𝒪C♭ C♭ a, a.2⟩ + ⟨algebraMap 𝒪C♭ C♭ b, b.2⟩ := by
        apply Subtype.ext; simp
      rw [this, map_add]; rfl }
theorem algebraMap_integerTiltHom (N : IntermediateField K♭ C♭) (σ : N →ₐ[K♭] N)
    (hσ : ∀ x : N, ‖((σ x : N) : C♭)‖ = ‖(x : C♭)‖) (a : integerTilt K C p N) :
    algebraMap 𝒪C♭ C♭ (integerTiltHom N σ hσ a : 𝒪C♭) =
      ((σ ⟨algebraMap 𝒪C♭ C♭ a, a.2⟩ : N) : C♭) :=
  (Exists.choose_spec (p := fun a' => a' ∈ integerTilt K C p N ∧
      algebraMap 𝒪C♭ C♭ a' = ((σ ⟨algebraMap 𝒪C♭ C♭ a, a.2⟩ : N) : C♭)) _).2
theorem integerTiltHom_id (N : IntermediateField K♭ C♭)
    (h : ∀ x : N, ‖(((AlgHom.id K♭ N) x : N) : C♭)‖ = ‖(x : C♭)‖) :
    integerTiltHom (p := p) N (AlgHom.id K♭ N) h = RingHom.id _ := by
  ext a
  apply IsFractionRing.injective 𝒪C♭ C♭
  rw [algebraMap_integerTiltHom]
  rfl
theorem integerTiltHom_preTiltMap (N : IntermediateField K♭ C♭) (σ : N →ₐ[K♭] N)
    (hσ : ∀ x : N, ‖((σ x : N) : C♭)‖ = ‖(x : C♭)‖) (β : 𝒪K♭)
    (hβ : preTiltMap p (algebraMap K C) (norm_algebraMap' C) β ∈ integerTilt K C p N) :
    integerTiltHom N σ hσ ⟨_, hβ⟩ = ⟨_, hβ⟩ := by
  apply Subtype.ext
  apply IsFractionRing.injective 𝒪C♭ C♭
  rw [algebraMap_integerTiltHom]
  have h1 : algebraMap 𝒪C♭ C♭ (preTiltMap p (algebraMap K C) (norm_algebraMap' C) β) =
      algebraMap K♭ C♭ (algebraMap 𝒪K♭ K♭ β) := (tiltMap_algebraMap _ _ β).symm
  have h2 : (⟨algebraMap 𝒪C♭ C♭ (preTiltMap p (algebraMap K C) (norm_algebraMap' C) β), hβ⟩ : N) =
      algebraMap K♭ N (algebraMap 𝒪K♭ K♭ β) := Subtype.ext h1
  change ((σ ⟨algebraMap 𝒪C♭ C♭ (preTiltMap p (algebraMap K C) (norm_algebraMap' C) β), hβ⟩ :
    N) : C♭) = _
  rw [h2, AlgHom.commutes]
  exact h1.symm
end IntegerHom
section Identify
abbrev untiltPreTiltMap (N : IntermediateField K♭ C♭) [FiniteDimensional K♭ N] :
    PreTilt (normInteger (untiltField K C p N)) p →+* 𝒪C♭ :=
  preTiltMap p ((untiltField K C p N).val : untiltField K C p N →+* C) (norm_val _)
theorem untiltPreTiltMap_mem (N : IntermediateField K♭ C♭) [FiniteDimensional K♭ N]
    (b : PreTilt (normInteger (untiltField K C p N)) p) : untiltPreTiltMap N b ∈ integerTilt K C p N := by
  rw [mem_integerTilt]
  have h := tiltIntermediateField_untiltField (K := K) (C := C) (p := p) N
  rw [← tiltMap_algebraMap]
  have hm : tiltMap p ((untiltField K C p N).val : untiltField K C p N →+* C) (norm_val _)
      (algebraMap _ _ b) ∈ tiltIntermediateField p (untiltField K C p N) := ⟨_, rfl⟩
  rw [h] at hm
  exact hm
theorem untiltPreTiltMap_surj (N : IntermediateField K♭ C♭) [FiniteDimensional K♭ N] {a : 𝒪C♭}
    (ha : a ∈ integerTilt K C p N) :
    ∃ b : PreTilt (normInteger (untiltField K C p N)) p, untiltPreTiltMap N b = a := by
  have h := tiltIntermediateField_untiltField (K := K) (C := C) (p := p) N
  have ha' : algebraMap 𝒪C♭ C♭ a ∈ tiltIntermediateField p (untiltField K C p N) := by
    rw [h]; exact ha
  obtain ⟨y, hy⟩ := ha'
  have hy1 : ‖y‖ ≤ 1 := by
    have := norm_tiltMap (p := p) ((untiltField K C p N).val : untiltField K C p N →+* C)
      (norm_val _) y
    rw [← this]
    change ‖tiltInclusion p (untiltField K C p N) y‖ ≤ 1
    rw [hy, norm_algebraMap_preTilt]; exact preTilt_norm_le_one _
  obtain ⟨b, rfl⟩ := norm_le_one_iff_exists_algebraMap.1 hy1
  refine ⟨b, IsFractionRing.injective 𝒪C♭ C♭ ?_⟩
  rw [← hy]
  exact (tiltMap_algebraMap _ _ b).symm
def preTiltUntiltEquiv (N : IntermediateField K♭ C♭) [FiniteDimensional K♭ N] :
    PreTilt (normInteger (untiltField K C p N)) p ≃+* integerTilt K C p N :=
  RingEquiv.ofBijective ((untiltPreTiltMap N).codRestrict _ (untiltPreTiltMap_mem N))
    ⟨fun b b' h => preTiltMap_injective _ _ (congrArg Subtype.val h), fun a => by
      obtain ⟨b, hb⟩ := untiltPreTiltMap_surj N a.2
      exact ⟨b, Subtype.ext hb⟩⟩
@[simp]
theorem coe_preTiltUntiltEquiv (N : IntermediateField K♭ C♭) [FiniteDimensional K♭ N]
    (b : PreTilt (normInteger (untiltField K C p N)) p) :
    (preTiltUntiltEquiv N b : 𝒪C♭) = untiltPreTiltMap N b :=
  rfl
end Identify
theorem wittVector_map_comp {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
    (f : R →+* S) (g : S →+* T) (x : WittVector p R) :
    WittVector.map (g.comp f) x = WittVector.map g (WittVector.map f x) :=
  WittVector.ext fun _ => rfl
theorem preTiltMap_congr {L M : Type*} [NontriviallyNormedField L] [IsUltrametricDist L]
    [NontriviallyNormedField M] [IsUltrametricDist M] [IsPerfectoidField L p]
    [IsPerfectoidField M p] {f g : L →+* M} (hfg : f = g) (hf : ∀ x, ‖f x‖ = ‖x‖)
    (hg : ∀ x, ‖g x‖ = ‖x‖) : preTiltMap p f hf = preTiltMap p g hg := by
  subst hfg; rfl
section Aut
def untiltPreTiltAut (N : IntermediateField K♭ C♭) [FiniteDimensional K♭ N] (σ : N ≃ₐ[K♭] N) :
    PreTilt (normInteger (untiltField K C p N)) p →+* PreTilt (normInteger (untiltField K C p N)) p :=
  (preTiltUntiltEquiv N).symm.toRingHom.comp
    ((integerTiltHom N σ.toAlgHom (norm_tiltAlgEquiv_toAlgHom_apply N σ)).comp (preTiltUntiltEquiv N).toRingHom)
theorem preTiltUntiltEquiv_untiltPreTiltAut (N : IntermediateField K♭ C♭) [FiniteDimensional K♭ N]
    (σ : N ≃ₐ[K♭] N) (b : PreTilt (normInteger (untiltField K C p N)) p) :
    preTiltUntiltEquiv N (untiltPreTiltAut N σ b) =
      integerTiltHom N σ.toAlgHom (norm_tiltAlgEquiv_toAlgHom_apply N σ) (preTiltUntiltEquiv N b) := by
  simp [untiltPreTiltAut]
theorem untiltPreTiltAut_mul (N : IntermediateField K♭ C♭) [FiniteDimensional K♭ N]
    (σ τ : N ≃ₐ[K♭] N) :
    untiltPreTiltAut N (σ * τ) = (untiltPreTiltAut N σ).comp (untiltPreTiltAut N τ) := by
  ext b
  apply (preTiltUntiltEquiv N).injective
  rw [RingHom.comp_apply, preTiltUntiltEquiv_untiltPreTiltAut, preTiltUntiltEquiv_untiltPreTiltAut,
    preTiltUntiltEquiv_untiltPreTiltAut]
  set x := preTiltUntiltEquiv N b
  apply Subtype.ext; apply IsFractionRing.injective 𝒪C♭ C♭
  rw [algebraMap_integerTiltHom, algebraMap_integerTiltHom]
  have : (⟨algebraMap 𝒪C♭ C♭ (integerTiltHom N τ.toAlgHom (norm_tiltAlgEquiv_toAlgHom_apply N τ) x : 𝒪C♭),
      (integerTiltHom N τ.toAlgHom (norm_tiltAlgEquiv_toAlgHom_apply N τ) x).2⟩ : N) =
      τ ⟨algebraMap 𝒪C♭ C♭ x, x.2⟩ := Subtype.ext (algebraMap_integerTiltHom N _ _ x)
  rw [this]; rfl
theorem untiltPreTiltAut_one (N : IntermediateField K♭ C♭) [FiniteDimensional K♭ N] :
    untiltPreTiltAut (K := K) (C := C) (p := p) N 1 = RingHom.id _ := by
  ext b
  apply (preTiltUntiltEquiv N).injective
  rw [preTiltUntiltEquiv_untiltPreTiltAut]
  have h := integerTiltHom_id (K := K) (C := C) (p := p) N (norm_tiltAlgEquiv_toAlgHom_apply N 1)
  exact congrArg (fun f => f (preTiltUntiltEquiv N b)) h
theorem untiltPreTiltMap_preTiltMap (N : IntermediateField K♭ C♭) [FiniteDimensional K♭ N]
    (β : 𝒪K♭) :
    untiltPreTiltMap N (preTiltMap p (algebraMap K (untiltField K C p N)) (norm_algebraMap' _) β) =
      preTiltMap p (algebraMap K C) (norm_algebraMap' C) β := by
  rw [untiltPreTiltMap, ← RingHom.comp_apply, ← preTiltMap_comp]
  exact congrArg (fun f => f β) (preTiltMap_congr (L := K) (M := C)
    (f := ((untiltField K C p N).val : untiltField K C p N →+* C).comp
      (algebraMap K (untiltField K C p N))) (g := algebraMap K C) (RingHom.ext fun _ => rfl) _ _)
theorem untiltPreTiltAut_preTiltMap (N : IntermediateField K♭ C♭) [FiniteDimensional K♭ N]
    (σ : N ≃ₐ[K♭] N) (β : 𝒪K♭) :
    untiltPreTiltAut N σ (preTiltMap p (algebraMap K (untiltField K C p N)) (norm_algebraMap' _) β) =
      preTiltMap p (algebraMap K (untiltField K C p N)) (norm_algebraMap' _) β := by
  apply (preTiltUntiltEquiv N).injective
  rw [preTiltUntiltEquiv_untiltPreTiltAut]
  have hβ : preTiltMap p (algebraMap K C) (norm_algebraMap' C) β ∈ integerTilt K C p N := by
    rw [← untiltPreTiltMap_preTiltMap N β]; exact untiltPreTiltMap_mem N _
  have he : preTiltUntiltEquiv N
      (preTiltMap p (algebraMap K (untiltField K C p N)) (norm_algebraMap' _) β) = ⟨_, hβ⟩ :=
    Subtype.ext (untiltPreTiltMap_preTiltMap N β)
  rw [he]
  exact integerTiltHom_preTiltMap N σ.toAlgHom _ β hβ
end Aut
section Theta
theorem map_untiltPreTiltAut_mem_ker (N : IntermediateField K♭ C♭) [FiniteDimensional K♭ N]
    (σ : N ≃ₐ[K♭] N) {x : WittVector p (PreTilt (normInteger (untiltField K C p N)) p)}
    (hx : x ∈ RingHom.ker (WittVector.fontaineTheta (normInteger (untiltField K C p N)) p)) :
    WittVector.map (untiltPreTiltAut N σ) x ∈
      RingHom.ker (WittVector.fontaineTheta (normInteger (untiltField K C p N)) p) := by
  obtain ⟨ξK, hξK, hξ1⟩ :=
    IsPerfectoidField.exists_mem_ker_fontaineTheta_isUnit_coeff_one (K := K) (p := p)
  set φKF := preTiltMap p (algebraMap K (untiltField K C p N)) (norm_algebraMap' _)
  set ξF := WittVector.map φKF ξK
  have hξF : ξF ∈ RingHom.ker (WittVector.fontaineTheta (normInteger (untiltField K C p N)) p) := by
    rw [RingHom.mem_ker, fontaineTheta_map_preTiltMap, RingHom.mem_ker.1 hξK, map_zero]
  have hξF1 : IsUnit (ξF.coeff 1) := by
    rw [WittVector.map_coeff]; exact hξ1.map _
  have hker := IsPerfectoidField.ker_fontaineTheta_eq_span (K := untiltField K C p N) hξF hξF1
  have hfix : WittVector.map (untiltPreTiltAut N σ) ξF = ξF := by
    ext n
    simp only [ξF, WittVector.map_coeff, φKF, untiltPreTiltAut_preTiltMap]
  rw [hker] at hx ⊢
  obtain ⟨y, rfl⟩ := Ideal.mem_span_singleton'.1 hx
  rw [map_mul, hfix]
  exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)
def untiltIntegerHom (N : IntermediateField K♭ C♭) [FiniteDimensional K♭ N] (σ : N ≃ₐ[K♭] N) :
    normInteger (untiltField K C p N) →+* normInteger (untiltField K C p N) :=
  (Ideal.Quotient.lift (RingHom.ker (WittVector.fontaineTheta (normInteger (untiltField K C p N)) p))
      ((WittVector.fontaineTheta (normInteger (untiltField K C p N)) p).comp
        (WittVector.map (untiltPreTiltAut N σ)))
      (fun _ hx => map_untiltPreTiltAut_mem_ker N σ hx)).comp
    (RingHom.quotientKerEquivOfSurjective
      (IsPerfectoidField.surjective_fontaineTheta (K := untiltField K C p N) p)).symm.toRingHom
theorem untiltIntegerHom_fontaineTheta (N : IntermediateField K♭ C♭) [FiniteDimensional K♭ N]
    (σ : N ≃ₐ[K♭] N) (w : WittVector p (PreTilt (normInteger (untiltField K C p N)) p)) :
    untiltIntegerHom N σ (WittVector.fontaineTheta (normInteger (untiltField K C p N)) p w) =
      WittVector.fontaineTheta (normInteger (untiltField K C p N)) p
        (WittVector.map (untiltPreTiltAut N σ) w) := by
  simp only [untiltIntegerHom, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
    RingHom.quotientKerEquivOfSurjective_symm_apply]
  exact Ideal.Quotient.lift_mk _ _ _
theorem untiltIntegerHom_mul (N : IntermediateField K♭ C♭) [FiniteDimensional K♭ N]
    (σ τ : N ≃ₐ[K♭] N) :
    untiltIntegerHom N (σ * τ) = (untiltIntegerHom N σ).comp (untiltIntegerHom N τ) := by
  ext y
  obtain ⟨w, rfl⟩ := IsPerfectoidField.surjective_fontaineTheta (K := untiltField K C p N) p y
  rw [RingHom.comp_apply, untiltIntegerHom_fontaineTheta, untiltIntegerHom_fontaineTheta,
    untiltIntegerHom_fontaineTheta, untiltPreTiltAut_mul, wittVector_map_comp]
theorem untiltIntegerHom_one (N : IntermediateField K♭ C♭) [FiniteDimensional K♭ N] :
    untiltIntegerHom (K := K) (C := C) (p := p) N 1 = RingHom.id _ := by
  ext y
  obtain ⟨w, rfl⟩ := IsPerfectoidField.surjective_fontaineTheta (K := untiltField K C p N) p y
  rw [untiltIntegerHom_fontaineTheta, untiltPreTiltAut_one, WittVector.map_id]
  rfl
def untiltIntegerEquiv (N : IntermediateField K♭ C♭) [FiniteDimensional K♭ N] (σ : N ≃ₐ[K♭] N) :
    normInteger (untiltField K C p N) ≃+* normInteger (untiltField K C p N) :=
  RingEquiv.ofRingHom (untiltIntegerHom N σ) (untiltIntegerHom N σ⁻¹)
    (by rw [← untiltIntegerHom_mul, mul_inv_cancel, untiltIntegerHom_one])
    (by rw [← untiltIntegerHom_mul, inv_mul_cancel, untiltIntegerHom_one])
@[simp]
theorem untiltIntegerEquiv_apply (N : IntermediateField K♭ C♭) [FiniteDimensional K♭ N]
    (σ : N ≃ₐ[K♭] N) (y : normInteger (untiltField K C p N)) :
    untiltIntegerEquiv N σ y = untiltIntegerHom N σ y :=
  rfl
theorem untiltIntegerHom_integerMap (N : IntermediateField K♭ C♭) [FiniteDimensional K♭ N]
    (σ : N ≃ₐ[K♭] N) (k : normInteger K) :
    untiltIntegerHom N σ (integerMap (algebraMap K (untiltField K C p N)) (norm_algebraMap' _) k) =
      integerMap (algebraMap K (untiltField K C p N)) (norm_algebraMap' _) k := by
  obtain ⟨w, rfl⟩ := IsPerfectoidField.surjective_fontaineTheta (K := K) p k
  rw [← fontaineTheta_map_preTiltMap, untiltIntegerHom_fontaineTheta, ← wittVector_map_comp,
    show (untiltPreTiltAut N σ).comp
        (preTiltMap p (algebraMap K (untiltField K C p N)) (norm_algebraMap' _)) =
      preTiltMap p (algebraMap K (untiltField K C p N)) (norm_algebraMap' _) from
      RingHom.ext (untiltPreTiltAut_preTiltMap N σ)]
end Theta
section FieldAut
theorem ringEquivOfRingEquiv_untiltIntegerEquiv_algebraMap (N : IntermediateField K♭ C♭)
    [FiniteDimensional K♭ N] (σ : N ≃ₐ[K♭] N) (k : K) :
    IsFractionRing.ringEquivOfRingEquiv (A := normInteger (untiltField K C p N))
        (K := untiltField K C p N) (B := normInteger (untiltField K C p N))
        (L := untiltField K C p N) (untiltIntegerEquiv N σ) (algebraMap K _ k) =
      algebraMap K _ k := by
  set f := IsFractionRing.ringEquivOfRingEquiv (A := normInteger (untiltField K C p N))
    (K := untiltField K C p N) (B := normInteger (untiltField K C p N))
    (L := untiltField K C p N) (untiltIntegerEquiv N σ)
  have key : ∀ k : K, ‖k‖ ≤ 1 → f (algebraMap K _ k) = algebraMap K _ k := by
    intro k hk
    have : algebraMap K (untiltField K C p N) k =
        algebraMap (normInteger (untiltField K C p N)) (untiltField K C p N)
          (integerMap (algebraMap K (untiltField K C p N)) (norm_algebraMap' _)
            ⟨k, mem_normInteger.2 hk⟩) := rfl
    rw [this, IsFractionRing.ringEquivOfRingEquiv_algebraMap, untiltIntegerEquiv_apply,
      untiltIntegerHom_integerMap]
  rcases le_or_gt ‖k‖ 1 with h | h
  · exact key k h
  · have := key k⁻¹ (by rw [norm_inv]; exact inv_le_one_of_one_le₀ h.le)
    rw [map_inv₀, map_inv₀] at this
    exact inv_injective this
def untiltAut (N : IntermediateField K♭ C♭) [FiniteDimensional K♭ N] (σ : N ≃ₐ[K♭] N) :
    untiltField K C p N ≃ₐ[K] untiltField K C p N :=
  AlgEquiv.ofRingEquiv (f := IsFractionRing.ringEquivOfRingEquiv
    (A := normInteger (untiltField K C p N)) (K := untiltField K C p N)
    (B := normInteger (untiltField K C p N)) (L := untiltField K C p N) (untiltIntegerEquiv N σ))
    (ringEquivOfRingEquiv_untiltIntegerEquiv_algebraMap N σ)
theorem untiltAut_algebraMap (N : IntermediateField K♭ C♭) [FiniteDimensional K♭ N]
    (σ : N ≃ₐ[K♭] N) (y : normInteger (untiltField K C p N)) :
    untiltAut N σ (algebraMap _ (untiltField K C p N) y) =
      algebraMap _ (untiltField K C p N) (untiltIntegerHom N σ y) :=
  IsFractionRing.ringEquivOfRingEquiv_algebraMap _ y
theorem untiltAut_mul (N : IntermediateField K♭ C♭) [FiniteDimensional K♭ N] (σ τ : N ≃ₐ[K♭] N) :
    untiltAut N (σ * τ) = untiltAut N σ * untiltAut N τ := by
  have h : (untiltAut N (σ * τ) : untiltField K C p N →+* untiltField K C p N) =
      ((untiltAut N σ * untiltAut N τ : untiltField K C p N ≃ₐ[K] untiltField K C p N) :
        untiltField K C p N →+* untiltField K C p N) := by
    refine IsLocalization.ringHom_ext (nonZeroDivisors (normInteger (untiltField K C p N))) ?_
    refine RingHom.ext fun y => ?_
    simp only [RingHom.comp_apply, RingHom.coe_coe, AlgEquiv.mul_apply]
    rw [untiltAut_algebraMap, untiltAut_algebraMap, untiltAut_algebraMap, untiltIntegerHom_mul,
      RingHom.comp_apply]
  exact AlgEquiv.ext fun x => congrArg (fun f => f x) h
theorem untiltAut_one (N : IntermediateField K♭ C♭) [FiniteDimensional K♭ N] :
    untiltAut (K := K) (C := C) (p := p) N 1 = 1 := by
  have h : (untiltAut N 1 : untiltField K C p N →+* untiltField K C p N) =
      RingHom.id (untiltField K C p N) := by
    refine IsLocalization.ringHom_ext (nonZeroDivisors (normInteger (untiltField K C p N))) ?_
    refine RingHom.ext fun y => ?_
    simp only [RingHom.comp_apply, RingHom.coe_coe, RingHom.id_apply]
    rw [untiltAut_algebraMap, untiltIntegerHom_one]
    rfl
  exact AlgEquiv.ext fun x => congrArg (fun f => f x) h
def untiltAutHom (N : IntermediateField K♭ C♭) [FiniteDimensional K♭ N] :
    (N ≃ₐ[K♭] N) →* (untiltField K C p N ≃ₐ[K] untiltField K C p N) where
  toFun := untiltAut N
  map_one' := untiltAut_one N
  map_mul' := untiltAut_mul N
end FieldAut
end GroundTheory.PAdicHodge


