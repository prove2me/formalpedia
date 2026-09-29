-- Prove2me | solution 1 for AlgebraicGeometry.IsAffineOpen.isOpen_and_exists_differentiableOn_eval_appLE_of_forall_differentiableOn
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/47042b0b-261c-5b57-8b3a-2bd6a11b1534

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_IsAffineOpen_isOpen_and_exists_differentiableOn_eval_appLE_of_forall_differentiableOn

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry Opposite Topology

namespace EvalLoc

theorem top_le_preimage_iff {Y : Scheme.{0}} (q : Spec (CommRingCat.of ℂ) ⟶ Y) (U : Y.Opens) :
    ⊤ ≤ q ⁻¹ᵁ U ↔ q.base (IsLocalRing.closedPoint ℂ) ∈ U := by
  constructor
  · intro h
    exact h (Set.mem_univ (IsLocalRing.closedPoint ℂ))
  · intro h p _
    have hp : p = IsLocalRing.closedPoint ℂ := Subsingleton.elim _ _
    subst hp
    exact h

theorem val_fromSpec {M : Scheme.{0}} {U : M.Opens} (hU : IsAffineOpen U)
    (σ : ↑(M.presheaf.obj (op U)) →+* ℂ)
    (h : ⊤ ≤ (Spec.map (CommRingCat.ofHom σ) ≫ hU.fromSpec) ⁻¹ᵁ U) (a : ↑(M.presheaf.obj (op U))) :
    (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom (((Spec.map (CommRingCat.ofHom σ) ≫ hU.fromSpec).appLE U ⊤ h) a) = σ a := by
  rw [Scheme.Hom.comp_appLE, hU.fromSpec_app_self]
  have e1 : (Spec (M.presheaf.obj (op U))).presheaf.map (eqToHom hU.fromSpec_preimage_self).op ≫
      (Spec.map (CommRingCat.ofHom σ)).appLE (hU.fromSpec ⁻¹ᵁ U) ⊤ h =
      (Spec.map (CommRingCat.ofHom σ)).appTop := by
    rw [Scheme.Hom.map_appLE]
    simp [Scheme.Hom.appLE, Scheme.Hom.appTop]
  have key : (((Scheme.ΓSpecIso (M.presheaf.obj (op U))).inv ≫
      (Spec (M.presheaf.obj (op U))).presheaf.map (eqToHom hU.fromSpec_preimage_self).op) ≫
        (Spec.map (CommRingCat.ofHom σ)).appLE (hU.fromSpec ⁻¹ᵁ U) ⊤ h) ≫ (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom =
      CommRingCat.ofHom σ := by
    simp only [Category.assoc]
    rw [← Category.assoc ((Spec (M.presheaf.obj (op U))).presheaf.map _), e1, Scheme.ΓSpecIso_naturality]
    erw [Iso.inv_hom_id_assoc]
  have := congrFun (congrArg (fun k => (CommRingCat.Hom.hom k : _ → _)) key) a
  simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply, CommRingCat.hom_ofHom] at this
  exact this

theorem top_le_preimage_basicOpen_iff {M : Scheme.{0}} {U : M.Opens} (hU : IsAffineOpen U)
    (σ : ↑(M.presheaf.obj (op U)) →+* ℂ) (b : ↑(M.presheaf.obj (op U))) :
    ⊤ ≤ (Spec.map (CommRingCat.ofHom σ) ≫ hU.fromSpec) ⁻¹ᵁ (M.basicOpen b) ↔ σ b ≠ 0 := by
  rw [Scheme.Hom.comp_preimage, hU.fromSpec_preimage_basicOpen, top_le_preimage_iff]
  change PrimeSpectrum.comap σ (IsLocalRing.closedPoint ℂ) ∈ PrimeSpectrum.basicOpen b ↔ _
  rw [PrimeSpectrum.mem_basicOpen]
  change σ b ∉ IsLocalRing.maximalIdeal ℂ ↔ _
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, not_not, isUnit_iff_ne_zero]

theorem val_map {G : Scheme.{0}} (p : Spec (CommRingCat.of ℂ) ⟶ G) {U U' : G.Opens} (hle : U ≤ U')
    (h : ⊤ ≤ p ⁻¹ᵁ U) (h' : ⊤ ≤ p ⁻¹ᵁ U') (s : Γ(G, U')) :
    (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom ((p.appLE U ⊤ h) (G.presheaf.map (homOfLE hle).op s)) =
      (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom ((p.appLE U' ⊤ h') s) := by
  congr 1
  rw [← CommRingCat.comp_apply, Scheme.Hom.map_appLE]

end EvalLoc

open EvalLoc in
theorem solution
    (M : Scheme.{0}) (U : M.Opens) (hU : IsAffineOpen U)
    (D : Set ℂ) (hD : IsOpen D)
    (σ : ℂ → (↑(M.presheaf.obj (op U)) →+* ℂ))
    (hσ : ∀ a : ↑(M.presheaf.obj (op U)), ∃ F : ℂ → ℂ, DifferentiableOn ℂ F D ∧ ∀ w ∈ D, σ w a = F w)
    (U' : M.Opens) (s : ↑(M.presheaf.obj (op U'))) :
    IsOpen {w : ℂ | w ∈ D ∧ ⊤ ≤ (Spec.map (CommRingCat.ofHom (σ w)) ≫ hU.fromSpec) ⁻¹ᵁ U'} ∧
    ∃ G : ℂ → ℂ,
      DifferentiableOn ℂ G {w : ℂ | w ∈ D ∧ ⊤ ≤ (Spec.map (CommRingCat.ofHom (σ w)) ≫ hU.fromSpec) ⁻¹ᵁ U'} ∧
      ∀ (w : ℂ), w ∈ D → ∀ (hw : ⊤ ≤ (Spec.map (CommRingCat.ofHom (σ w)) ≫ hU.fromSpec) ⁻¹ᵁ U'),
        G w = (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom
          (((Spec.map (CommRingCat.ofHom (σ w)) ≫ hU.fromSpec).appLE U' ⊤ hw) s) := by
  classical

  set p : ℂ → (Spec (CommRingCat.of ℂ) ⟶ M) := fun w => Spec.map (CommRingCat.ofHom (σ w)) ≫ hU.fromSpec with hp
  set S : Set ℂ := {w : ℂ | w ∈ D ∧ ⊤ ≤ (Spec.map (CommRingCat.ofHom (σ w)) ≫ hU.fromSpec) ⁻¹ᵁ U'} with hS

  choose Fa hFa hFaval using hσ

  have hpU : ∀ w, ⊤ ≤ (Spec.map (CommRingCat.ofHom (σ w)) ≫ hU.fromSpec) ⁻¹ᵁ U := by
    intro w; rw [Scheme.Hom.comp_preimage, hU.fromSpec_preimage_self]; simp

  have hloc : ∀ w₀ ∈ S, ∃ (b a : ↑(M.presheaf.obj (op U))) (k : ℕ), M.basicOpen b ≤ U' ∧ σ w₀ b ≠ 0 ∧
      ∀ w ∈ D, σ w b ≠ 0 → ∃ hw : ⊤ ≤ (Spec.map (CommRingCat.ofHom (σ w)) ≫ hU.fromSpec) ⁻¹ᵁ U',
        (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom
          (((Spec.map (CommRingCat.ofHom (σ w)) ≫ hU.fromSpec).appLE U' ⊤ hw) s) * (σ w b) ^ k = σ w a := by
    rintro w₀ ⟨hw₀D, hw₀⟩

    set x₀ : M := (Spec.map (CommRingCat.ofHom (σ w₀)) ≫ hU.fromSpec).base (IsLocalRing.closedPoint ℂ) with hx₀
    have hx₀U' : x₀ ∈ U' := (top_le_preimage_iff _ _).1 hw₀
    have hx₀U : x₀ ∈ U := (top_le_preimage_iff _ _).1 (hpU w₀)
    obtain ⟨b, hbU', hx₀b⟩ := hU.exists_basicOpen_le ⟨x₀, hx₀U'⟩ hx₀U
    have hb0 : σ w₀ b ≠ 0 := (top_le_preimage_basicOpen_iff hU (σ w₀) b).1 ((top_le_preimage_iff _ _).2 hx₀b)

    haveI := hU.isLocalization_basicOpen b
    obtain ⟨⟨a, ⟨bk, k, rfl⟩⟩, hak⟩ := IsLocalization.surj (Submonoid.powers b) (M.presheaf.map (homOfLE hbU').op s)
    refine ⟨b, a, k, hbU', hb0, fun w hwD hwb => ?_⟩
    have hwb' : ⊤ ≤ (Spec.map (CommRingCat.ofHom (σ w)) ≫ hU.fromSpec) ⁻¹ᵁ (M.basicOpen b) :=
      (top_le_preimage_basicOpen_iff hU (σ w) b).2 hwb
    have hwU' : ⊤ ≤ (Spec.map (CommRingCat.ofHom (σ w)) ≫ hU.fromSpec) ⁻¹ᵁ U' :=
      (top_le_preimage_iff _ _).2 (hbU' ((top_le_preimage_iff _ _).1 hwb'))
    refine ⟨hwU', ?_⟩

    have hev := congrArg (fun t => (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom
      (((Spec.map (CommRingCat.ofHom (σ w)) ≫ hU.fromSpec).appLE (M.basicOpen b) ⊤ hwb') t)) hak
    simp only [map_mul, map_pow] at hev

    have halg : ∀ r : ↑(M.presheaf.obj (op U)), algebraMap _ (M.presheaf.obj (op (M.basicOpen b))) r =
        M.presheaf.map (homOfLE (M.basicOpen_le b)).op r := fun r => rfl
    rw [halg, halg, val_map _ hbU' hwb' hwU', val_map _ (M.basicOpen_le b) hwb' (hpU w),
      val_map _ (M.basicOpen_le b) hwb' (hpU w), val_fromSpec hU, val_fromSpec hU] at hev
    exact hev
  constructor
  ·
    rw [isOpen_iff_mem_nhds]
    intro w₀ hw₀
    obtain ⟨b, a, k, hbU', hb0, hval⟩ := hloc w₀ hw₀
    have hcont : ContinuousOn (fun w => Fa b w) D := (hFa b).continuousOn
    have hnb : {w | w ∈ D ∧ Fa b w ≠ 0} ∈ 𝓝 w₀ := by
      have ho : IsOpen ({w | w ∈ D ∧ Fa b w ≠ 0}) := by
        have : {w | w ∈ D ∧ Fa b w ≠ 0} = D ∩ (fun w => Fa b w) ⁻¹' {z | z ≠ 0} := by ext w; simp
        rw [this]; exact hcont.isOpen_inter_preimage hD isOpen_ne
      refine ho.mem_nhds ⟨hw₀.1, ?_⟩
      rw [← hFaval b w₀ hw₀.1]; exact hb0
    refine Filter.mem_of_superset hnb ?_
    rintro w ⟨hwD, hwb⟩
    rw [← hFaval b w hwD] at hwb
    exact ⟨hwD, (hval w hwD hwb).1⟩
  ·
    refine ⟨fun w => if h : w ∈ D ∧ ⊤ ≤ (Spec.map (CommRingCat.ofHom (σ w)) ≫ hU.fromSpec) ⁻¹ᵁ U' then
        (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom (((Spec.map (CommRingCat.ofHom (σ w)) ≫ hU.fromSpec).appLE U' ⊤ h.2) s)
      else 0, ?_, ?_⟩
    · intro w₀ hw₀
      obtain ⟨b, a, k, hbU', hb0, hval⟩ := hloc w₀ hw₀

      have hnb : ∀ᶠ w in 𝓝 w₀, w ∈ D ∧ Fa b w ≠ 0 := by
        have hcont : ContinuousOn (fun w => Fa b w) D := (hFa b).continuousOn
        have ho : IsOpen ({w | w ∈ D ∧ Fa b w ≠ 0}) := by
          have : {w | w ∈ D ∧ Fa b w ≠ 0} = D ∩ (fun w => Fa b w) ⁻¹' {z | z ≠ 0} := by ext w; simp
          rw [this]; exact hcont.isOpen_inter_preimage hD isOpen_ne
        exact ho.mem_nhds ⟨hw₀.1, by rw [← hFaval b w₀ hw₀.1]; exact hb0⟩
      have heq : ∀ᶠ w in 𝓝 w₀, (fun w => if h : w ∈ D ∧ ⊤ ≤ (Spec.map (CommRingCat.ofHom (σ w)) ≫ hU.fromSpec) ⁻¹ᵁ U' then
          (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom (((Spec.map (CommRingCat.ofHom (σ w)) ≫ hU.fromSpec).appLE U' ⊤ h.2) s)
          else 0) w = Fa a w / Fa b w ^ k := by
        filter_upwards [hnb] with w hw
        obtain ⟨hwD, hwb⟩ := hw
        have hwb' : σ w b ≠ 0 := by rw [hFaval b w hwD]; exact hwb
        obtain ⟨hwU', hv⟩ := hval w hwD hwb'
        rw [dif_pos ⟨hwD, hwU'⟩, eq_div_iff (pow_ne_zero _ hwb), ← hFaval a w hwD, ← hFaval b w hwD]
        exact hv
      have hdiff : DifferentiableAt ℂ (fun w => Fa a w / Fa b w ^ k) w₀ := by
        have hDn : D ∈ 𝓝 w₀ := hD.mem_nhds hw₀.1
        refine ((hFa a).differentiableAt hDn).div (((hFa b).differentiableAt hDn).pow k) ?_
        refine pow_ne_zero _ ?_
        rw [← hFaval b w₀ hw₀.1]; exact hb0
      exact (hdiff.congr_of_eventuallyEq heq).differentiableWithinAt
    · intro w hwD hw
      beta_reduce
      rw [dif_pos ⟨hwD, hw⟩]

end S_AlgebraicGeometry_IsAffineOpen_isOpen_and_exists_differentiableOn_eval_appLE_of_forall_differentiableOn
end P2MW
export P2MW.S_AlgebraicGeometry_IsAffineOpen_isOpen_and_exists_differentiableOn_eval_appLE_of_forall_differentiableOn (solution)
