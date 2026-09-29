-- Prove2me | solution 1 for AlgebraicGeometry.isAffine_of_isClosedImmersion_of_isNilpotent_ker
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/5edb2f1a-7a14-5b80-9976-70463c1e728a

import Mathlib
import Theorems.Thm_AlgebraicGeometry_isAffine_of_isClosedImmersion_of_ker_mul_ker_eq_bot
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_isAffine_of_isClosedImmersion_of_isNilpotent_ker

set_option autoImplicit false

universe u

p2m_open "CategoryTheory AlgebraicGeometry P2MW.S_AlgebraicGeometry_isAffine_of_isClosedImmersion_of_isNilpotent_ker.AlgebraicGeometry TopologicalSpace Opposite"

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Scheme.IdealSheafData.ideal_bot IsClosedImmersion.isIso_iff_ker_eq_bot Surjective Scheme.IdealSheafData.one_eq_top Scheme.IdealSheafData.support_bot Scheme.Hom IsAffine.of_isIso iSup_affineOpens_eq_top IsAffine isAffine_of_isEmpty Scheme.IdealSheafData.ideal_pow Scheme Scheme.IdealSheafData.support_top Scheme.IdealSheafData.ext_of_iSup_eq_top IsClosedImmersion Scheme.Hom.comp_app IsClosedImmersion.of_comp_isClosedImmersion IsClosedImmersion.lift IsClosedImmersion.lift_fac Scheme.Hom.preimage_iSup Scheme.Hom.ker_apply Scheme.IdealSheafData.support Scheme.IdealSheafData.le_def Scheme.IdealSheafData isAffine_of_isClosedImmersion_of_ker_mul_ker_eq_bot"
p2m_open "AlgebraicGeometry"

namespace ThickAffNilp

p2m_open "AlgebraicGeometry.Scheme.IdealSheafData"

theorem isEmpty_of_top_eq_bot (X : Scheme.{u}) (h : (⊤ : X.IdealSheafData) = ⊥) : IsEmpty X := by
  have := congr(Scheme.IdealSheafData.support $h)
  rw [Scheme.IdealSheafData.support_top, Scheme.IdealSheafData.support_bot] at this
  have h' : (Set.univ : Set X) = ∅ := by
    have := congr((($this) : Set X))
    simpa using this.symm
  exact Set.univ_eq_empty_iff.mp h'

theorem pow_antitone {X : Scheme.{u}} (I : X.IdealSheafData) {m n : ℕ} (h : m ≤ n) : I ^ n ≤ I ^ m := by
  rw [Scheme.IdealSheafData.le_def]
  intro U
  rw [Scheme.IdealSheafData.ideal_pow, Scheme.IdealSheafData.ideal_pow]
  exact Ideal.pow_le_pow_right h

theorem ker_lift_ideal_pow_eq_bot {X₀ X : Scheme.{u}} (i : X₀ ⟶ X) [IsClosedImmersion i]
    (J : X.IdealSheafData) (n : ℕ) (hJ : i.ker ^ n ≤ J) (hJ' : J ≤ i.ker) (U : X.affineOpens) :
    letI i' := IsClosedImmersion.lift J.subschemeι i (by rwa [ker_subschemeι])
    (i'.ker.ideal ⟨J.subschemeι ⁻¹ᵁ U, U.2.preimage _⟩) ^ n = ⊥ := by
  set i' := IsClosedImmersion.lift J.subschemeι i (by rwa [ker_subschemeι]) with hi'
  have hfac : i' ≫ J.subschemeι = i := IsClosedImmersion.lift_fac _ _ _
  haveI : IsClosedImmersion i' := by
    have : IsClosedImmersion (i' ≫ J.subschemeι) := by rw [hfac]; infer_instance
    exact IsClosedImmersion.of_comp_isClosedImmersion i' J.subschemeι
  set φ := (J.subschemeι.app U).hom with hφ
  have hφsurj : Function.Surjective φ := J.subschemeι.app_surjective U U.2
  have hkerφ : RingHom.ker φ = J.ideal U := by
    rw [hφ, ← Scheme.Hom.ker_apply, ker_subschemeι]

  have hcomp : RingHom.ker (i.app U).hom =
      (RingHom.ker (i'.app (J.subschemeι ⁻¹ᵁ U)).hom).comap φ := by
    have : RingHom.ker (i.app U).hom = RingHom.ker ((i' ≫ J.subschemeι).app U).hom := by
      rw [hfac]
    rw [this]
    ext x
    simp only [RingHom.mem_ker, Ideal.mem_comap, Scheme.Hom.comp_app, hφ]
    rfl
  rw [Scheme.Hom.ker_apply]
  change RingHom.ker (i'.app (J.subschemeι ⁻¹ᵁ U)).hom ^ n = ⊥
  have hK : RingHom.ker (i'.app (J.subschemeι ⁻¹ᵁ U)).hom = (RingHom.ker (i.app U).hom).map φ := by
    rw [hcomp, Ideal.map_comap_of_surjective φ hφsurj]
  rw [hK, ← Ideal.map_pow, ← Scheme.Hom.ker_apply]
  change Ideal.map φ ((i.ker ^ n).ideal U) = ⊥
  rw [Ideal.map_eq_bot_iff_le_ker, hkerφ]
  exact hJ U

def P (n : ℕ) : Prop := ∀ ⦃X₀ X : Scheme.{u}⦄ (i : X₀ ⟶ X), IsClosedImmersion i → IsAffine X₀ →
  i.ker ^ n = ⊥ → IsAffine X

theorem p_all : ∀ n : ℕ, P.{u} n := by
  intro n
  induction n with
  | zero =>
    intro X₀ X i _ _ h
    rw [pow_zero, Scheme.IdealSheafData.one_eq_top] at h
    haveI := isEmpty_of_top_eq_bot X h
    exact isAffine_of_isEmpty
  | succ n ih =>
    intro X₀ X i _ _ h
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn
      rw [zero_add, pow_one] at h
      haveI : IsIso i := IsClosedImmersion.isIso_iff_ker_eq_bot.mpr h
      exact IsAffine.of_isIso (inv i)
    ·
      set J := i.ker ^ n with hJdef
      have hJle : J ≤ i.ker := by
        rw [hJdef]
        conv_rhs => rw [← pow_one i.ker]
        exact pow_antitone _ hn
      have hJsq : J * J = ⊥ := by
        rw [hJdef, ← pow_add, ← le_bot_iff, ← h]
        exact pow_antitone _ (by omega)

      let i' := IsClosedImmersion.lift J.subschemeι i (by rwa [ker_subschemeι])
      have hfac : i' ≫ J.subschemeι = i := IsClosedImmersion.lift_fac _ _ _
      haveI : IsClosedImmersion i' := by
        have : IsClosedImmersion (i' ≫ J.subschemeι) := by rw [hfac]; infer_instance
        exact IsClosedImmersion.of_comp_isClosedImmersion i' J.subschemeι

      have hker' : i'.ker ^ n = ⊥ := by
        refine Scheme.IdealSheafData.ext_of_iSup_eq_top
          (fun U : X.affineOpens => ⟨J.subschemeι ⁻¹ᵁ U, U.2.preimage _⟩) ?_ fun U => ?_
        · change ⨆ U : X.affineOpens, J.subschemeι ⁻¹ᵁ (U : X.Opens) = ⊤
          rw [← Scheme.Hom.preimage_iSup, iSup_affineOpens_eq_top]
          rfl
        · rw [Scheme.IdealSheafData.ideal_pow, Scheme.IdealSheafData.ideal_bot]
          exact ker_lift_ideal_pow_eq_bot i J n le_rfl hJle U
      haveI : IsAffine J.subscheme := ih i' inferInstance inferInstance hker'
      have hsq : J.subschemeι.ker * J.subschemeι.ker = ⊥ := by rwa [ker_subschemeι]
      exact AlgebraicGeometry.isAffine_of_isClosedImmersion_of_ker_mul_ker_eq_bot J.subschemeι hsq

theorem isAffine_of_isNilpotent_ker {X₀ X : Scheme.{u}} (i : X₀ ⟶ X)
    [IsClosedImmersion i] [IsAffine X₀] (h : IsNilpotent i.ker) : IsAffine X := by
  obtain ⟨n, hn⟩ := h
  exact p_all n i inferInstance inferInstance (by simpa using hn)

end ThickAffNilp

end AlgebraicGeometry

theorem solution
    {X₀ X : Scheme.{u}} (i : X₀ ⟶ X) [IsClosedImmersion i] [IsAffine X₀]
    (h : IsNilpotent i.ker) : IsAffine X :=
  AlgebraicGeometry.ThickAffNilp.isAffine_of_isNilpotent_ker i h

end S_AlgebraicGeometry_isAffine_of_isClosedImmersion_of_isNilpotent_ker
end P2MW
export P2MW.S_AlgebraicGeometry_isAffine_of_isClosedImmersion_of_isNilpotent_ker (solution)
