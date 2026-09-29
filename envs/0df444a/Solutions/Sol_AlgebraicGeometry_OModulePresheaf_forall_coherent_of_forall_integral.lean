-- Prove2me | solution 1 for AlgebraicGeometry.OModulePresheaf.forall_coherent_of_forall_integral
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/59c3f108-91bc-57f7-ad13-28a06e39187d

import Mathlib
import Definitions.Def_AlgebraicGeometry_OModulePresheafConstructions
import Definitions.Def_AlgebraicGeometry_OModulePresheafIdealFiltration
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_hasDevissageStep
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_forall_of_forall_idealAnnihilates
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_forall_pushforward_of_isIntegral
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_OModulePresheaf_forall_coherent_of_forall_integral

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace P2mDevissageDriver

open AlgebraicGeometry.OModulePresheaf

variable {R : Type u} [CommRing R] [IsNoetherianRing R] {V : Scheme.{u}} (π : V ⟶ Spec (.of R)) [IsProper π]

include π in

theorem isNoetherian : IsNoetherian V := by
  haveI : IsLocallyNoetherian V := LocallyOfFiniteType.isLocallyNoetherian π
  haveI : CompactSpace V := (HasAffineProperty.iff_of_isAffine (P := @QuasiCompact) (f := π)).mp inferInstance
  exact {}

variable (Q : Closeds V → OModulePresheaf π → Prop)
  (h0 : ∀ (Y : Closeds V) (G : OModulePresheaf π), (∀ U : V.affineOpens, Subsingleton (G.obj U.1)) → Q Y G)
  (hmono : ∀ (Y Y' : Closeds V) (G : OModulePresheaf π), Y' ≤ Y → Q Y' G → Q Y G)
  (hext : ∀ (Y : Closeds V) (G₁ G₂ G₃ : OModulePresheaf π), Nonempty (AffSES G₁ G₂ G₃) →
    G₁.IsCoherent → G₁.IsQuasicoherent → G₂.IsCoherent → G₂.IsQuasicoherent →
    G₃.IsCoherent → G₃.IsQuasicoherent →
    (Q Y G₁ → Q Y G₃ → Q Y G₂) ∧ (Q Y G₁ → Q Y G₂ → Q Y G₃) ∧ (Q Y G₂ → Q Y G₃ → Q Y G₁))
  (hInt : ∀ Z₀ : Closeds V, (Z₀ : Set V).Nonempty →
    IsIntegral (Scheme.IdealSheafData.vanishingIdeal Z₀).subscheme →
    (∀ Y' < Z₀, ∀ G : OModulePresheaf π, G.IsCoherent → G.IsQuasicoherent → G.SupportedIn Y' → Q Y' G) →
    Q Z₀ (pushforwardUnit π (Scheme.IdealSheafData.vanishingIdeal Z₀).subschemeι))

include h0 hmono hext hInt in

theorem step (Y : Closeds V)
    (IH : ∀ Y' < Y, ∀ G : OModulePresheaf π, G.IsCoherent → G.IsQuasicoherent → G.SupportedIn Y' → Q Y' G) :
    ∀ F : OModulePresheaf π, F.IsCoherent → F.IsQuasicoherent → F.SupportedIn Y → Q Y F := by
  haveI : IsNoetherian V := isNoetherian π

  refine forall_of_forall_idealAnnihilates π Y (Q Y) (h0 Y) (hext Y) ?_
  intro G hGc hGq hGs hann
  by_cases hY : (Y : Set V).Nonempty
  ·
    obtain ⟨D⟩ := hasDevissageStep π G hGc hGq Y hY hGs hann

    have hG₃ : Q Y D.G₃ :=
      hmono Y D.Z₁ D.G₃ D.Z₁_lt.le (IH D.Z₁ D.Z₁_lt D.G₃ D.isCoherent_G₃ D.isQuasicoherent_G₃ D.supportedIn_G₃)

    have IH₀ : ∀ Y' < D.Z₀, ∀ G' : OModulePresheaf π,
        G'.IsCoherent → G'.IsQuasicoherent → G'.SupportedIn Y' → Q Y' G' :=
      fun Y' hY' G' h₁ h₂ h₃ => IH Y' (lt_of_lt_of_le hY' D.Z₀_le) G' h₁ h₂ h₃

    have hO : Q D.Z₀ (pushforwardUnit π (Scheme.IdealSheafData.vanishingIdeal D.Z₀).subschemeι) :=
      hInt D.Z₀ D.Z₀_nonempty D.isIntegral IH₀

    have hH : Q D.Z₀ (pushforward π (Scheme.IdealSheafData.vanishingIdeal D.Z₀).subschemeι D.H) :=
      forall_pushforward_of_isIntegral π D.Z₀ D.Z₀_nonempty D.isIntegral (Q D.Z₀) (h0 D.Z₀) (hext D.Z₀) hO
        (fun Y' hY' G' h₁ h₂ h₃ => hmono D.Z₀ Y' G' hY'.le (IH₀ Y' hY' G' h₁ h₂ h₃))
        D.H D.isCoherent_pushforward D.isQuasicoherent_pushforward D.supportedIn_pushforward

    exact (hext Y _ G D.G₃ ⟨D.ses⟩ D.isCoherent_pushforward D.isQuasicoherent_pushforward hGc hGq
      D.isCoherent_G₃ D.isQuasicoherent_G₃).1 (hmono Y D.Z₀ _ D.Z₀_le hH) hG₃
  ·
    refine h0 Y G fun U => hGs U ?_
    rw [Set.not_nonempty_iff_eq_empty.mp hY, Set.inter_empty]

include h0 hmono hext hInt in
theorem main : ∀ (Y : Closeds V) (F : OModulePresheaf π), F.IsCoherent → F.IsQuasicoherent → F.SupportedIn Y → Q Y F := by
  haveI : IsNoetherian V := isNoetherian π
  intro Y
  induction Y using WellFoundedLT.induction with
  | ind Y IH => exact step π Q h0 hmono hext hInt Y IH

end P2mDevissageDriver

theorem solution
    {R : Type u} [CommRing R] [IsNoetherianRing R] {V : Scheme.{u}} (π : V ⟶ Spec (.of R)) [IsProper π]
    (Q : Closeds V → OModulePresheaf π → Prop)
    (h0 : ∀ (Y : Closeds V) (G : OModulePresheaf π), (∀ U : V.affineOpens, Subsingleton (G.obj U.1)) → Q Y G)
    (hmono : ∀ (Y Y' : Closeds V) (G : OModulePresheaf π), Y' ≤ Y → Q Y' G → Q Y G)
    (hext : ∀ (Y : Closeds V) (G₁ G₂ G₃ : OModulePresheaf π), Nonempty (OModulePresheaf.AffSES G₁ G₂ G₃) →
      G₁.IsCoherent → G₁.IsQuasicoherent → G₂.IsCoherent → G₂.IsQuasicoherent →
      G₃.IsCoherent → G₃.IsQuasicoherent →
      (Q Y G₁ → Q Y G₃ → Q Y G₂) ∧ (Q Y G₁ → Q Y G₂ → Q Y G₃) ∧ (Q Y G₂ → Q Y G₃ → Q Y G₁))
    (hInt : ∀ Z₀ : Closeds V, (Z₀ : Set V).Nonempty →
      IsIntegral (Scheme.IdealSheafData.vanishingIdeal Z₀).subscheme →
      (∀ Y' < Z₀, ∀ G : OModulePresheaf π, G.IsCoherent → G.IsQuasicoherent → G.SupportedIn Y' → Q Y' G) →
      Q Z₀ (OModulePresheaf.pushforwardUnit π (Scheme.IdealSheafData.vanishingIdeal Z₀).subschemeι)) :
    ∀ (Y : Closeds V) (F : OModulePresheaf π), F.IsCoherent → F.IsQuasicoherent → F.SupportedIn Y → Q Y F :=
  P2mDevissageDriver.main π Q h0 hmono hext hInt

end S_AlgebraicGeometry_OModulePresheaf_forall_coherent_of_forall_integral
end P2MW
export P2MW.S_AlgebraicGeometry_OModulePresheaf_forall_coherent_of_forall_integral (solution)
