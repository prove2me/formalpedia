-- Prove2me | solution 1 for AlgebraicGeometry.OModulePresheaf.cechFinite_of_forall_cechFinite_idealPowQuot
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/8b57da83-5a77-523d-bfdc-0ae63ce2252e

import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.RingTheory.Localization.Away.Basic
import Definitions.Def_AlgebraicGeometry_OModulePresheafIdealFiltration
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_idealPowSub_eq_bot
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_cechFinite_of_affSES_mid
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_cechFinite_of_affSES_right
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_OModulePresheaf_cechFinite_of_forall_cechFinite_idealPowQuot

set_option maxHeartbeats 6400000
set_option synthInstance.maxHeartbeats 1600000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option autoImplicit false

p2m_open "AlgebraicGeometry P2MW.S_AlgebraicGeometry_OModulePresheaf_cechFinite_of_forall_cechFinite_idealPowQuot.AlgebraicGeometry CategoryTheory TopologicalSpace Opposite"

noncomputable section

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "IsLocallyNoetherian Spec Scheme Scheme.IdealSheafData.vanishingIdeal IsSeparated Scheme.IdealSheafData OModulePresheaf.idealPowQuot OModulePresheaf.zero OModulePresheaf OModulePresheaf.cochain OModulePresheaf.CechFinite OModulePresheaf.IsCoherent OModulePresheaf.IsQuasicoherent OModulePresheaf.SupportedIn OModulePresheaf.exists_idealPowSub_eq_bot OModulePresheaf.cechFinite_of_affSES_mid OModulePresheaf.cechFinite_of_affSES_right"
namespace OModulePresheaf
p2m_export "AlgebraicGeometry.OModulePresheaf" "idealPowSub idealPow idealPowSub_antitone idealPowQuot idealPowSES idealPowZeroSES zero AffSES cochain CechFinite IsCoherent IsQuasicoherent SupportedIn exists_idealPowSub_eq_bot cechFinite_of_affSES_mid cechFinite_of_affSES_right"
namespace G4T
p2m_open "AlgebraicGeometry.OModulePresheaf AlgebraicGeometry"

universe u

section Wrappers
variable {R : Type u} [CommRing R] [IsNoetherianRing R] {V : Scheme.{u}} {π : V ⟶ Spec (.of R)} [IsSeparated π]
  {F₁ F₂ F₃ : OModulePresheaf π}
theorem cechFinite_of_affSES_mid' (K : V.OrderedAffineCover) (S : AffSES F₁ F₂ F₃) (h₁ : F₁.CechFinite K)
    (h₃ : F₃.CechFinite K) : F₂.CechFinite K := OModulePresheaf.cechFinite_of_affSES_mid S K h₁ h₃
theorem cechFinite_of_affSES_right' (K : V.OrderedAffineCover) (S : AffSES F₁ F₂ F₃) (h₁ : F₁.CechFinite K)
    (h₂ : F₂.CechFinite K) : F₃.CechFinite K := OModulePresheaf.cechFinite_of_affSES_right S K h₁ h₂
end Wrappers

section ZeroBase

variable {R : Type u} [CommRing R] {V : Scheme.{u}} (π : V ⟶ Spec (.of R))

theorem cechFinite_zero (K : V.OrderedAffineCover) :
    OModulePresheaf.CechFinite (K := K) (OModulePresheaf.zero π) := by
  have hCF : ∀ q, Subsingleton
      (OModulePresheaf.cochain (OModulePresheaf.zero π) K q) :=
    fun q => ⟨fun a b => funext fun s => Subsingleton.elim _ _⟩
  exact ⟨(haveI := hCF 0; ⟨⟨∅, Subsingleton.elim _ _⟩⟩),
    fun i => (haveI := hCF (i + 1); ⟨⟨∅, Subsingleton.elim _ _⟩⟩)⟩

theorem cechFinite_idealPow_of_forall_subsingleton [IsSeparated π]
    (K : V.OrderedAffineCover) (I : V.IdealSheafData) (F : OModulePresheaf π) (N : ℕ)
    (hN : ∀ (q : ℕ) (s : K.Idx q),
      idealPowSub π I F N (K.inter s) = ⊥) :
    OModulePresheaf.CechFinite (K := K) (idealPow π I F N) := by
  have hCF : ∀ q, Subsingleton
      (OModulePresheaf.cochain (idealPow π I F N) K q) := fun q => by
    refine ⟨fun a b => funext fun s => Subtype.ext ?_⟩
    have hav := (Submodule.mem_bot R).mp (hN q s ▸ (a s).2 :
      (idealPowSub π I F N (K.inter s)).subtype (a s) ∈ ⊥)
    have hbv := (Submodule.mem_bot R).mp (hN q s ▸ (b s).2 :
      (idealPowSub π I F N (K.inter s)).subtype (b s) ∈ ⊥)
    exact hav.trans hbv.symm
  exact ⟨(haveI := hCF 0; ⟨⟨∅, Subsingleton.elim _ _⟩⟩),
    fun i => (haveI := hCF (i + 1); ⟨⟨∅, Subsingleton.elim _ _⟩⟩)⟩

theorem exists_cechFinite_idealPow [IsSeparated π] [IsLocallyNoetherian V]
    (K : V.OrderedAffineCover) (Y : Closeds V) (F : OModulePresheaf π)
    (hFc : OModulePresheaf.IsCoherent F) (hFq : OModulePresheaf.IsQuasicoherent F)
    (hFs : OModulePresheaf.SupportedIn F Y) :
    ∃ N, OModulePresheaf.CechFinite (K := K)
      (idealPow π (Scheme.IdealSheafData.vanishingIdeal Y) F N) := by

  let T : Type u := Σ q : Fin (Fintype.card K.ι), K.Idx q
  haveI : Fintype T := inferInstance
  choose Nqs hNqs using fun t : T => OModulePresheaf.exists_idealPowSub_eq_bot π Y F hFc hFq hFs
    ⟨K.inter t.2, K.isAffineOpen_inter π t.2⟩
  refine ⟨Finset.univ.sup Nqs,
    cechFinite_idealPow_of_forall_subsingleton π K _ F _ fun q s => ?_⟩

  rcases lt_or_ge q (Fintype.card K.ι) with hq | hq
  · exact le_bot_iff.mp
      ((hNqs ⟨⟨q, hq⟩, s⟩).symm ▸ idealPowSub_antitone π _ F
        (Finset.le_sup (Finset.mem_univ (⟨⟨q, hq⟩, s⟩ : T))) _)
  · have hcard := Fintype.card_le_of_injective s.1 s.2.injective
    rw [Fintype.card_fin] at hcard; omega

theorem cechFinite_of_forall_cechFinite_idealPowQuot [IsNoetherianRing R] [IsSeparated π]
    [IsLocallyNoetherian V] (K : V.OrderedAffineCover) (Y : Closeds V) (F : OModulePresheaf π)
    (hFc : OModulePresheaf.IsCoherent F) (hFq : OModulePresheaf.IsQuasicoherent F)
    (hFs : OModulePresheaf.SupportedIn F Y)
    (hStep : ∀ k, OModulePresheaf.CechFinite (K := K)
      (idealPowQuot π (Scheme.IdealSheafData.vanishingIdeal Y) F k)) :
    OModulePresheaf.CechFinite (K := K) F := by
  set I := Scheme.IdealSheafData.vanishingIdeal Y
  obtain ⟨N, hN⟩ := exists_cechFinite_idealPow π K Y F hFc hFq hFs

  have hSmul : ∀ j, OModulePresheaf.CechFinite (K := K)
      (idealPow π I F (N - j)) := fun j => by
    induction j with
    | zero => simpa using hN
    | succ j ih =>
      rcases Nat.lt_or_ge j N with hj | hj
      · have heq : N - j = (N - (j + 1)) + 1 := by omega
        exact cechFinite_of_affSES_mid' K
          (idealPowSES π I F (N - (j + 1))) (heq ▸ ih) (hStep _)
      · rw [Nat.sub_eq_zero_of_le (Nat.le_succ_of_le hj)]
        rw [Nat.sub_eq_zero_of_le hj] at ih; exact ih
  exact cechFinite_of_affSES_right' K
    (idealPowZeroSES π I F)
    (cechFinite_zero π K) (by simpa using hSmul N)

end ZeroBase

end AlgebraicGeometry.OModulePresheaf.G4T

end

universe u

open _root_.AlgebraicGeometry _root_.P2MW.S_AlgebraicGeometry_OModulePresheaf_cechFinite_of_forall_cechFinite_idealPowQuot.AlgebraicGeometry in
theorem solution {R : Type u} [CommRing R] [IsNoetherianRing R] {V : Scheme.{u}} (π : V ⟶ Spec (.of R)) [IsSeparated π] [IsLocallyNoetherian V] (K : V.OrderedAffineCover) (Y : TopologicalSpace.Closeds V) (F : OModulePresheaf π) (hFc : F.IsCoherent) (hFq : F.IsQuasicoherent) (hFs : F.SupportedIn Y) (hStep : ∀ k, (OModulePresheaf.idealPowQuot π (Scheme.IdealSheafData.vanishingIdeal Y) F k).CechFinite K) : F.CechFinite K :=
  AlgebraicGeometry.OModulePresheaf.G4T.cechFinite_of_forall_cechFinite_idealPowQuot π K Y F hFc hFq hFs hStep

end S_AlgebraicGeometry_OModulePresheaf_cechFinite_of_forall_cechFinite_idealPowQuot
end P2MW
export P2MW.S_AlgebraicGeometry_OModulePresheaf_cechFinite_of_forall_cechFinite_idealPowQuot (solution)
