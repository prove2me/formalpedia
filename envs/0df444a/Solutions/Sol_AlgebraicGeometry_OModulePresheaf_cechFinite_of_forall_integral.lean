-- Prove2me | solution 1 for AlgebraicGeometry.OModulePresheaf.cechFinite_of_forall_integral
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/13cd8c42-76ca-5e5c-8463-2d1421b7b3ba

import Definitions.Def_AlgebraicGeometry_OModulePresheafIdealFiltration
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_hasDevissageStep
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_cechFinite_pushforward_of_isIntegral_of_ih
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_cechFinite_of_forall_cechFinite_idealPowQuot
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_isCoherent_idealPowQuot
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_isQuasicoherent_idealPowQuot
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_supportedIn_idealPowQuot
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_cechFinite_of_affSES_mid
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.RingTheory.Noetherian.Basic
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_OModulePresheaf_cechFinite_of_forall_integral

set_option autoImplicit false

universe u

p2m_open "CategoryTheory AlgebraicGeometry P2MW.S_AlgebraicGeometry_OModulePresheaf_cechFinite_of_forall_integral.AlgebraicGeometry TopologicalSpace Opposite"

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "IsLocallyNoetherian IsProper LocallyOfFiniteType.isLocallyNoetherian QuasiCompact LocallyOfFiniteType Spec IsIntegral Scheme Scheme.IdealSheafData.vanishingIdeal QuasiCompact.compactSpace_of_compactSpace IsSeparated IsNoetherian Scheme.IdealSheafData OModulePresheaf.IdealAnnihilates OModulePresheaf.idealAnnihilates_idealPowQuot OModulePresheaf.pushforward OModulePresheaf.pushforwardUnit Scheme.OrderedAffineCover.isAffineOpen_inter Scheme.OrderedAffineCover OModulePresheaf OModulePresheaf.cechFinite_iff OModulePresheaf.hasDevissageStep OModulePresheaf.cechFinite_pushforward_of_isIntegral_of_ih OModulePresheaf.cechFinite_of_forall_cechFinite_idealPowQuot OModulePresheaf.isCoherent_idealPowQuot OModulePresheaf.isQuasicoherent_idealPowQuot OModulePresheaf.supportedIn_idealPowQuot OModulePresheaf.cechFinite_of_affSES_mid"
namespace OModulePresheaf
p2m_export "AlgebraicGeometry.OModulePresheaf" "IdealAnnihilates idealAnnihilates_idealPowQuot pushforward pushforwardUnit cochain CechFinite cechFinite_iff IsCoherent IsQuasicoherent SupportedIn hasDevissageStep cechFinite_pushforward_of_isIntegral_of_ih cechFinite_of_forall_cechFinite_idealPowQuot isCoherent_idealPowQuot isQuasicoherent_idealPowQuot supportedIn_idealPowQuot cechFinite_of_affSES_mid"
namespace Driver
p2m_open "AlgebraicGeometry.OModulePresheaf AlgebraicGeometry"

variable {R : Type u} [CommRing R] {V : Scheme.{u}}

theorem isNoetherian_of_isProper [IsNoetherianRing R] (π : V ⟶ Spec (.of R)) [IsProper π] : IsNoetherian V := by
  haveI : LocallyOfFiniteType π := inferInstance
  haveI : IsLocallyNoetherian (Spec (CommRingCat.of R)) := inferInstance
  haveI : IsLocallyNoetherian V := LocallyOfFiniteType.isLocallyNoetherian π
  haveI : CompactSpace V := QuasiCompact.compactSpace_of_compactSpace π
  exact {}

theorem cechFinite_of_supportedIn_empty (π : V ⟶ Spec (.of R)) [IsSeparated π] (K : V.OrderedAffineCover)
    (F : OModulePresheaf π) {Y : Closeds V} (hY : (Y : Set V) = ∅) (hFs : F.SupportedIn Y) : F.CechFinite K := by
  have hCF : ∀ q, Subsingleton (F.cochain K q) := fun q =>
    ⟨fun a b => funext fun s => @Subsingleton.elim _
      (hFs ⟨_, Scheme.OrderedAffineCover.isAffineOpen_inter π K s⟩ (by rw [hY]; exact Set.inter_empty _)) _ _⟩
  rw [OModulePresheaf.cechFinite_iff]
  refine ⟨?_, fun i => ?_⟩
  · haveI := hCF 0; infer_instance
  · haveI := hCF (i + 1); infer_instance

end AlgebraicGeometry.OModulePresheaf.Driver

open AlgebraicGeometry.OModulePresheaf.Driver in

theorem solution
    {R : Type u} [CommRing R] [IsNoetherianRing R] {V : Scheme.{u}} (π : V ⟶ Spec (.of R)) [IsProper π]
    (K : V.OrderedAffineCover)
    (hInt : ∀ Z₀ : TopologicalSpace.Closeds V, (Z₀ : Set V).Nonempty →
      IsIntegral (Scheme.IdealSheafData.vanishingIdeal Z₀).subscheme →
      (∀ Y' < Z₀, ∀ G : OModulePresheaf π, G.IsCoherent → G.IsQuasicoherent → G.SupportedIn Y' →
        G.CechFinite K) →
      (OModulePresheaf.pushforwardUnit π (Scheme.IdealSheafData.vanishingIdeal Z₀).subschemeι).CechFinite K) :
    ∀ (Y : TopologicalSpace.Closeds V) (F : OModulePresheaf π),
      F.IsCoherent → F.IsQuasicoherent → F.SupportedIn Y → F.CechFinite K := by
  haveI : IsSeparated π := inferInstance
  haveI : IsNoetherian V := isNoetherian_of_isProper π
  haveI : IsLocallyNoetherian V := inferInstance
  intro Y
  induction Y using WellFoundedLT.induction with
  | _ Y ihY =>
  intro F hFc hFq hFs
  by_cases hYne : (Y : Set V).Nonempty
  ·
    have hStep : ∀ F' : OModulePresheaf π, F'.IsCoherent → F'.IsQuasicoherent → F'.SupportedIn Y →
        OModulePresheaf.IdealAnnihilates π (Scheme.IdealSheafData.vanishingIdeal Y) F' → F'.CechFinite K := by
      intro F' hFc' hFq' hFs' hAnn'
      obtain ⟨S⟩ := AlgebraicGeometry.OModulePresheaf.hasDevissageStep π F' hFc' hFq' Y hYne hFs' hAnn'
      have hG₃ : S.G₃.CechFinite K := ihY S.Z₁ S.Z₁_lt S.G₃ S.isCoherent_G₃ S.isQuasicoherent_G₃ S.supportedIn_G₃
      have hCP : (OModulePresheaf.pushforward π (Scheme.IdealSheafData.vanishingIdeal S.Z₀).subschemeι S.H).CechFinite K := by
        rcases lt_or_eq_of_le S.Z₀_le with hlt | heq
        · exact ihY S.Z₀ hlt _ S.isCoherent_pushforward S.isQuasicoherent_pushforward S.supportedIn_pushforward
        · have ih0 : ∀ Y' < S.Z₀, ∀ G : OModulePresheaf π, G.IsCoherent → G.IsQuasicoherent → G.SupportedIn Y' →
              G.CechFinite K := fun Y' hY' => ihY Y' (heq ▸ hY')
          exact AlgebraicGeometry.OModulePresheaf.cechFinite_pushforward_of_isIntegral_of_ih π K S.Z₀_nonempty
            S.isIntegral (hInt S.Z₀ S.Z₀_nonempty S.isIntegral ih0) ih0 S.H S.isCoherent_pushforward
            S.isQuasicoherent_pushforward
      exact AlgebraicGeometry.OModulePresheaf.cechFinite_of_affSES_mid S.ses K hCP hG₃
    exact AlgebraicGeometry.OModulePresheaf.cechFinite_of_forall_cechFinite_idealPowQuot π K Y F hFc hFq hFs fun k =>
      hStep _ (AlgebraicGeometry.OModulePresheaf.isCoherent_idealPowQuot π _ F k hFc)
        (AlgebraicGeometry.OModulePresheaf.isQuasicoherent_idealPowQuot π _ F k hFq)
        (AlgebraicGeometry.OModulePresheaf.supportedIn_idealPowQuot π _ F k hFs)
        (AlgebraicGeometry.OModulePresheaf.idealAnnihilates_idealPowQuot π _ F k)
  · exact cechFinite_of_supportedIn_empty π K F (Set.not_nonempty_iff_eq_empty.mp hYne) hFs

end S_AlgebraicGeometry_OModulePresheaf_cechFinite_of_forall_integral
end P2MW
export P2MW.S_AlgebraicGeometry_OModulePresheaf_cechFinite_of_forall_integral (solution)
