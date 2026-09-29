-- Prove2me | solution 1 for AlgebraicGeometry.ProjSpace.exists_isFG_hom_injective_saturated_twistGradedModule
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/ff659ec0-bbbf-53a1-a8e3-8dad9ca1ea82

import Mathlib
import Definitions.Def_AlgebraicGeometry_ProjSpaceCover
import Definitions.Def_AlgebraicGeometry_ProjSpaceCechGradedModule
import Definitions.Def_AlgebraicGeometry_ProjTwistDatum
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_ProjSpace_exists_isFG_hom_injective_saturated_twistGradedModule

set_option autoImplicit false

universe u

p2m_open "CategoryTheory AlgebraicGeometry P2MW.S_AlgebraicGeometry_ProjSpace_exists_isFG_hom_injective_saturated_twistGradedModule.AlgebraicGeometry"

attribute [local instance] MvPolynomial.gradedAlgebra

set_option maxHeartbeats 6400000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false

noncomputable section

noncomputable section

open CategoryTheory Opposite MvPolynomial HomogeneousLocalization TopologicalSpace

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Spec.map_comp Scheme.mem_basicOpen Scheme.basicOpen_res Surjective Scheme.Hom Proj.basicOpenIsoAway IsFinite Scheme.preimage_basicOpen Spec Spec.map Proj.basicOpenToSpec Scheme Scheme.Hom.appTop Proj.mem_basicOpen Scheme.Opens.topIso_hom Scheme.Hom.comp_appTop Proj IsFinite.finite_app Proj.stalkIso' Proj.basicOpenIsoSpec_inv_ι Proj.isAffineOpen_basicOpen Proj.basicOpen Proj.basicOpen_mul Scheme.basicOpen_mul IsAffineOpen Scheme.Opens IsAffineHom Scheme.Opens.ι_appTop Proj.awayToSection Proj.basicOpenToSpec_app_top Proj.basicOpenIsoSpec_hom Scheme.basicOpen_le ProjectiveSpectrum.Proj.awayToSection_germ Scheme.ΓSpecIso_inv_naturality_assoc Scheme.ΓSpecIso ProjSpace.π ProjSpace.X_mem_one ProjSpace.awayι_comp_π ProjSpace.val_algebraMap ProjSpace.awayMk_monomial Scheme.TwoAffineOpenCover Scheme.TwoAffineOpenCover.algebraOfHom ProjSpace.twistGradedModule"
namespace ProjSpace
p2m_export "AlgebraicGeometry.ProjSpace" "π X_mem_one awayι_comp_π ratio val_algebraMap awayMk_monomial map pullbackChart frameUnit restrictFun TwistCompat restrictFun_restrictFun restrictFun_irrel restrictFun_refl restrictFun_algebraMap' twistObj twistObj.smul_val twistObj.algebraMap_smul twist pullbackOverlap pullbackOverlap_eq_inf frameUnit_cocycle frameUnit_self twistObj.add_val twistObj.zero_val twistFam twistGradedModule isAffineOpen_pullbackChart isAffineOpen_pullbackOverlap twistObj.ext"
namespace GMSec
p2m_open "AlgebraicGeometry.ProjSpace AlgebraicGeometry"

attribute [local instance] MvPolynomial.gradedAlgebra

variable {A : Type u} [CommRing A] {N : ℕ} {X : Scheme.{u}}
  (φ : X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) A))

local notation "𝒜" => MvPolynomial.homogeneousSubmodule (Fin (N + 1)) A

theorem proj_basicOpen_awayMk (j : Fin (N + 1)) {d : ℕ}
    {g : MvPolynomial (Fin (N + 1)) A} (hg : g ∈ 𝒜 d) :
    (Proj 𝒜).basicOpen ((Proj.awayToSection 𝒜 (MvPolynomial.X j)).hom
        (HomogeneousLocalization.Away.mk 𝒜 (ProjSpace.X_mem_one A N j) d g (by simpa using hg)))
      = Proj.basicOpen 𝒜 ((MvPolynomial.X j : MvPolynomial (Fin (N + 1)) A) * g) := by
  set z := HomogeneousLocalization.Away.mk 𝒜 (ProjSpace.X_mem_one A N j) d g (by simpa using hg) with hz
  have hkey : ∀ (x : Proj 𝒜) (hxj : x ∈ Proj.basicOpen 𝒜 (MvPolynomial.X j)),
      IsUnit ((Proj 𝒜).presheaf.germ _ x hxj ((Proj.awayToSection 𝒜 (MvPolynomial.X j)).hom z)) ↔ g ∉ x.asHomogeneousIdeal := by
    intro x hxj
    have hxj' : (MvPolynomial.X j : MvPolynomial (Fin (N + 1)) A) ∈ x.asHomogeneousIdeal.toIdeal.primeCompl := hxj
    have hgerm := congrArg (fun ψ => CommRingCat.Hom.hom ψ z)
      (ProjectiveSpectrum.Proj.awayToSection_germ 𝒜 (MvPolynomial.X j) x hxj)
    simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at hgerm
    erw [hgerm]
    haveI : IsLocalHom (Proj.stalkIso' 𝒜 x).toCommRingCatIso.inv.hom := isLocalHom_of_isIso _
    refine (isUnit_map_iff (Proj.stalkIso' 𝒜 x).toCommRingCatIso.inv.hom _).trans ?_
    rw [← HomogeneousLocalization.isUnit_iff_isUnit_val]
    have hval : (HomogeneousLocalization.mapId 𝒜 (Submonoid.powers_le.mpr hxj') z).val
        = Localization.mk g ⟨(MvPolynomial.X j : MvPolynomial (Fin (N + 1)) A) ^ d, pow_mem hxj' d⟩ := by
      simp only [hz, HomogeneousLocalization.Away.mk, HomogeneousLocalization.mapId,
        HomogeneousLocalization.map_mk, HomogeneousLocalization.val_mk]
      rfl
    rw [show Submonoid.powers_le.mpr hxj = Submonoid.powers_le.mpr hxj' from rfl, hval,
      Localization.mk_eq_mk', IsLocalization.AtPrime.isUnit_mk'_iff]
    exact Iff.rfl
  ext x
  simp only [SetLike.mem_coe, Proj.basicOpen_mul, Proj.mem_basicOpen, Opens.mem_inf]
  refine ⟨fun hx => ?_, fun ⟨hxj, hxg⟩ => ?_⟩
  · have hxj : x ∈ Proj.basicOpen 𝒜 (MvPolynomial.X j) := Scheme.basicOpen_le _ _ hx
    exact ⟨hxj, (hkey x hxj).mp ((Scheme.mem_basicOpen _ _ x hxj).mp hx)⟩
  · exact (Scheme.mem_basicOpen _ _ x hxj).mpr ((hkey x hxj).mpr hxg)

theorem pullbackOverlap_eq_basicOpen (i j : Fin (N + 1)) :
    pullbackOverlap φ i j = X.basicOpen (frameUnit φ i j) := by
  have h1 : (Proj 𝒜).basicOpen ((Proj.awayToSection 𝒜 (MvPolynomial.X i)).hom (ratio A N i j))
      = Proj.basicOpen 𝒜 (MvPolynomial.X i * MvPolynomial.X j) :=
    proj_basicOpen_awayMk (A := A) i (X_mem_one A N j)
  have h2 := Scheme.preimage_basicOpen φ (U := Proj.basicOpen 𝒜 (MvPolynomial.X i))
    ((Proj.awayToSection 𝒜 (MvPolynomial.X i)).hom (ratio A N i j))
  rw [h1] at h2
  exact h2

theorem inf_pullbackChart_eq_basicOpen (i j : Fin (N + 1)) :
    pullbackChart φ i ⊓ pullbackChart φ j = X.basicOpen (frameUnit φ i j) := by
  rw [← pullbackOverlap_eq_inf, pullbackOverlap_eq_basicOpen]

end AlgebraicGeometry.ProjSpace.GMSec

end

noncomputable section

open CategoryTheory Opposite MvPolynomial HomogeneousLocalization TopologicalSpace

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Spec.map_comp Scheme.mem_basicOpen Scheme.basicOpen_res Surjective Scheme.Hom Proj.basicOpenIsoAway IsFinite Scheme.preimage_basicOpen Spec Spec.map Proj.basicOpenToSpec Scheme Scheme.Hom.appTop Proj.mem_basicOpen Scheme.Opens.topIso_hom Scheme.Hom.comp_appTop Proj IsFinite.finite_app Proj.stalkIso' Proj.basicOpenIsoSpec_inv_ι Proj.isAffineOpen_basicOpen Proj.basicOpen Proj.basicOpen_mul Scheme.basicOpen_mul IsAffineOpen Scheme.Opens IsAffineHom Scheme.Opens.ι_appTop Proj.awayToSection Proj.basicOpenToSpec_app_top Proj.basicOpenIsoSpec_hom Scheme.basicOpen_le ProjectiveSpectrum.Proj.awayToSection_germ Scheme.ΓSpecIso_inv_naturality_assoc Scheme.ΓSpecIso ProjSpace.π ProjSpace.X_mem_one ProjSpace.awayι_comp_π ProjSpace.val_algebraMap ProjSpace.awayMk_monomial Scheme.TwoAffineOpenCover Scheme.TwoAffineOpenCover.algebraOfHom ProjSpace.twistGradedModule"
namespace ProjSpace
p2m_export "AlgebraicGeometry.ProjSpace" "π X_mem_one awayι_comp_π ratio val_algebraMap awayMk_monomial map pullbackChart frameUnit restrictFun TwistCompat restrictFun_restrictFun restrictFun_irrel restrictFun_refl restrictFun_algebraMap' twistObj twistObj.smul_val twistObj.algebraMap_smul twist pullbackOverlap pullbackOverlap_eq_inf frameUnit_cocycle frameUnit_self twistObj.add_val twistObj.zero_val twistFam twistGradedModule isAffineOpen_pullbackChart isAffineOpen_pullbackOverlap twistObj.ext"
namespace GMSec
p2m_open "AlgebraicGeometry.ProjSpace AlgebraicGeometry"

attribute [local instance] MvPolynomial.gradedAlgebra

variable {A : Type u} [CommRing A] {N : ℕ} {X : Scheme.{u}}
  (φ : X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) A)) (π : X ⟶ Spec (.of A)) (m : ℕ)

theorem restrictFun_injective_of_eq {V W : X.Opens} (hVW : V = W) :
    Function.Injective (restrictFun (le_of_eq hVW) : Γ(X, W) → Γ(X, V)) := by
  subst hVW
  intro x y h
  rwa [restrictFun_refl, restrictFun_refl] at h

theorem frameUnit_cocycle_of_le {W : X.Opens} (i i' j : Fin (N + 1)) (hi : W ≤ pullbackChart φ i) (hi' : W ≤ pullbackChart φ i') :
    restrictFun hi (frameUnit φ i i') * restrictFun hi' (frameUnit φ i' j) = restrictFun hi (frameUnit φ i j) := by
  have hW : W ≤ pullbackOverlap φ i i' := by rw [pullbackOverlap_eq_inf]; exact le_inf hi hi'
  have key := congrArg (restrictFun hW) (frameUnit_cocycle φ i i' j)
  rw [map_mul, restrictFun_restrictFun, restrictFun_restrictFun, restrictFun_restrictFun] at key
  exact key

theorem frameUnit_mul_swap_of_le {W : X.Opens} (i i' : Fin (N + 1)) (hi : W ≤ pullbackChart φ i) (hi' : W ≤ pullbackChart φ i') :
    restrictFun hi (frameUnit φ i i') * restrictFun hi' (frameUnit φ i' i) = 1 := by
  rw [frameUnit_cocycle_of_le φ i i' i hi hi', frameUnit_self, map_one]

section Chart

variable {U : X.Opens} {i₀ : Fin (N + 1)} (hU : U ≤ pullbackChart φ i₀)
include hU

theorem twistObj_eq_of_val_eq {g g' : twistObj π φ m U} (h : g.val i₀ = g'.val i₀) : g = g' := by
  refine twistObj.ext (_root_.funext fun i => ?_)

  have heq : (U ⊓ pullbackChart φ i) ⊓ pullbackChart φ i₀ = U ⊓ pullbackChart φ i :=
    inf_eq_left.mpr (le_trans inf_le_left hU)
  apply restrictFun_injective_of_eq heq
  have hg := g.compat i i₀
  have hg' := g'.compat i i₀
  rw [restrictFun_irrel (le_of_eq heq) inf_le_left, hg, hg']

  congr 1
  have : restrictFun (le_inf (le_trans inf_le_left inf_le_left) inf_le_right :
      (U ⊓ pullbackChart φ i) ⊓ pullbackChart φ i₀ ≤ U ⊓ pullbackChart φ i₀) (g.val i₀)
      = restrictFun (le_inf (le_trans inf_le_left inf_le_left) inf_le_right) (g'.val i₀) := by rw [h]
  exact this

def frameFamily (h : Γ(X, U ⊓ pullbackChart φ i₀)) : ∀ i : Fin (N + 1), Γ(X, U ⊓ pullbackChart φ i) :=
  fun i => restrictFun inf_le_right (frameUnit φ i i₀) ^ m
    * restrictFun (le_inf inf_le_left (le_trans inf_le_left hU)) h

theorem frameFamily_compat (h : Γ(X, U ⊓ pullbackChart φ i₀)) : TwistCompat φ m U (frameFamily φ m hU h) := by
  intro i j
  simp only [frameFamily, map_mul, map_pow, restrictFun_restrictFun]

  have hc := frameUnit_cocycle_of_le φ i j i₀
    (le_trans inf_le_left inf_le_right : (U ⊓ pullbackChart φ i) ⊓ pullbackChart φ j ≤ pullbackChart φ i)
    (inf_le_right : (U ⊓ pullbackChart φ i) ⊓ pullbackChart φ j ≤ pullbackChart φ j)
  rw [restrictFun_irrel _ (le_trans inf_le_left inf_le_right : (U ⊓ pullbackChart φ i) ⊓ pullbackChart φ j ≤ pullbackChart φ i),
    ← hc, mul_pow, mul_assoc]

def twistObjOfFun (h : Γ(X, U ⊓ pullbackChart φ i₀)) : twistObj π φ m U :=
  ⟨frameFamily φ m hU h, frameFamily_compat φ m hU h⟩

theorem twistObjOfFun_val_self (h : Γ(X, U ⊓ pullbackChart φ i₀)) : (twistObjOfFun φ π m hU h).val i₀ = h := by
  show restrictFun _ (frameUnit φ i₀ i₀) ^ m * restrictFun _ h = h
  rw [frameUnit_self, map_one, one_pow, one_mul, restrictFun_irrel _ (le_refl _), restrictFun_refl]

theorem twistObjOfFun_val (h : Γ(X, U ⊓ pullbackChart φ i₀)) (i : Fin (N + 1)) :
    (twistObjOfFun φ π m hU h).val i
      = restrictFun inf_le_right (frameUnit φ i i₀) ^ m * restrictFun (le_inf inf_le_left (le_trans inf_le_left hU)) h := rfl

theorem twistObjOfFun_val_eq (g : twistObj π φ m U) : twistObjOfFun φ π m hU (g.val i₀) = g :=
  twistObj_eq_of_val_eq φ π m hU (twistObjOfFun_val_self φ π m hU _)

theorem val_self_injective : Function.Injective fun g : twistObj π φ m U => g.val i₀ :=
  fun _ _ h => twistObj_eq_of_val_eq φ π m hU h

theorem val_self_surjective : Function.Surjective fun g : twistObj π φ m U => g.val i₀ :=
  fun h => ⟨twistObjOfFun φ π m hU h, twistObjOfFun_val_self φ π m hU h⟩

theorem twistObjOfFun_add (h h' : Γ(X, U ⊓ pullbackChart φ i₀)) :
    twistObjOfFun φ π m hU (h + h') = twistObjOfFun φ π m hU h + twistObjOfFun φ π m hU h' :=
  twistObj_eq_of_val_eq φ π m hU (by rw [twistObjOfFun_val_self, twistObj.add_val, Pi.add_apply, twistObjOfFun_val_self,
    twistObjOfFun_val_self])

theorem twistObjOfFun_smul (a : Γ(X, U)) (h : Γ(X, U ⊓ pullbackChart φ i₀)) :
    twistObjOfFun φ π m hU (restrictFun inf_le_left a * h) = a • twistObjOfFun φ π m hU h :=
  twistObj_eq_of_val_eq φ π m hU (by rw [twistObjOfFun_val_self, twistObj.smul_val, twistObjOfFun_val_self])

end Chart

end AlgebraicGeometry.ProjSpace.GMSec

end

noncomputable section

open CategoryTheory Opposite MvPolynomial HomogeneousLocalization TopologicalSpace

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Spec.map_comp Scheme.mem_basicOpen Scheme.basicOpen_res Surjective Scheme.Hom Proj.basicOpenIsoAway IsFinite Scheme.preimage_basicOpen Spec Spec.map Proj.basicOpenToSpec Scheme Scheme.Hom.appTop Proj.mem_basicOpen Scheme.Opens.topIso_hom Scheme.Hom.comp_appTop Proj IsFinite.finite_app Proj.stalkIso' Proj.basicOpenIsoSpec_inv_ι Proj.isAffineOpen_basicOpen Proj.basicOpen Proj.basicOpen_mul Scheme.basicOpen_mul IsAffineOpen Scheme.Opens IsAffineHom Scheme.Opens.ι_appTop Proj.awayToSection Proj.basicOpenToSpec_app_top Proj.basicOpenIsoSpec_hom Scheme.basicOpen_le ProjectiveSpectrum.Proj.awayToSection_germ Scheme.ΓSpecIso_inv_naturality_assoc Scheme.ΓSpecIso ProjSpace.π ProjSpace.X_mem_one ProjSpace.awayι_comp_π ProjSpace.val_algebraMap ProjSpace.awayMk_monomial Scheme.TwoAffineOpenCover Scheme.TwoAffineOpenCover.algebraOfHom ProjSpace.twistGradedModule"
namespace ProjSpace
p2m_export "AlgebraicGeometry.ProjSpace" "π X_mem_one awayι_comp_π ratio val_algebraMap awayMk_monomial map pullbackChart frameUnit restrictFun TwistCompat restrictFun_restrictFun restrictFun_irrel restrictFun_refl restrictFun_algebraMap' twistObj twistObj.smul_val twistObj.algebraMap_smul twist pullbackOverlap pullbackOverlap_eq_inf frameUnit_cocycle frameUnit_self twistObj.add_val twistObj.zero_val twistFam twistGradedModule isAffineOpen_pullbackChart isAffineOpen_pullbackOverlap twistObj.ext"
namespace GMSec
p2m_open "AlgebraicGeometry.ProjSpace AlgebraicGeometry"

attribute [local instance] MvPolynomial.gradedAlgebra

variable {A : Type u} [CommRing A] {N : ℕ} {X : Scheme.{u}}
  (φ : X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) A))

def interI (I : Finset (Fin (N + 1))) : X.Opens := ⨅ i ∈ I, pullbackChart φ i

theorem interI_le {I : Finset (Fin (N + 1))} {i : Fin (N + 1)} (hi : i ∈ I) : interI φ I ≤ pullbackChart φ i :=
  (iInf_le _ i).trans (iInf_le _ hi)

theorem interI_anti {I J : Finset (Fin (N + 1))} (h : I ⊆ J) : interI φ J ≤ interI φ I :=
  le_iInf fun _ => le_iInf fun hi => interI_le φ (h hi)

def frameProd (I : Finset (Fin (N + 1))) (i₀ : Fin (N + 1)) : Γ(X, pullbackChart φ i₀) := ∏ j ∈ I, frameUnit φ i₀ j

theorem pullbackChart_inf_interI_eq_basicOpen (K : Finset (Fin (N + 1))) (i₀ : Fin (N + 1)) :
    pullbackChart φ i₀ ⊓ interI φ K = X.basicOpen (frameProd φ K i₀) := by
  classical
  unfold frameProd interI
  induction K using Finset.induction_on with
  | empty =>
    rw [Finset.prod_empty]
    simp only [Finset.notMem_empty, iInf_false, iInf_top, inf_top_eq]
    exact (X.basicOpen_of_isUnit isUnit_one).symm
  | insert k K hkK ih =>
    rw [Finset.prod_insert hkK, Scheme.basicOpen_mul, ← inf_pullbackChart_eq_basicOpen, ← ih, Finset.iInf_insert,
      inf_inf_distrib_left]

theorem interI_eq_basicOpen {I : Finset (Fin (N + 1))} {i₀ : Fin (N + 1)} (hi₀ : i₀ ∈ I) :
    interI φ I = X.basicOpen (frameProd φ I i₀) := by
  rw [← pullbackChart_inf_interI_eq_basicOpen, eq_comm, inf_eq_right]
  exact interI_le φ hi₀

theorem interI_le_basicOpen {I : Finset (Fin (N + 1))} {i₀ : Fin (N + 1)} (hi₀ : i₀ ∈ I) :
    interI φ I ≤ X.basicOpen (frameProd φ I i₀) := le_of_eq (interI_eq_basicOpen φ hi₀)

theorem basicOpen_le_interI {I : Finset (Fin (N + 1))} {i₀ : Fin (N + 1)} (hi₀ : i₀ ∈ I) :
    X.basicOpen (frameProd φ I i₀) ≤ interI φ I := le_of_eq (interI_eq_basicOpen φ hi₀).symm

theorem isAffineOpen_interI [IsAffineHom φ] {I : Finset (Fin (N + 1))} {i₀ : Fin (N + 1)} (hi₀ : i₀ ∈ I) :
    IsAffineOpen (interI φ I) := by
  rw [interI_eq_basicOpen φ hi₀]
  exact (isAffineOpen_pullbackChart φ i₀).basicOpen _

end AlgebraicGeometry.ProjSpace.GMSec

end

noncomputable section

open CategoryTheory Opposite MvPolynomial HomogeneousLocalization TopologicalSpace

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Spec.map_comp Scheme.mem_basicOpen Scheme.basicOpen_res Surjective Scheme.Hom Proj.basicOpenIsoAway IsFinite Scheme.preimage_basicOpen Spec Spec.map Proj.basicOpenToSpec Scheme Scheme.Hom.appTop Proj.mem_basicOpen Scheme.Opens.topIso_hom Scheme.Hom.comp_appTop Proj IsFinite.finite_app Proj.stalkIso' Proj.basicOpenIsoSpec_inv_ι Proj.isAffineOpen_basicOpen Proj.basicOpen Proj.basicOpen_mul Scheme.basicOpen_mul IsAffineOpen Scheme.Opens IsAffineHom Scheme.Opens.ι_appTop Proj.awayToSection Proj.basicOpenToSpec_app_top Proj.basicOpenIsoSpec_hom Scheme.basicOpen_le ProjectiveSpectrum.Proj.awayToSection_germ Scheme.ΓSpecIso_inv_naturality_assoc Scheme.ΓSpecIso ProjSpace.π ProjSpace.X_mem_one ProjSpace.awayι_comp_π ProjSpace.val_algebraMap ProjSpace.awayMk_monomial Scheme.TwoAffineOpenCover Scheme.TwoAffineOpenCover.algebraOfHom ProjSpace.twistGradedModule"
namespace ProjSpace
p2m_export "AlgebraicGeometry.ProjSpace" "π X_mem_one awayι_comp_π ratio val_algebraMap awayMk_monomial map pullbackChart frameUnit restrictFun TwistCompat restrictFun_restrictFun restrictFun_irrel restrictFun_refl restrictFun_algebraMap' twistObj twistObj.smul_val twistObj.algebraMap_smul twist pullbackOverlap pullbackOverlap_eq_inf frameUnit_cocycle frameUnit_self twistObj.add_val twistObj.zero_val twistFam twistGradedModule isAffineOpen_pullbackChart isAffineOpen_pullbackOverlap twistObj.ext"
namespace GMSec
p2m_open "AlgebraicGeometry.ProjSpace AlgebraicGeometry"

attribute [local instance] MvPolynomial.gradedAlgebra

variable {A : Type u} [CommRing A] {N : ℕ} {X : Scheme.{u}}
  (φ : X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) A)) (π : X ⟶ Spec (.of A))

abbrev uTop (i j : Fin (N + 1)) : Γ(X, (⊤ : X.Opens) ⊓ pullbackChart φ i) := restrictFun inf_le_right (frameUnit φ i j)

theorem D_xMul_apply (j : Fin (N + 1)) (f : (twistGradedModule φ π).M) (d : ℤ) (i : Fin (N + 1)) :
    ((twistGradedModule φ π).xMul j f) d i = uTop φ i j * f (d - 1) i := rfl

theorem twistXMul_pow_apply (j : Fin (N + 1)) (k : ℕ) (f : (twistGradedModule φ π).M) (d : ℤ) (i : Fin (N + 1)) :
    (((twistGradedModule φ π).xMul j ^ k) f) d i = uTop φ i j ^ k * f (d - k) i := by
  induction k generalizing d with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', Module.End.mul_apply, D_xMul_apply, ih, pow_succ', mul_assoc]
    congr 2
    · push_cast; ring_nf

theorem twistMonMul_apply (b : Fin (N + 1) → ℕ) (f : (twistGradedModule φ π).M) (d : ℤ) (i : Fin (N + 1)) :
    (ProjSpaceCech.GradedModule.monMul (twistGradedModule φ π) b f) d i
      = (∏ j, uTop φ i j ^ b j) * f (d - ∑ j, (b j : ℤ)) i := by
  classical

  suffices h : ∀ (s : Finset (Fin (N + 1))) (d : ℤ),
      (ProjSpaceCech.GradedModule.monMul (twistGradedModule φ π) (∑ j ∈ s, Pi.single j (b j)) f) d i
        = (∏ j ∈ s, uTop φ i j ^ b j) * f (d - ∑ j ∈ s, (b j : ℤ)) i by
    have hb : (∑ j ∈ Finset.univ, Pi.single j (b j) : Fin (N + 1) → ℕ) = b := by
      funext j; simp [Finset.sum_apply, Pi.single_apply]
    simpa [hb] using h Finset.univ d
  intro s
  induction s using Finset.induction_on with
  | empty =>
    intro d
    simp [ProjSpaceCech.GradedModule.monMul_zero]
  | insert k s hks ih =>
    intro d
    rw [Finset.sum_insert hks, ProjSpaceCech.GradedModule.monMul_add_apply, ProjSpaceCech.GradedModule.monMul_single,
      twistXMul_pow_apply, ih, Finset.prod_insert hks, Finset.sum_insert hks, mul_assoc]
    congr 2
    ring_nf

end AlgebraicGeometry.ProjSpace.GMSec

end

noncomputable section

open CategoryTheory Opposite MvPolynomial HomogeneousLocalization TopologicalSpace

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Spec.map_comp Scheme.mem_basicOpen Scheme.basicOpen_res Surjective Scheme.Hom Proj.basicOpenIsoAway IsFinite Scheme.preimage_basicOpen Spec Spec.map Proj.basicOpenToSpec Scheme Scheme.Hom.appTop Proj.mem_basicOpen Scheme.Opens.topIso_hom Scheme.Hom.comp_appTop Proj IsFinite.finite_app Proj.stalkIso' Proj.basicOpenIsoSpec_inv_ι Proj.isAffineOpen_basicOpen Proj.basicOpen Proj.basicOpen_mul Scheme.basicOpen_mul IsAffineOpen Scheme.Opens IsAffineHom Scheme.Opens.ι_appTop Proj.awayToSection Proj.basicOpenToSpec_app_top Proj.basicOpenIsoSpec_hom Scheme.basicOpen_le ProjectiveSpectrum.Proj.awayToSection_germ Scheme.ΓSpecIso_inv_naturality_assoc Scheme.ΓSpecIso ProjSpace.π ProjSpace.X_mem_one ProjSpace.awayι_comp_π ProjSpace.val_algebraMap ProjSpace.awayMk_monomial Scheme.TwoAffineOpenCover Scheme.TwoAffineOpenCover.algebraOfHom ProjSpace.twistGradedModule"
namespace ProjSpace
p2m_export "AlgebraicGeometry.ProjSpace" "π X_mem_one awayι_comp_π ratio val_algebraMap awayMk_monomial map pullbackChart frameUnit restrictFun TwistCompat restrictFun_restrictFun restrictFun_irrel restrictFun_refl restrictFun_algebraMap' twistObj twistObj.smul_val twistObj.algebraMap_smul twist pullbackOverlap pullbackOverlap_eq_inf frameUnit_cocycle frameUnit_self twistObj.add_val twistObj.zero_val twistFam twistGradedModule isAffineOpen_pullbackChart isAffineOpen_pullbackOverlap twistObj.ext"
namespace GMSec
p2m_open "AlgebraicGeometry.ProjSpace AlgebraicGeometry"

attribute [local instance] MvPolynomial.gradedAlgebra

variable {A : Type u} [CommRing A] {N : ℕ} {X : Scheme.{u}}
  (φ : X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) A)) (π : X ⟶ Spec (.of A)) (m : ℕ)

theorem twistMonMul_shift_apply (k : ℤ) (b : Fin (N + 1) → ℕ) (f : ((twistGradedModule φ π).shift k).M) (d : ℤ) (i : Fin (N + 1)) :
    (ProjSpaceCech.GradedModule.monMul ((twistGradedModule φ π).shift k) b f) d i
      = (∏ j, uTop φ i j ^ b j) * f (d - ∑ j, (b j : ℤ)) i :=
  twistMonMul_apply φ π b f d i

section Psi

variable {I : Finset (Fin (N + 1))} {i₀ : Fin (N + 1)} (hi₀ : i₀ ∈ I)

abbrev Wop (I : Finset (Fin (N + 1))) (i₀ : Fin (N + 1)) : X.Opens := interI φ I ⊓ pullbackChart φ i₀

theorem Wop_le_top : Wop φ I i₀ ≤ (⊤ : X.Opens) ⊓ pullbackChart φ i₀ := inf_le_inf_right _ le_top
theorem Wop_le_self : Wop φ I i₀ ≤ pullbackChart φ i₀ := inf_le_right
theorem Wop_le_chart {j : Fin (N + 1)} (hj : j ∈ I) : Wop φ I i₀ ≤ pullbackChart φ j := inf_le_left.trans (interI_le φ hj)

def invProd (I : Finset (Fin (N + 1))) (i₀ : Fin (N + 1)) (a : Fin (N + 1) → ℕ) : Γ(X, Wop φ I i₀) :=
  ∏ j ∈ I.attach, restrictFun (Wop_le_chart φ j.2) (frameUnit φ j i₀) ^ a j

def dirProd (I : Finset (Fin (N + 1))) (i₀ : Fin (N + 1)) (a : Fin (N + 1) → ℕ) : Γ(X, Wop φ I i₀) :=
  ∏ j ∈ I.attach, restrictFun (Wop_le_self φ) (frameUnit φ i₀ j) ^ a j

theorem dirProd_mul_invProd (a : Fin (N + 1) → ℕ) : dirProd φ I i₀ a * invProd φ I i₀ a = 1 := by
  unfold dirProd invProd
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_eq_one fun j _ => ?_
  rw [← mul_pow, frameUnit_mul_swap_of_le φ i₀ j (Wop_le_self φ) (Wop_le_chart φ j.2), one_pow]

theorem invProd_add (a b : Fin (N + 1) → ℕ) : invProd φ I i₀ (a + b) = invProd φ I i₀ a * invProd φ I i₀ b := by
  unfold invProd
  rw [← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun j _ => by rw [Pi.add_apply, pow_add]

theorem dirProd_add (a b : Fin (N + 1) → ℕ) : dirProd φ I i₀ (a + b) = dirProd φ I i₀ a * dirProd φ I i₀ b := by
  unfold dirProd
  rw [← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun j _ => by rw [Pi.add_apply, pow_add]

theorem restrictFun_prod_uTop {a : Fin (N + 1) → ℕ} (ha : ∀ j ∉ I, a j = 0) :
    restrictFun (Wop_le_top φ) (∏ j, uTop φ i₀ j ^ a j) = dirProd φ I i₀ a := by
  classical
  rw [map_prod]
  have h1 : (∏ j, restrictFun (Wop_le_top φ (I := I)) (uTop φ i₀ j ^ a j))
      = ∏ j ∈ I, restrictFun (Wop_le_top φ (I := I)) (uTop φ i₀ j ^ a j) := by
    refine (Finset.prod_subset (Finset.subset_univ I) fun j _ hj => ?_).symm
    rw [ha j hj, pow_zero, map_one]
  rw [h1, dirProd, ← Finset.prod_attach I]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [map_pow, uTop, restrictFun_restrictFun]

def PsiNum (x : ProjSpaceCech.GradedModule.Frac ((twistGradedModule φ π).shift m) I) : Γ(X, Wop φ I i₀) :=
  restrictFun (Wop_le_top φ) (x.num ((∑ j, (x.denExp j : ℤ)) + m) i₀) * invProd φ I i₀ x.denExp

theorem PsiNum_eq_of_rel {x y : ProjSpaceCech.GradedModule.Frac ((twistGradedModule φ π).shift m) I}
    (h : ProjSpaceCech.GradedModule.Frac.Rel ((twistGradedModule φ π).shift m) I x y) :
    PsiNum φ π m (i₀ := i₀) x = PsiNum φ π m y := by
  obtain ⟨c, hc, heq⟩ := h

  have key := congrFun (congrFun heq ((∑ j, ((c + y.denExp) j : ℤ)) + ((∑ j, (x.denExp j : ℤ)) + m))) i₀
  rw [twistMonMul_shift_apply, twistMonMul_shift_apply, add_sub_cancel_left] at key
  have hdeg : (∑ j, ((c + y.denExp) j : ℤ)) + ((∑ j, (x.denExp j : ℤ)) + m) - ∑ j, ((c + x.denExp) j : ℤ)
      = (∑ j, (y.denExp j : ℤ)) + m := by
    simp only [Pi.add_apply, Nat.cast_add, Finset.sum_add_distrib]; ring
  rw [hdeg] at key

  have key' := congrArg (fun t => restrictFun (Wop_le_top φ (I := I)) t * invProd φ I i₀ (c + x.denExp + y.denExp)) key
  simp only [map_mul] at key'
  rw [restrictFun_prod_uTop φ (fun j hj => by simp [Pi.add_apply, hc j hj, y.hden j hj]),
    restrictFun_prod_uTop φ (fun j hj => by simp [Pi.add_apply, hc j hj, x.hden j hj])] at key'

  have e1 : dirProd φ I i₀ (c + y.denExp) * invProd φ I i₀ (c + x.denExp + y.denExp) = invProd φ I i₀ x.denExp := by
    rw [show c + x.denExp + y.denExp = (c + y.denExp) + x.denExp by abel, invProd_add, ← mul_assoc, dirProd_mul_invProd, one_mul]
  have e2 : dirProd φ I i₀ (c + x.denExp) * invProd φ I i₀ (c + x.denExp + y.denExp) = invProd φ I i₀ y.denExp := by
    rw [invProd_add, ← mul_assoc, dirProd_mul_invProd, one_mul]
  calc PsiNum φ π m x
      = restrictFun (Wop_le_top φ) (x.num ((∑ j, (x.denExp j : ℤ)) + m) i₀)
          * (dirProd φ I i₀ (c + y.denExp) * invProd φ I i₀ (c + x.denExp + y.denExp)) := by rw [e1]; rfl
    _ = restrictFun (Wop_le_top φ) (y.num ((∑ j, (y.denExp j : ℤ)) + m) i₀)
          * (dirProd φ I i₀ (c + x.denExp) * invProd φ I i₀ (c + x.denExp + y.denExp)) := by
        rw [← mul_assoc, ← mul_assoc, mul_comm (restrictFun _ _) (dirProd φ I i₀ (c + y.denExp)),
          mul_comm (restrictFun _ _) (dirProd φ I i₀ (c + x.denExp)), key']
    _ = PsiNum φ π m y := by rw [e2]; rfl

end Psi

end AlgebraicGeometry.ProjSpace.GMSec

end

noncomputable section

open CategoryTheory Opposite MvPolynomial HomogeneousLocalization TopologicalSpace

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Spec.map_comp Scheme.mem_basicOpen Scheme.basicOpen_res Surjective Scheme.Hom Proj.basicOpenIsoAway IsFinite Scheme.preimage_basicOpen Spec Spec.map Proj.basicOpenToSpec Scheme Scheme.Hom.appTop Proj.mem_basicOpen Scheme.Opens.topIso_hom Scheme.Hom.comp_appTop Proj IsFinite.finite_app Proj.stalkIso' Proj.basicOpenIsoSpec_inv_ι Proj.isAffineOpen_basicOpen Proj.basicOpen Proj.basicOpen_mul Scheme.basicOpen_mul IsAffineOpen Scheme.Opens IsAffineHom Scheme.Opens.ι_appTop Proj.awayToSection Proj.basicOpenToSpec_app_top Proj.basicOpenIsoSpec_hom Scheme.basicOpen_le ProjectiveSpectrum.Proj.awayToSection_germ Scheme.ΓSpecIso_inv_naturality_assoc Scheme.ΓSpecIso ProjSpace.π ProjSpace.X_mem_one ProjSpace.awayι_comp_π ProjSpace.val_algebraMap ProjSpace.awayMk_monomial Scheme.TwoAffineOpenCover Scheme.TwoAffineOpenCover.algebraOfHom ProjSpace.twistGradedModule"
namespace ProjSpace
p2m_export "AlgebraicGeometry.ProjSpace" "π X_mem_one awayι_comp_π ratio val_algebraMap awayMk_monomial map pullbackChart frameUnit restrictFun TwistCompat restrictFun_restrictFun restrictFun_irrel restrictFun_refl restrictFun_algebraMap' twistObj twistObj.smul_val twistObj.algebraMap_smul twist pullbackOverlap pullbackOverlap_eq_inf frameUnit_cocycle frameUnit_self twistObj.add_val twistObj.zero_val twistFam twistGradedModule isAffineOpen_pullbackChart isAffineOpen_pullbackOverlap twistObj.ext"
namespace GMSec
p2m_open "AlgebraicGeometry.ProjSpace AlgebraicGeometry"

attribute [local instance] MvPolynomial.gradedAlgebra

variable {A : Type u} [CommRing A] {N : ℕ} {X : Scheme.{u}}
  (φ : X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) A)) (π : X ⟶ Spec (.of A)) (m : ℕ)

section Psi

variable {I : Finset (Fin (N + 1))} {i₀ : Fin (N + 1)}

theorem PsiNum_add_repr (x y : ProjSpaceCech.GradedModule.Frac ((twistGradedModule φ π).shift (m : ℤ)) I)
    (hnum : ProjSpaceCech.GradedModule.monMul ((twistGradedModule φ π).shift (m : ℤ)) y.denExp x.num + ProjSpaceCech.GradedModule.monMul ((twistGradedModule φ π).shift (m : ℤ)) x.denExp y.num
      ∈ ((twistGradedModule φ π).shift (m : ℤ)).grade (∑ j, ((x.denExp + y.denExp) j : ℤ))) :
    PsiNum φ π m (i₀ := i₀) ⟨x.denExp + y.denExp, ProjSpaceCech.GradedModule.Frac.supp_add I x.hden y.hden,
        ProjSpaceCech.GradedModule.monMul ((twistGradedModule φ π).shift (m : ℤ)) y.denExp x.num + ProjSpaceCech.GradedModule.monMul ((twistGradedModule φ π).shift (m : ℤ)) x.denExp y.num, hnum⟩
      = PsiNum φ π m x + PsiNum φ π m y := by
  unfold PsiNum
  simp only
  have hdeg : (∑ j, ((x.denExp + y.denExp) j : ℤ)) + m
      = (∑ j, (y.denExp j : ℤ)) + ((∑ j, (x.denExp j : ℤ)) + m) := by
    simp only [Pi.add_apply, Nat.cast_add, Finset.sum_add_distrib]; ring
  have hdeg' : (∑ j, ((x.denExp + y.denExp) j : ℤ)) + m
      = (∑ j, (x.denExp j : ℤ)) + ((∑ j, (y.denExp j : ℤ)) + m) := by
    simp only [Pi.add_apply, Nat.cast_add, Finset.sum_add_distrib]; ring
  rw [show (ProjSpaceCech.GradedModule.monMul ((twistGradedModule φ π).shift (m : ℤ)) y.denExp x.num + ProjSpaceCech.GradedModule.monMul ((twistGradedModule φ π).shift (m : ℤ)) x.denExp y.num)
      ((∑ j, ((x.denExp + y.denExp) j : ℤ)) + m) i₀
      = (ProjSpaceCech.GradedModule.monMul ((twistGradedModule φ π).shift (m : ℤ)) y.denExp x.num) ((∑ j, ((x.denExp + y.denExp) j : ℤ)) + m) i₀
        + (ProjSpaceCech.GradedModule.monMul ((twistGradedModule φ π).shift (m : ℤ)) x.denExp y.num) ((∑ j, ((x.denExp + y.denExp) j : ℤ)) + m) i₀ from rfl]
  conv_lhs => rw [hdeg]; arg 1; arg 2; arg 2; rw [← hdeg, hdeg']
  rw [twistMonMul_shift_apply, twistMonMul_shift_apply, add_sub_cancel_left, add_sub_cancel_left, map_add, map_mul, map_mul,
    restrictFun_prod_uTop φ y.hden, restrictFun_prod_uTop φ x.hden, invProd_add, add_mul]
  congr 1
  ·
    calc dirProd φ I i₀ y.denExp * restrictFun (Wop_le_top φ) (x.num ((∑ j, (x.denExp j : ℤ)) + m) i₀)
          * (invProd φ I i₀ x.denExp * invProd φ I i₀ y.denExp)
        = restrictFun (Wop_le_top φ) (x.num ((∑ j, (x.denExp j : ℤ)) + m) i₀) * invProd φ I i₀ x.denExp
          * (dirProd φ I i₀ y.denExp * invProd φ I i₀ y.denExp) := by ring
      _ = _ := by rw [dirProd_mul_invProd, mul_one]
  · calc dirProd φ I i₀ x.denExp * restrictFun (Wop_le_top φ) (y.num ((∑ j, (y.denExp j : ℤ)) + m) i₀)
          * (invProd φ I i₀ x.denExp * invProd φ I i₀ y.denExp)
        = restrictFun (Wop_le_top φ) (y.num ((∑ j, (y.denExp j : ℤ)) + m) i₀) * invProd φ I i₀ y.denExp
          * (dirProd φ I i₀ x.denExp * invProd φ I i₀ x.denExp) := by ring
      _ = _ := by rw [dirProd_mul_invProd, mul_one]

theorem PsiNum_smul_repr (r : A) (x : ProjSpaceCech.GradedModule.Frac ((twistGradedModule φ π).shift (m : ℤ)) I) :
    PsiNum φ π m (i₀ := i₀) ⟨x.denExp, x.hden, r • x.num, Submodule.smul_mem _ r x.hnum⟩
      = (Scheme.TwoAffineOpenCover.algebraOfHom π (Wop φ I i₀)).algebraMap r * PsiNum φ π m x := by
  unfold PsiNum
  simp only
  rw [show (r • x.num) ((∑ j, (x.denExp j : ℤ)) + m) i₀
      = (Scheme.TwoAffineOpenCover.algebraOfHom π ((⊤ : X.Opens) ⊓ pullbackChart φ i₀)).algebraMap r
        * x.num ((∑ j, (x.denExp j : ℤ)) + m) i₀ from rfl,
    map_mul, restrictFun_algebraMap' π, mul_assoc]

end Psi

end AlgebraicGeometry.ProjSpace.GMSec

end

noncomputable section

open CategoryTheory Opposite MvPolynomial HomogeneousLocalization TopologicalSpace

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Spec.map_comp Scheme.mem_basicOpen Scheme.basicOpen_res Surjective Scheme.Hom Proj.basicOpenIsoAway IsFinite Scheme.preimage_basicOpen Spec Spec.map Proj.basicOpenToSpec Scheme Scheme.Hom.appTop Proj.mem_basicOpen Scheme.Opens.topIso_hom Scheme.Hom.comp_appTop Proj IsFinite.finite_app Proj.stalkIso' Proj.basicOpenIsoSpec_inv_ι Proj.isAffineOpen_basicOpen Proj.basicOpen Proj.basicOpen_mul Scheme.basicOpen_mul IsAffineOpen Scheme.Opens IsAffineHom Scheme.Opens.ι_appTop Proj.awayToSection Proj.basicOpenToSpec_app_top Proj.basicOpenIsoSpec_hom Scheme.basicOpen_le ProjectiveSpectrum.Proj.awayToSection_germ Scheme.ΓSpecIso_inv_naturality_assoc Scheme.ΓSpecIso ProjSpace.π ProjSpace.X_mem_one ProjSpace.awayι_comp_π ProjSpace.val_algebraMap ProjSpace.awayMk_monomial Scheme.TwoAffineOpenCover Scheme.TwoAffineOpenCover.algebraOfHom ProjSpace.twistGradedModule"
namespace ProjSpace
p2m_export "AlgebraicGeometry.ProjSpace" "π X_mem_one awayι_comp_π ratio val_algebraMap awayMk_monomial map pullbackChart frameUnit restrictFun TwistCompat restrictFun_restrictFun restrictFun_irrel restrictFun_refl restrictFun_algebraMap' twistObj twistObj.smul_val twistObj.algebraMap_smul twist pullbackOverlap pullbackOverlap_eq_inf frameUnit_cocycle frameUnit_self twistObj.add_val twistObj.zero_val twistFam twistGradedModule isAffineOpen_pullbackChart isAffineOpen_pullbackOverlap twistObj.ext"
namespace GMSec
p2m_open "AlgebraicGeometry.ProjSpace AlgebraicGeometry"

attribute [local instance] MvPolynomial.gradedAlgebra

variable {A : Type u} [CommRing A] {N : ℕ} {X : Scheme.{u}}
  (φ : X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) A)) (π : X ⟶ Spec (.of A)) (m : ℕ)

section Psi

variable {I : Finset (Fin (N + 1))} {i₀ : Fin (N + 1)} (hi₀ : i₀ ∈ I)

def PsiFun : ProjSpaceCech.GradedModule.sec ((twistGradedModule φ π).shift (m : ℤ)) I → Γ(X, Wop φ I i₀) :=
  Quotient.lift (PsiNum φ π m (i₀ := i₀)) fun _ _ h => PsiNum_eq_of_rel φ π m h

theorem PsiFun_mk (x : ProjSpaceCech.GradedModule.Frac ((twistGradedModule φ π).shift (m : ℤ)) I) :
    PsiFun φ π m (i₀ := i₀) (ProjSpaceCech.GradedModule.sec.mk _ I x) = PsiNum φ π m x := rfl

theorem PsiFun_add (s t : ProjSpaceCech.GradedModule.sec ((twistGradedModule φ π).shift (m : ℤ)) I) :
    PsiFun φ π m (i₀ := i₀) (s + t) = PsiFun φ π m s + PsiFun φ π m t := by
  induction s using Quotient.inductionOn with
  | h x =>
    induction t using Quotient.inductionOn with
    | h y => exact PsiNum_add_repr φ π m x y _

theorem PsiFun_smul (r : A) (s : ProjSpaceCech.GradedModule.sec ((twistGradedModule φ π).shift (m : ℤ)) I) :
    PsiFun φ π m (i₀ := i₀) (r • s) = (Scheme.TwoAffineOpenCover.algebraOfHom π (Wop φ I i₀)).algebraMap r * PsiFun φ π m s := by
  induction s using Quotient.inductionOn with
  | h x => exact PsiNum_smul_repr φ π m r x

include hi₀ in

def Psi : ProjSpaceCech.GradedModule.sec ((twistGradedModule φ π).shift (m : ℤ)) I →ₗ[A] twistObj π φ m (interI φ I) where
  toFun s := twistObjOfFun φ π m (interI_le φ hi₀) (PsiFun φ π m s)
  map_add' s t := by rw [PsiFun_add, twistObjOfFun_add]
  map_smul' r s := by
    rw [PsiFun_smul, RingHom.id_apply, twistObj.algebraMap_smul, ← twistObjOfFun_smul]
    congr 1
    rw [restrictFun_algebraMap' π]

theorem Psi_val_self (s : ProjSpaceCech.GradedModule.sec ((twistGradedModule φ π).shift (m : ℤ)) I) :
    (Psi φ π m hi₀ s).val i₀ = PsiFun φ π m s :=
  twistObjOfFun_val_self φ π m _ _

theorem Psi_mk_val_self (x : ProjSpaceCech.GradedModule.Frac ((twistGradedModule φ π).shift (m : ℤ)) I) :
    (Psi φ π m hi₀ (ProjSpaceCech.GradedModule.sec.mk _ I x)).val i₀ = PsiNum φ π m x :=
  twistObjOfFun_val_self φ π m _ _

end Psi

end AlgebraicGeometry.ProjSpace.GMSec

end

noncomputable section

open CategoryTheory Opposite MvPolynomial HomogeneousLocalization TopologicalSpace

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Spec.map_comp Scheme.mem_basicOpen Scheme.basicOpen_res Surjective Scheme.Hom Proj.basicOpenIsoAway IsFinite Scheme.preimage_basicOpen Spec Spec.map Proj.basicOpenToSpec Scheme Scheme.Hom.appTop Proj.mem_basicOpen Scheme.Opens.topIso_hom Scheme.Hom.comp_appTop Proj IsFinite.finite_app Proj.stalkIso' Proj.basicOpenIsoSpec_inv_ι Proj.isAffineOpen_basicOpen Proj.basicOpen Proj.basicOpen_mul Scheme.basicOpen_mul IsAffineOpen Scheme.Opens IsAffineHom Scheme.Opens.ι_appTop Proj.awayToSection Proj.basicOpenToSpec_app_top Proj.basicOpenIsoSpec_hom Scheme.basicOpen_le ProjectiveSpectrum.Proj.awayToSection_germ Scheme.ΓSpecIso_inv_naturality_assoc Scheme.ΓSpecIso ProjSpace.π ProjSpace.X_mem_one ProjSpace.awayι_comp_π ProjSpace.val_algebraMap ProjSpace.awayMk_monomial Scheme.TwoAffineOpenCover Scheme.TwoAffineOpenCover.algebraOfHom ProjSpace.twistGradedModule"
namespace ProjSpace
p2m_export "AlgebraicGeometry.ProjSpace" "π X_mem_one awayι_comp_π ratio val_algebraMap awayMk_monomial map pullbackChart frameUnit restrictFun TwistCompat restrictFun_restrictFun restrictFun_irrel restrictFun_refl restrictFun_algebraMap' twistObj twistObj.smul_val twistObj.algebraMap_smul twist pullbackOverlap pullbackOverlap_eq_inf frameUnit_cocycle frameUnit_self twistObj.add_val twistObj.zero_val twistFam twistGradedModule isAffineOpen_pullbackChart isAffineOpen_pullbackOverlap twistObj.ext"
namespace GMSec
p2m_open "AlgebraicGeometry.ProjSpace AlgebraicGeometry"

attribute [local instance] MvPolynomial.gradedAlgebra

variable {A : Type u} [CommRing A] {N : ℕ} {X : Scheme.{u}}
  (φ : X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) A)) (π : X ⟶ Spec (.of A)) (m : ℕ)

theorem exists_pow_mul_eq_zero_of_restrict_basicOpen {V : X.Opens} (hV : IsAffineOpen V) (g s : Γ(X, V))
    (hs : restrictFun (X.basicOpen_le g) s = 0) : ∃ n : ℕ, g ^ n * s = 0 := by
  haveI := hV.isLocalization_basicOpen g
  have h0 : algebraMap Γ(X, V) Γ(X, X.basicOpen g) s = algebraMap Γ(X, V) Γ(X, X.basicOpen g) 0 := by
    rw [map_zero]; exact hs
  obtain ⟨⟨_, n, rfl⟩, hc⟩ := IsLocalization.exists_of_eq (M := Submonoid.powers g) h0
  exact ⟨n, by simpa using hc⟩

theorem exists_pow_mul_eq_zero_of_restrict {V O : X.Opens} (hV : IsAffineOpen V) (g s : Γ(X, V)) (hOV : O ≤ V)
    (hgO : X.basicOpen g ≤ O) (hs : restrictFun hOV s = 0) : ∃ n : ℕ, g ^ n * s = 0 := by
  refine exists_pow_mul_eq_zero_of_restrict_basicOpen hV g s ?_
  have := congrArg (restrictFun hgO) hs
  rwa [map_zero, restrictFun_restrictFun] at this

theorem isAffineOpen_top_inf_pullbackChart [IsAffineHom φ] (i : Fin (N + 1)) :
    IsAffineOpen ((⊤ : X.Opens) ⊓ pullbackChart φ i) := by
  rw [top_inf_eq]; exact isAffineOpen_pullbackChart φ i

section Inj

variable [IsAffineHom φ] {I : Finset (Fin (N + 1))} {i₀ : Fin (N + 1)} (hi₀ : i₀ ∈ I)
include hi₀

theorem stepA (t : Γ(X, (⊤ : X.Opens) ⊓ pullbackChart φ i₀)) (ht : restrictFun (Wop_le_top φ (I := I)) t = 0) :
    ∃ n : ℕ, restrictFun inf_le_right (frameProd φ I i₀) ^ n * t = 0 := by
  refine exists_pow_mul_eq_zero_of_restrict (isAffineOpen_top_inf_pullbackChart φ i₀) _ t (Wop_le_top φ) ?_ ht

  rw [show restrictFun (inf_le_right : (⊤ : X.Opens) ⊓ pullbackChart φ i₀ ≤ pullbackChart φ i₀) (frameProd φ I i₀)
      = (X.presheaf.map (homOfLE (inf_le_right : (⊤ : X.Opens) ⊓ pullbackChart φ i₀ ≤ pullbackChart φ i₀)).op).hom
          (frameProd φ I i₀) from rfl, Scheme.basicOpen_res, ← interI_eq_basicOpen φ hi₀]
  exact le_inf inf_le_right (inf_le_left.trans inf_le_right)

omit hi₀ in

theorem stepB_restrict (e : ℕ) (g : ∀ i, Γ(X, (⊤ : X.Opens) ⊓ pullbackChart φ i)) (hg : TwistCompat φ e ⊤ g)
    (n : ℕ) (i : Fin (N + 1)) :
    restrictFun (inf_le_left : ((⊤ : X.Opens) ⊓ pullbackChart φ i) ⊓ pullbackChart φ i₀ ≤ (⊤ : X.Opens) ⊓ pullbackChart φ i)
        ((∏ j ∈ I, uTop φ i j ^ n) * g i)
      = restrictFun (inf_le_left.trans inf_le_right : ((⊤ : X.Opens) ⊓ pullbackChart φ i) ⊓ pullbackChart φ i₀ ≤ pullbackChart φ i)
          (frameUnit φ i i₀) ^ (n * I.card + e)
        * restrictFun (le_inf (inf_le_left.trans inf_le_left) inf_le_right :
            ((⊤ : X.Opens) ⊓ pullbackChart φ i) ⊓ pullbackChart φ i₀ ≤ (⊤ : X.Opens) ⊓ pullbackChart φ i₀)
          (restrictFun inf_le_right (frameProd φ I i₀) ^ n * g i₀) := by
  have hc := hg i i₀
  rw [map_mul, hc, map_mul, map_pow, map_prod, restrictFun_restrictFun, frameProd, map_prod]

  have hcoc : ∀ j, restrictFun (inf_le_left : ((⊤ : X.Opens) ⊓ pullbackChart φ i) ⊓ pullbackChart φ i₀ ≤ (⊤ : X.Opens) ⊓ pullbackChart φ i)
        (uTop φ i j ^ n)
      = (restrictFun (inf_le_left.trans inf_le_right : ((⊤ : X.Opens) ⊓ pullbackChart φ i) ⊓ pullbackChart φ i₀ ≤ pullbackChart φ i) (frameUnit φ i i₀)
          * restrictFun (inf_le_right : ((⊤ : X.Opens) ⊓ pullbackChart φ i) ⊓ pullbackChart φ i₀ ≤ pullbackChart φ i₀) (frameUnit φ i₀ j)) ^ n := by
    intro j
    rw [map_pow, uTop, restrictFun_restrictFun, frameUnit_cocycle_of_le φ i i₀ j]
  simp only [hcoc, mul_pow, Finset.prod_mul_distrib, Finset.prod_const, Finset.prod_pow]
  ring

theorem stepB (e : ℕ) (g : ∀ i, Γ(X, (⊤ : X.Opens) ⊓ pullbackChart φ i)) (hg : TwistCompat φ e ⊤ g) (n : ℕ)
    (hkill : restrictFun inf_le_right (frameProd φ I i₀) ^ n * g i₀ = 0) (i : Fin (N + 1)) :
    ∃ k : ℕ, uTop φ i i₀ ^ k * ((∏ j ∈ I, uTop φ i j ^ n) * g i) = 0 := by
  refine exists_pow_mul_eq_zero_of_restrict (isAffineOpen_top_inf_pullbackChart φ i) _ _
    (inf_le_left : ((⊤ : X.Opens) ⊓ pullbackChart φ i) ⊓ pullbackChart φ i₀ ≤ (⊤ : X.Opens) ⊓ pullbackChart φ i) ?_ ?_
  · rw [show uTop φ i i₀ = (X.presheaf.map (homOfLE (inf_le_right : (⊤ : X.Opens) ⊓ pullbackChart φ i ≤ pullbackChart φ i)).op).hom
        (frameUnit φ i i₀) from rfl, Scheme.basicOpen_res, ← inf_pullbackChart_eq_basicOpen]
    exact le_inf inf_le_left (inf_le_right.trans inf_le_right)
  · rw [stepB_restrict φ e g hg n i, hkill, map_zero, mul_zero]

end Inj

end AlgebraicGeometry.ProjSpace.GMSec

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Spec.map_comp Scheme.mem_basicOpen Scheme.basicOpen_res Surjective Scheme.Hom Proj.basicOpenIsoAway IsFinite Scheme.preimage_basicOpen Spec Spec.map Proj.basicOpenToSpec Scheme Scheme.Hom.appTop Proj.mem_basicOpen Scheme.Opens.topIso_hom Scheme.Hom.comp_appTop Proj IsFinite.finite_app Proj.stalkIso' Proj.basicOpenIsoSpec_inv_ι Proj.isAffineOpen_basicOpen Proj.basicOpen Proj.basicOpen_mul Scheme.basicOpen_mul IsAffineOpen Scheme.Opens IsAffineHom Scheme.Opens.ι_appTop Proj.awayToSection Proj.basicOpenToSpec_app_top Proj.basicOpenIsoSpec_hom Scheme.basicOpen_le ProjectiveSpectrum.Proj.awayToSection_germ Scheme.ΓSpecIso_inv_naturality_assoc Scheme.ΓSpecIso ProjSpace.π ProjSpace.X_mem_one ProjSpace.awayι_comp_π ProjSpace.val_algebraMap ProjSpace.awayMk_monomial Scheme.TwoAffineOpenCover Scheme.TwoAffineOpenCover.algebraOfHom ProjSpace.twistGradedModule"
namespace ProjSpace
p2m_export "AlgebraicGeometry.ProjSpace" "π X_mem_one awayι_comp_π ratio val_algebraMap awayMk_monomial map pullbackChart frameUnit restrictFun TwistCompat restrictFun_restrictFun restrictFun_irrel restrictFun_refl restrictFun_algebraMap' twistObj twistObj.smul_val twistObj.algebraMap_smul twist pullbackOverlap pullbackOverlap_eq_inf frameUnit_cocycle frameUnit_self twistObj.add_val twistObj.zero_val twistFam twistGradedModule isAffineOpen_pullbackChart isAffineOpen_pullbackOverlap twistObj.ext"
namespace GMSec
p2m_open "AlgebraicGeometry.ProjSpace AlgebraicGeometry"

attribute [local instance] MvPolynomial.gradedAlgebra

variable {A : Type u} [CommRing A] {N : ℕ} {X : Scheme.{u}}
  (φ : X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) A)) (π : X ⟶ Spec (.of A)) (m : ℕ)

section Inj2

variable [IsAffineHom φ] {I : Finset (Fin (N + 1))} {i₀ : Fin (N + 1)} (hi₀ : i₀ ∈ I)
include hi₀

theorem stepC (a : Fin (N + 1) → ℕ) (f : ((twistGradedModule φ π).shift (m : ℤ)).M)
    (hf : f ∈ ((twistGradedModule φ π).shift (m : ℤ)).grade (∑ j, (a j : ℤ)))
    (hW : restrictFun (Wop_le_top φ (I := I)) (f ((∑ j, (a j : ℤ)) + m) i₀) = 0) :
    ∃ c : Fin (N + 1) → ℕ, (∀ j ∉ I, c j = 0) ∧
      ProjSpaceCech.GradedModule.monMul ((twistGradedModule φ π).shift (m : ℤ)) c f = 0 := by
  classical
  set e : ℤ := (∑ j, (a j : ℤ)) + m with he_def
  have he : 0 ≤ e := by positivity
  have hcompat : TwistCompat φ e.toNat ⊤ (f e) := hf.2.2 he
  obtain ⟨n, hn⟩ := stepA φ hi₀ (f e i₀) hW
  choose k hk using fun i => stepB φ hi₀ e.toNat (f e) hcompat n hn i
  set K : ℕ := Finset.univ.sup k with hK
  refine ⟨fun j => (if j ∈ I then n else 0) + (if j = i₀ then K else 0), fun j hj => by
    simp [hj, show j ≠ i₀ from fun h => hj (h ▸ hi₀)], ?_⟩
  funext d i
  rw [twistMonMul_shift_apply]
  show _ = (0 : Γ(X, (⊤ : X.Opens) ⊓ pullbackChart φ i))
  by_cases hd : d - ∑ j, (((if j ∈ I then n else 0) + (if j = i₀ then K else 0) : ℕ) : ℤ) = e
  · rw [hd]
    have hprod : (∏ j, uTop φ i j ^ ((if j ∈ I then n else 0) + (if j = i₀ then K else 0)))
        = uTop φ i i₀ ^ K * ∏ j ∈ I, uTop φ i j ^ n := by
      simp only [pow_add, Finset.prod_mul_distrib, pow_ite, pow_zero, Finset.prod_ite_eq', Finset.mem_univ, if_true,
        Finset.prod_ite_mem, Finset.univ_inter]
      ring
    rw [hprod]
    have hKi : k i ≤ K := Finset.le_sup (f := k) (Finset.mem_univ i)
    calc uTop φ i i₀ ^ K * (∏ j ∈ I, uTop φ i j ^ n) * f e i
        = uTop φ i i₀ ^ (K - k i) * (uTop φ i i₀ ^ k i * ((∏ j ∈ I, uTop φ i j ^ n) * f e i)) := by
          rw [← mul_assoc, ← mul_assoc, ← pow_add, Nat.sub_add_cancel hKi]
      _ = 0 := by rw [hk i, mul_zero]
  · rw [hf.1 _ hd]
    exact mul_zero _

theorem Psi_injective : Function.Injective (Psi φ π m hi₀ (I := I)) := by
  refine (injective_iff_map_eq_zero _).mpr fun s hs => ?_
  induction s using Quotient.inductionOn with
  | h x =>
    obtain ⟨a, ha, f, hf⟩ := x

    have h1 := congrArg (fun g : twistObj π φ m (interI φ I) => g.val i₀) hs
    rw [show (⟦(⟨a, ha, f, hf⟩ : ProjSpaceCech.GradedModule.Frac _ I)⟧ : ProjSpaceCech.GradedModule.sec _ I)
        = ProjSpaceCech.GradedModule.sec.mk _ I ⟨a, ha, f, hf⟩ from rfl, Psi_mk_val_self, twistObj.zero_val] at h1
    have hW : restrictFun (Wop_le_top φ (I := I)) (f ((∑ j, (a j : ℤ)) + m) i₀) = 0 := by
      have h2 := congrArg (fun t => t * dirProd φ I i₀ a) h1
      simp only [PsiNum, Pi.zero_apply, zero_mul, mul_assoc] at h2
      rwa [mul_comm (invProd φ I i₀ a), dirProd_mul_invProd, mul_one] at h2
    obtain ⟨c, hc, hmon⟩ := stepC φ π m hi₀ a f hf hW
    show ProjSpaceCech.GradedModule.sec.mk _ I ⟨a, ha, f, hf⟩
      = ProjSpaceCech.GradedModule.sec.mk _ I ⟨0, fun _ _ => rfl, 0, by simp⟩
    refine (ProjSpaceCech.GradedModule.sec_mk_eq _ I).mpr ⟨c, hc, ?_⟩
    show ProjSpaceCech.GradedModule.monMul _ (c + 0) f = ProjSpaceCech.GradedModule.monMul _ (c + a) 0
    rw [add_zero, map_zero, hmon]

end Inj2

end AlgebraicGeometry.ProjSpace.GMSec

end

noncomputable section

open CategoryTheory Opposite MvPolynomial HomogeneousLocalization TopologicalSpace

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Spec.map_comp Scheme.mem_basicOpen Scheme.basicOpen_res Surjective Scheme.Hom Proj.basicOpenIsoAway IsFinite Scheme.preimage_basicOpen Spec Spec.map Proj.basicOpenToSpec Scheme Scheme.Hom.appTop Proj.mem_basicOpen Scheme.Opens.topIso_hom Scheme.Hom.comp_appTop Proj IsFinite.finite_app Proj.stalkIso' Proj.basicOpenIsoSpec_inv_ι Proj.isAffineOpen_basicOpen Proj.basicOpen Proj.basicOpen_mul Scheme.basicOpen_mul IsAffineOpen Scheme.Opens IsAffineHom Scheme.Opens.ι_appTop Proj.awayToSection Proj.basicOpenToSpec_app_top Proj.basicOpenIsoSpec_hom Scheme.basicOpen_le ProjectiveSpectrum.Proj.awayToSection_germ Scheme.ΓSpecIso_inv_naturality_assoc Scheme.ΓSpecIso ProjSpace.π ProjSpace.X_mem_one ProjSpace.awayι_comp_π ProjSpace.val_algebraMap ProjSpace.awayMk_monomial Scheme.TwoAffineOpenCover Scheme.TwoAffineOpenCover.algebraOfHom ProjSpace.twistGradedModule"
namespace ProjSpace
p2m_export "AlgebraicGeometry.ProjSpace" "π X_mem_one awayι_comp_π ratio val_algebraMap awayMk_monomial map pullbackChart frameUnit restrictFun TwistCompat restrictFun_restrictFun restrictFun_irrel restrictFun_refl restrictFun_algebraMap' twistObj twistObj.smul_val twistObj.algebraMap_smul twist pullbackOverlap pullbackOverlap_eq_inf frameUnit_cocycle frameUnit_self twistObj.add_val twistObj.zero_val twistFam twistGradedModule isAffineOpen_pullbackChart isAffineOpen_pullbackOverlap twistObj.ext"
namespace GMSec
p2m_open "AlgebraicGeometry.ProjSpace AlgebraicGeometry"

attribute [local instance] MvPolynomial.gradedAlgebra

variable {A : Type u} [CommRing A] {N : ℕ} {X : Scheme.{u}}
  (φ : X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) A)) (π : X ⟶ Spec (.of A)) (m : ℕ)

theorem exists_extend_of_affine {V O : X.Opens} (hV : IsAffineOpen V) (g : Γ(X, V)) (hOV : O ≤ V) (hgO : X.basicOpen g ≤ O)
    (s : Γ(X, O)) : ∃ (n : ℕ) (t : Γ(X, V)),
      restrictFun (X.basicOpen_le g) t = restrictFun (X.basicOpen_le g) g ^ n * restrictFun hgO s := by
  haveI := hV.isLocalization_basicOpen g
  obtain ⟨⟨t, ⟨_, n, rfl⟩⟩, ht⟩ := IsLocalization.surj (Submonoid.powers g) (restrictFun hgO s)
  refine ⟨n, t, ?_⟩

  have : restrictFun (X.basicOpen_le g) t = restrictFun hgO s * restrictFun (X.basicOpen_le g) (g ^ n) := ht.symm
  rw [this, map_pow, mul_comm]

theorem restrictFun_self {W : X.Opens} (h : W ≤ W) (x : Γ(X, W)) : restrictFun h x = x := restrictFun_refl x

section Surj

variable [IsAffineHom φ] {I : Finset (Fin (N + 1))} {i₀ : Fin (N + 1)} (hi₀ : i₀ ∈ I)
include hi₀

theorem basicOpen_frameProd_le_Wop :
    X.basicOpen (restrictFun (inf_le_right : (⊤ : X.Opens) ⊓ pullbackChart φ i₀ ≤ pullbackChart φ i₀) (frameProd φ I i₀)) ≤ Wop φ I i₀ := by
  rw [show restrictFun (inf_le_right : (⊤ : X.Opens) ⊓ pullbackChart φ i₀ ≤ pullbackChart φ i₀) (frameProd φ I i₀)
      = (X.presheaf.map (homOfLE (inf_le_right : (⊤ : X.Opens) ⊓ pullbackChart φ i₀ ≤ pullbackChart φ i₀)).op).hom
          (frameProd φ I i₀) from rfl, Scheme.basicOpen_res, ← interI_eq_basicOpen φ hi₀]
  exact le_inf inf_le_right (inf_le_left.trans inf_le_right)

theorem Wop_le_basicOpen_frameProd :
    Wop φ I i₀ ≤ X.basicOpen (restrictFun (inf_le_right : (⊤ : X.Opens) ⊓ pullbackChart φ i₀ ≤ pullbackChart φ i₀) (frameProd φ I i₀)) := by
  rw [show restrictFun (inf_le_right : (⊤ : X.Opens) ⊓ pullbackChart φ i₀ ≤ pullbackChart φ i₀) (frameProd φ I i₀)
      = (X.presheaf.map (homOfLE (inf_le_right : (⊤ : X.Opens) ⊓ pullbackChart φ i₀ ≤ pullbackChart φ i₀)).op).hom
          (frameProd φ I i₀) from rfl, Scheme.basicOpen_res, ← interI_eq_basicOpen φ hi₀]
  exact le_inf (le_inf le_top inf_le_right) inf_le_left

theorem surj_step1 (h : Γ(X, Wop φ I i₀)) : ∃ (n : ℕ) (t : Γ(X, (⊤ : X.Opens) ⊓ pullbackChart φ i₀)),
    restrictFun (Wop_le_top φ) t = restrictFun (Wop_le_top φ) (restrictFun inf_le_right (frameProd φ I i₀)) ^ n * h := by
  obtain ⟨n, t, ht⟩ := exists_extend_of_affine (isAffineOpen_top_inf_pullbackChart φ i₀)
    (restrictFun inf_le_right (frameProd φ I i₀)) (Wop_le_top φ) (basicOpen_frameProd_le_Wop φ hi₀) h
  refine ⟨n, t, ?_⟩
  have key := congrArg (restrictFun (Wop_le_basicOpen_frameProd φ hi₀)) ht
  simp only [map_mul, map_pow, restrictFun_restrictFun, restrictFun_self] at key
  rw [restrictFun_restrictFun]
  exact key

omit hi₀ in

theorem surj_step2 (e₁ : ℕ) (t : Γ(X, (⊤ : X.Opens) ⊓ pullbackChart φ i₀)) (i : Fin (N + 1)) :
    ∃ (k : ℕ) (f : Γ(X, (⊤ : X.Opens) ⊓ pullbackChart φ i)),
      restrictFun (inf_le_left : ((⊤ : X.Opens) ⊓ pullbackChart φ i) ⊓ pullbackChart φ i₀ ≤ (⊤ : X.Opens) ⊓ pullbackChart φ i) f
        = restrictFun (inf_le_left.trans inf_le_right : ((⊤ : X.Opens) ⊓ pullbackChart φ i) ⊓ pullbackChart φ i₀ ≤ pullbackChart φ i)
            (frameUnit φ i i₀) ^ (k + e₁)
          * restrictFun (le_inf (inf_le_left.trans inf_le_left) inf_le_right :
              ((⊤ : X.Opens) ⊓ pullbackChart φ i) ⊓ pullbackChart φ i₀ ≤ (⊤ : X.Opens) ⊓ pullbackChart φ i₀) t := by

  have hle : X.basicOpen (uTop φ i i₀) ≤ ((⊤ : X.Opens) ⊓ pullbackChart φ i) ⊓ pullbackChart φ i₀ := by
    rw [show uTop φ i i₀ = (X.presheaf.map (homOfLE (inf_le_right : (⊤ : X.Opens) ⊓ pullbackChart φ i ≤ pullbackChart φ i)).op).hom
        (frameUnit φ i i₀) from rfl, Scheme.basicOpen_res, ← inf_pullbackChart_eq_basicOpen]
    exact le_inf inf_le_left (inf_le_right.trans inf_le_right)
  have hge : ((⊤ : X.Opens) ⊓ pullbackChart φ i) ⊓ pullbackChart φ i₀ ≤ X.basicOpen (uTop φ i i₀) := by
    rw [show uTop φ i i₀ = (X.presheaf.map (homOfLE (inf_le_right : (⊤ : X.Opens) ⊓ pullbackChart φ i ≤ pullbackChart φ i)).op).hom
        (frameUnit φ i i₀) from rfl, Scheme.basicOpen_res, ← inf_pullbackChart_eq_basicOpen]
    exact le_inf inf_le_left (le_inf (inf_le_left.trans inf_le_right) inf_le_right)
  set s : Γ(X, ((⊤ : X.Opens) ⊓ pullbackChart φ i) ⊓ pullbackChart φ i₀) :=
    restrictFun (inf_le_left.trans inf_le_right : ((⊤ : X.Opens) ⊓ pullbackChart φ i) ⊓ pullbackChart φ i₀ ≤ pullbackChart φ i)
        (frameUnit φ i i₀) ^ e₁
      * restrictFun (le_inf (inf_le_left.trans inf_le_left) inf_le_right :
          ((⊤ : X.Opens) ⊓ pullbackChart φ i) ⊓ pullbackChart φ i₀ ≤ (⊤ : X.Opens) ⊓ pullbackChart φ i₀) t with hs
  obtain ⟨k, f, hf⟩ := exists_extend_of_affine (isAffineOpen_top_inf_pullbackChart φ i) (uTop φ i i₀) inf_le_left hle s
  refine ⟨k, f, ?_⟩
  have key := congrArg (restrictFun hge) hf
  simp only [map_mul, map_pow, restrictFun_restrictFun, restrictFun_self] at key
  rw [key, hs, pow_add]
  ring

end Surj

end AlgebraicGeometry.ProjSpace.GMSec

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Spec.map_comp Scheme.mem_basicOpen Scheme.basicOpen_res Surjective Scheme.Hom Proj.basicOpenIsoAway IsFinite Scheme.preimage_basicOpen Spec Spec.map Proj.basicOpenToSpec Scheme Scheme.Hom.appTop Proj.mem_basicOpen Scheme.Opens.topIso_hom Scheme.Hom.comp_appTop Proj IsFinite.finite_app Proj.stalkIso' Proj.basicOpenIsoSpec_inv_ι Proj.isAffineOpen_basicOpen Proj.basicOpen Proj.basicOpen_mul Scheme.basicOpen_mul IsAffineOpen Scheme.Opens IsAffineHom Scheme.Opens.ι_appTop Proj.awayToSection Proj.basicOpenToSpec_app_top Proj.basicOpenIsoSpec_hom Scheme.basicOpen_le ProjectiveSpectrum.Proj.awayToSection_germ Scheme.ΓSpecIso_inv_naturality_assoc Scheme.ΓSpecIso ProjSpace.π ProjSpace.X_mem_one ProjSpace.awayι_comp_π ProjSpace.val_algebraMap ProjSpace.awayMk_monomial Scheme.TwoAffineOpenCover Scheme.TwoAffineOpenCover.algebraOfHom ProjSpace.twistGradedModule"
namespace ProjSpace
p2m_export "AlgebraicGeometry.ProjSpace" "π X_mem_one awayι_comp_π ratio val_algebraMap awayMk_monomial map pullbackChart frameUnit restrictFun TwistCompat restrictFun_restrictFun restrictFun_irrel restrictFun_refl restrictFun_algebraMap' twistObj twistObj.smul_val twistObj.algebraMap_smul twist pullbackOverlap pullbackOverlap_eq_inf frameUnit_cocycle frameUnit_self twistObj.add_val twistObj.zero_val twistFam twistGradedModule isAffineOpen_pullbackChart isAffineOpen_pullbackOverlap twistObj.ext"
namespace GMSec
p2m_open "AlgebraicGeometry.ProjSpace AlgebraicGeometry"

attribute [local instance] MvPolynomial.gradedAlgebra

variable {A : Type u} [CommRing A] {N : ℕ} {X : Scheme.{u}}
  (φ : X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) A)) (π : X ⟶ Spec (.of A)) (m : ℕ)

theorem isAffineOpen_topChart_inf [IsAffineHom φ] (i j : Fin (N + 1)) :
    IsAffineOpen (((⊤ : X.Opens) ⊓ pullbackChart φ i) ⊓ pullbackChart φ j) := by
  rw [top_inf_eq, ← pullbackOverlap_eq_inf]; exact isAffineOpen_pullbackOverlap φ i j

section Surj3

variable {i₀ : Fin (N + 1)}

abbrev Vt (i : Fin (N + 1)) : X.Opens := (⊤ : X.Opens) ⊓ pullbackChart φ i
abbrev Ot (i i' : Fin (N + 1)) : X.Opens := ((⊤ : X.Opens) ⊓ pullbackChart φ i) ⊓ pullbackChart φ i'

theorem Ot_le_Vt (i i' : Fin (N + 1)) : Ot φ i i' ≤ Vt φ i := inf_le_left
theorem Ot_le_chart_left (i i' : Fin (N + 1)) : Ot φ i i' ≤ pullbackChart φ i := inf_le_left.trans inf_le_right
theorem Ot_le_chart_right (i i' : Fin (N + 1)) : Ot φ i i' ≤ pullbackChart φ i' := inf_le_right
theorem Ot_le_Vt_right (i i' : Fin (N + 1)) : Ot φ i i' ≤ Vt φ i' := le_inf (inf_le_left.trans inf_le_left) inf_le_right

theorem surj_step3a [IsAffineHom φ] (E : ℕ) (t : Γ(X, Vt φ i₀)) (F : ∀ i, Γ(X, Vt φ i))
    (hF : ∀ i, restrictFun (Ot_le_Vt φ i i₀) (F i)
      = restrictFun (Ot_le_chart_left φ i i₀) (frameUnit φ i i₀) ^ E * restrictFun (Ot_le_Vt_right φ i i₀) t)
    (i j : Fin (N + 1)) :
    ∃ r : ℕ, restrictFun (Ot_le_Vt φ i j) (uTop φ i i₀) ^ r
      * (restrictFun (Ot_le_Vt φ i j) (F i)
          - restrictFun (Ot_le_chart_left φ i j) (frameUnit φ i j) ^ E * restrictFun (Ot_le_Vt_right φ i j) (F j)) = 0 := by

  refine exists_pow_mul_eq_zero_of_restrict (isAffineOpen_topChart_inf φ i j) _ _
    (inf_le_left : Ot φ i j ⊓ pullbackChart φ i₀ ≤ Ot φ i j) ?_ ?_
  · rw [show restrictFun (Ot_le_Vt φ i j) (uTop φ i i₀)
        = (X.presheaf.map (homOfLE (Ot_le_chart_left φ i j)).op).hom (frameUnit φ i i₀) from by
          simp only [uTop, restrictFun_restrictFun],
      Scheme.basicOpen_res, ← inf_pullbackChart_eq_basicOpen]
    exact le_inf inf_le_left (inf_le_right.trans inf_le_right)
  ·
    have hi := congrArg (restrictFun (le_inf (inf_le_left.trans (Ot_le_Vt φ i j)) inf_le_right :
      Ot φ i j ⊓ pullbackChart φ i₀ ≤ Ot φ i i₀)) (hF i)
    have hj := congrArg (restrictFun (le_inf (inf_le_left.trans (Ot_le_Vt_right φ i j)) inf_le_right :
      Ot φ i j ⊓ pullbackChart φ i₀ ≤ Ot φ j i₀)) (hF j)
    simp only [map_mul, map_pow, restrictFun_restrictFun] at hi hj
    rw [map_sub, map_mul, map_pow, restrictFun_restrictFun, restrictFun_restrictFun, restrictFun_restrictFun, hi, hj,
      ← mul_assoc, ← mul_pow,
      frameUnit_cocycle_of_le φ i j i₀ (inf_le_left.trans (Ot_le_chart_left φ i j)) (inf_le_left.trans (Ot_le_chart_right φ i j)),
      sub_self]

theorem surj_step3b [IsAffineHom φ] (E : ℕ) (t : Γ(X, Vt φ i₀)) (F : ∀ i, Γ(X, Vt φ i))
    (hF : ∀ i, restrictFun (Ot_le_Vt φ i i₀) (F i)
      = restrictFun (Ot_le_chart_left φ i i₀) (frameUnit φ i i₀) ^ E * restrictFun (Ot_le_Vt_right φ i i₀) t) :
    ∃ R : ℕ, TwistCompat φ (R + E) ⊤ (fun i => uTop φ i i₀ ^ R * F i) := by
  classical
  choose r hr using fun p : Fin (N + 1) × Fin (N + 1) => surj_step3a φ E t F hF p.1 p.2
  refine ⟨Finset.univ.sup r, fun i j => ?_⟩
  have hRij : r (i, j) ≤ Finset.univ.sup r := Finset.le_sup (f := r) (Finset.mem_univ (i, j))
  have key := hr (i, j)
  simp only at key

  have key' := congrArg (fun z => restrictFun (Ot_le_Vt φ i j) (uTop φ i i₀) ^ (Finset.univ.sup r - r (i, j)) * z) key
  simp only [mul_zero, ← mul_assoc, ← pow_add, Nat.sub_add_cancel hRij, mul_sub] at key'

  show restrictFun _ (uTop φ i i₀ ^ Finset.univ.sup r * F i)
    = restrictFun _ (frameUnit φ i j) ^ (Finset.univ.sup r + E) * restrictFun _ (uTop φ j i₀ ^ Finset.univ.sup r * F j)
  rw [map_mul, map_pow, map_mul, map_pow]
  rw [sub_eq_zero] at key'
  rw [key', pow_add]

  have hc := frameUnit_cocycle_of_le φ i j i₀ (Ot_le_chart_left φ i j) (Ot_le_chart_right φ i j)
  have hu : restrictFun (Ot_le_Vt_right φ i j) (uTop φ j i₀) = restrictFun (Ot_le_chart_right φ i j) (frameUnit φ j i₀) := by
    simp only [uTop, restrictFun_restrictFun]
  have hu' : restrictFun (Ot_le_Vt φ i j) (uTop φ i i₀) = restrictFun (Ot_le_chart_left φ i j) (frameUnit φ i i₀) := by
    simp only [uTop, restrictFun_restrictFun]
  rw [hu, hu', ← hc]
  ring

end Surj3

end AlgebraicGeometry.ProjSpace.GMSec

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Spec.map_comp Scheme.mem_basicOpen Scheme.basicOpen_res Surjective Scheme.Hom Proj.basicOpenIsoAway IsFinite Scheme.preimage_basicOpen Spec Spec.map Proj.basicOpenToSpec Scheme Scheme.Hom.appTop Proj.mem_basicOpen Scheme.Opens.topIso_hom Scheme.Hom.comp_appTop Proj IsFinite.finite_app Proj.stalkIso' Proj.basicOpenIsoSpec_inv_ι Proj.isAffineOpen_basicOpen Proj.basicOpen Proj.basicOpen_mul Scheme.basicOpen_mul IsAffineOpen Scheme.Opens IsAffineHom Scheme.Opens.ι_appTop Proj.awayToSection Proj.basicOpenToSpec_app_top Proj.basicOpenIsoSpec_hom Scheme.basicOpen_le ProjectiveSpectrum.Proj.awayToSection_germ Scheme.ΓSpecIso_inv_naturality_assoc Scheme.ΓSpecIso ProjSpace.π ProjSpace.X_mem_one ProjSpace.awayι_comp_π ProjSpace.val_algebraMap ProjSpace.awayMk_monomial Scheme.TwoAffineOpenCover Scheme.TwoAffineOpenCover.algebraOfHom ProjSpace.twistGradedModule"
namespace ProjSpace
p2m_export "AlgebraicGeometry.ProjSpace" "π X_mem_one awayι_comp_π ratio val_algebraMap awayMk_monomial map pullbackChart frameUnit restrictFun TwistCompat restrictFun_restrictFun restrictFun_irrel restrictFun_refl restrictFun_algebraMap' twistObj twistObj.smul_val twistObj.algebraMap_smul twist pullbackOverlap pullbackOverlap_eq_inf frameUnit_cocycle frameUnit_self twistObj.add_val twistObj.zero_val twistFam twistGradedModule isAffineOpen_pullbackChart isAffineOpen_pullbackOverlap twistObj.ext"
namespace GMSec
p2m_open "AlgebraicGeometry.ProjSpace AlgebraicGeometry"

attribute [local instance] MvPolynomial.gradedAlgebra

variable {A : Type u} [CommRing A] {N : ℕ} {X : Scheme.{u}}
  (φ : X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) A)) (π : X ⟶ Spec (.of A)) (m : ℕ)

section Surj4

variable [IsAffineHom φ] {I : Finset (Fin (N + 1))} {i₀ : Fin (N + 1)} (hi₀ : i₀ ∈ I)
include hi₀

theorem invProd_single_self (M : ℕ) : invProd φ I i₀ (Pi.single i₀ M) = 1 := by
  unfold invProd
  refine Finset.prod_eq_one fun j _ => ?_
  by_cases hj : (j : Fin (N + 1)) = i₀
  · have : restrictFun (Wop_le_chart φ (i₀ := i₀) j.2) (frameUnit φ j i₀) = 1 := by
      have h1 : frameUnit φ (j : Fin (N + 1)) i₀ = 1 := by rw [hj, frameUnit_self]
      rw [h1, map_one]
    rw [this, one_pow]
  · rw [Pi.single_apply, if_neg hj, pow_zero]

theorem restrictFun_frameProd_pow (n : ℕ) :
    restrictFun (Wop_le_top φ) (restrictFun (inf_le_right : (⊤ : X.Opens) ⊓ pullbackChart φ i₀ ≤ pullbackChart φ i₀) (frameProd φ I i₀)) ^ n
      = dirProd φ I i₀ (fun j => if j ∈ I then n else 0) := by
  classical
  rw [restrictFun_restrictFun, frameProd, map_prod, ← Finset.prod_attach I, ← Finset.prod_pow, dirProd]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [if_pos j.2]

theorem PsiNum_surjective (h : Γ(X, Wop φ I i₀)) :
    ∃ x : ProjSpaceCech.GradedModule.Frac ((twistGradedModule φ π).shift (m : ℤ)) I, PsiNum φ π m (i₀ := i₀) x = h := by
  classical
  obtain ⟨n, t, ht⟩ := surj_step1 φ hi₀ h
  set e₁ : ℕ := n * I.card + m with he₁
  choose k f hf using fun i => surj_step2 φ (i₀ := i₀) e₁ t i
  set K : ℕ := Finset.univ.sup k with hK

  set F : ∀ i, Γ(X, Vt φ i) := fun i => uTop φ i i₀ ^ (K - k i) * f i with hFdef
  have hF : ∀ i, restrictFun (Ot_le_Vt φ i i₀) (F i)
      = restrictFun (Ot_le_chart_left φ i i₀) (frameUnit φ i i₀) ^ (K + e₁) * restrictFun (Ot_le_Vt_right φ i i₀) t := by
    intro i
    have hKi : k i ≤ K := Finset.le_sup (f := k) (Finset.mem_univ i)
    simp only [hFdef, map_mul, map_pow, hf i, uTop, restrictFun_restrictFun]
    rw [← mul_assoc, ← pow_add, show K - k i + (k i + e₁) = K + e₁ by omega]
  obtain ⟨R, hG⟩ := surj_step3b φ (K + e₁) t F hF

  set c₁ : Fin (N + 1) → ℕ := fun j => if j ∈ I then n else 0 with hc₁
  set a : Fin (N + 1) → ℕ := c₁ + Pi.single i₀ (K + R) with ha_def
  have ha : ∀ j ∉ I, a j = 0 := fun j hj => by
    simp [ha_def, hc₁, hj, show j ≠ i₀ from fun h => hj (h ▸ hi₀)]
  have hdeg : (∑ j, (a j : ℤ)) + m = ((R + (K + e₁) : ℕ) : ℤ) := by
    have h1 : (∑ j, (c₁ j : ℤ)) = n * I.card := by
      simp only [hc₁, Nat.cast_ite, Nat.cast_zero, Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul]
      ring
    have h2 : (∑ j, ((Pi.single i₀ (K + R) : Fin (N + 1) → ℕ) j : ℤ)) = K + R := by
      rw [Finset.sum_eq_single i₀ (fun j _ hj => by simp [Pi.single_apply, hj]) (fun h => absurd (Finset.mem_univ _) h)]
      simp
    simp only [ha_def, Pi.add_apply, Nat.cast_add, Finset.sum_add_distrib, h1, h2, he₁]
    push_cast; ring

  set num : ((twistGradedModule φ π).shift (m : ℤ)).M := fun d => if d = (∑ j, (a j : ℤ)) + m then (fun i => uTop φ i i₀ ^ R * F i) else 0
    with hnum_def
  have hnum : num ∈ ((twistGradedModule φ π).shift (m : ℤ)).grade (∑ j, (a j : ℤ)) := by
    refine ⟨fun d' hd' => ?_, fun hd => ?_, fun hd => ?_⟩
    · simp only [hnum_def, if_neg hd']
    · exfalso; rw [hdeg] at hd; omega
    · show TwistCompat φ _ ⊤ (num ((∑ j, (a j : ℤ)) + m))
      simp only [hnum_def, if_pos rfl, hdeg, Int.toNat_natCast]
      exact hG
  refine ⟨⟨a, ha, num, hnum⟩, ?_⟩

  have hnum_at : num ((∑ j, (a j : ℤ)) + m) = fun i => uTop φ i i₀ ^ R * F i := by simp only [hnum_def, if_pos rfl]
  have hfi₀ : restrictFun (Wop_le_top φ (I := I)) (f i₀) = restrictFun (Wop_le_top φ) t := by
    have := congrArg (restrictFun (le_inf (Wop_le_top φ (I := I)) inf_le_right : Wop φ I i₀ ≤ Ot φ i₀ i₀)) (hf i₀)
    simp only [map_mul, map_pow, restrictFun_restrictFun, frameUnit_self, map_one, one_pow, one_mul] at this
    exact this
  show restrictFun (Wop_le_top φ) (num ((∑ j, (a j : ℤ)) + m) i₀) * invProd φ I i₀ a = h
  rw [hnum_at]
  simp only [hFdef, map_mul, map_pow, uTop, frameUnit_self, map_one, one_pow, one_mul]
  rw [hfi₀, ht, ha_def, invProd_add, invProd_single_self φ hi₀, mul_one, restrictFun_frameProd_pow φ hi₀]
  calc dirProd φ I i₀ c₁ * h * invProd φ I i₀ c₁ = h * (dirProd φ I i₀ c₁ * invProd φ I i₀ c₁) := by ring
    _ = h := by rw [dirProd_mul_invProd, mul_one]

theorem Psi_surjective : Function.Surjective (Psi φ π m hi₀ (I := I)) := by
  intro g
  obtain ⟨x, hx⟩ := PsiNum_surjective φ π m hi₀ (g.val i₀)
  refine ⟨ProjSpaceCech.GradedModule.sec.mk _ I x, ?_⟩
  apply twistObj_eq_of_val_eq φ π m (interI_le φ hi₀)
  rw [Psi_mk_val_self, hx]

theorem Psi_bijective : Function.Bijective (Psi φ π m hi₀ (I := I)) :=
  ⟨Psi_injective φ π m hi₀, Psi_surjective φ π m hi₀⟩

end Surj4

end AlgebraicGeometry.ProjSpace.GMSec

end

noncomputable section

open MvPolynomial

namespace ProjSpaceCech
p2m_export "ProjSpaceCech" "GradedModule GradedModule.monMul GradedModule.monMul_zero GradedModule.monMul_add_apply GradedModule.monMul_single GradedModule.monMul_mem_grade GradedModule.Frac GradedModule.Frac.supp_add GradedModule.Frac.Rel GradedModule.sec GradedModule.sec.mk GradedModule.sec_mk_eq GradedModule.sec_mk_smul GradedModule.freeGrade GradedModule.freeGrade_of_nonneg GradedModule.pi GradedModule.quot GradedModule.FD GradedModule.Hom GradedModule.IsFG"
namespace GradedModule
p2m_export "ProjSpaceCech.GradedModule" "monMul monMul_zero monMul_add_apply monMul_single monMul_mem_grade Frac Frac.supp_add Frac.Rel sec sec.mk sec_mk_eq sec_mk_smul d freeGrade freeGrade_of_nonneg free shift pi quot FD sub Hom Presentation IsFG mk M xMul grade xMul_comm"
p2m_open "ProjSpaceCech.GradedModule ProjSpaceCech"

variable {R : Type u} [CommRing R] {n : ℕ} (D : GradedModule R n)

def evalLin (v : D.M) : MvPolynomial (Fin (n + 1)) R →ₗ[R] D.M :=
  (MvPolynomial.basisMonomials (Fin (n + 1)) R).constr R fun e : Fin (n + 1) →₀ ℕ => GradedModule.monMul D (⇑e) v

theorem evalLin_monomial (v : D.M) (e : Fin (n + 1) →₀ ℕ) (r : R) :
    evalLin D v (monomial e r) = r • GradedModule.monMul D (⇑e) v := by
  have h1 : (monomial e r : MvPolynomial (Fin (n + 1)) R) = r • (MvPolynomial.basisMonomials (Fin (n + 1)) R) e := by
    rw [MvPolynomial.coe_basisMonomials, smul_monomial, smul_eq_mul, mul_one]
  rw [h1, map_smul, evalLin, Module.Basis.constr_basis]

theorem evalLin_X_mul (v : D.M) (j : Fin (n + 1)) (p : MvPolynomial (Fin (n + 1)) R) :
    evalLin D v (X j * p) = D.xMul j (evalLin D v p) := by
  induction p using MvPolynomial.induction_on' with
  | monomial e r =>
    rw [X, monomial_mul, one_mul, evalLin_monomial, evalLin_monomial, map_smul]
    congr 1
    have hcoe : (⇑((Finsupp.single j 1 + e : Fin (n + 1) →₀ ℕ)) : Fin (n + 1) → ℕ) = Pi.single j 1 + ⇑e := by
      funext k
      simp only [Finsupp.coe_add, Pi.add_apply, Finsupp.single_apply, Pi.single_apply]
      by_cases h : j = k
      · subst h; simp
      · simp [h, Ne.symm h]
    rw [hcoe, GradedModule.monMul_add_apply, GradedModule.monMul_single, pow_one]
  | add p q hp hq => rw [mul_add, map_add, map_add, hp, hq, ← map_add]

theorem evalLin_mem_grade {a : ℤ} {v : D.M} (hv : v ∈ D.grade a) {d : ℤ} {p : MvPolynomial (Fin (n + 1)) R}
    (hp : p ∈ (GradedModule.FD R n (-a)).grade d) : evalLin D v p ∈ D.grade d := by
  classical

  change p ∈ GradedModule.freeGrade R n (d + -a) at hp
  by_cases hd : 0 ≤ d + -a
  · rw [GradedModule.freeGrade_of_nonneg R n hd, mem_homogeneousSubmodule] at hp
    rw [p.as_sum, map_sum]
    refine Submodule.sum_mem _ fun e he => ?_
    rw [evalLin_monomial]
    refine Submodule.smul_mem _ _ ?_
    have hdeg : (∑ j, ((⇑e) j : ℤ)) = d + -a := by
      have h1 := hp (mem_support_iff.mp he)
      have h2 : (∑ j, (e j : ℤ)) = ((∑ j ∈ e.support, e j : ℕ) : ℤ) := by
        push_cast
        exact (Finset.sum_subset (Finset.subset_univ _) fun j _ hj => by
          rw [Finsupp.notMem_support_iff.mp hj, Nat.cast_zero]).symm
      rw [h2]
      have h3 : (∑ j ∈ e.support, e j) = (d + -a).toNat := by
        simpa [Finsupp.degree, Finsupp.weight, Finsupp.sum, Finsupp.linearCombination, Finsupp.lsum] using h1
      rw [h3, Int.toNat_of_nonneg hd]
    have := GradedModule.monMul_mem_grade D (⇑e) a v hv
    rwa [hdeg, show a + (d + -a) = d by ring] at this
  · simp only [GradedModule.freeGrade, hd, if_false, Submodule.mem_bot] at hp
    rw [hp, map_zero]
    exact Submodule.zero_mem _

def evalHom {a : ℤ} (v : D.M) (hv : v ∈ D.grade a) : GradedModule.Hom (GradedModule.FD R n (-a)) D where
  toLinearMap := evalLin D v
  mem_grade d p hp := evalLin_mem_grade D hv hp
  xMul_comm j := LinearMap.ext fun p => evalLin_X_mul D v j p

theorem evalHom_one {a : ℤ} (v : D.M) (hv : v ∈ D.grade a) :
    (evalHom D v hv).toLinearMap (1 : MvPolynomial (Fin (n + 1)) R) = v := by
  show evalLin D v (monomial 0 1) = v
  rw [evalLin_monomial, one_smul]
  show GradedModule.monMul D (⇑(0 : Fin (n + 1) →₀ ℕ)) v = v
  rw [show (⇑(0 : Fin (n + 1) →₀ ℕ) : Fin (n + 1) → ℕ) = 0 from rfl, GradedModule.monMul_zero]
  rfl

end ProjSpaceCech.GradedModule

end

noncomputable section

open CategoryTheory Opposite MvPolynomial HomogeneousLocalization TopologicalSpace

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Spec.map_comp Scheme.mem_basicOpen Scheme.basicOpen_res Surjective Scheme.Hom Proj.basicOpenIsoAway IsFinite Scheme.preimage_basicOpen Spec Spec.map Proj.basicOpenToSpec Scheme Scheme.Hom.appTop Proj.mem_basicOpen Scheme.Opens.topIso_hom Scheme.Hom.comp_appTop Proj IsFinite.finite_app Proj.stalkIso' Proj.basicOpenIsoSpec_inv_ι Proj.isAffineOpen_basicOpen Proj.basicOpen Proj.basicOpen_mul Scheme.basicOpen_mul IsAffineOpen Scheme.Opens IsAffineHom Scheme.Opens.ι_appTop Proj.awayToSection Proj.basicOpenToSpec_app_top Proj.basicOpenIsoSpec_hom Scheme.basicOpen_le ProjectiveSpectrum.Proj.awayToSection_germ Scheme.ΓSpecIso_inv_naturality_assoc Scheme.ΓSpecIso ProjSpace.π ProjSpace.X_mem_one ProjSpace.awayι_comp_π ProjSpace.val_algebraMap ProjSpace.awayMk_monomial Scheme.TwoAffineOpenCover Scheme.TwoAffineOpenCover.algebraOfHom ProjSpace.twistGradedModule"
namespace ProjSpace
p2m_export "AlgebraicGeometry.ProjSpace" "π X_mem_one awayι_comp_π ratio val_algebraMap awayMk_monomial map pullbackChart frameUnit restrictFun TwistCompat restrictFun_restrictFun restrictFun_irrel restrictFun_refl restrictFun_algebraMap' twistObj twistObj.smul_val twistObj.algebraMap_smul twist pullbackOverlap pullbackOverlap_eq_inf frameUnit_cocycle frameUnit_self twistObj.add_val twistObj.zero_val twistFam twistGradedModule isAffineOpen_pullbackChart isAffineOpen_pullbackOverlap twistObj.ext"
namespace GMSec
p2m_open "AlgebraicGeometry.ProjSpace AlgebraicGeometry"

attribute [local instance] MvPolynomial.gradedAlgebra

variable {A : Type u} [CommRing A] {N : ℕ} {X : Scheme.{u}}
  (φ : X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) A)) (π : X ⟶ Spec (.of A)) (m : ℕ)

section MonMul

variable [IsAffineHom φ] {I : Finset (Fin (N + 1))} {i₀ : Fin (N + 1)} (hi₀ : i₀ ∈ I)
include hi₀

def monMulFrac (c : Fin (N + 1) → ℕ) (x : ProjSpaceCech.GradedModule.Frac ((twistGradedModule φ π).shift (m : ℤ)) I) :
    ProjSpaceCech.GradedModule.Frac ((twistGradedModule φ π).shift (m : ℤ)) I where
  denExp := x.denExp + Pi.single i₀ (∑ l, c l)
  hden j hj := by
    have : j ≠ i₀ := fun h => hj (h ▸ hi₀)
    simp [Pi.add_apply, x.hden j hj, Pi.single_apply, this]
  num := ProjSpaceCech.GradedModule.monMul ((twistGradedModule φ π).shift (m : ℤ)) c x.num
  hnum := by
    have h := ProjSpaceCech.GradedModule.monMul_mem_grade ((twistGradedModule φ π).shift (m : ℤ)) c _ x.num x.hnum
    convert h using 2
    have hsingle : (∑ j, ((Pi.single i₀ (∑ l, c l) : Fin (N + 1) → ℕ) j : ℤ)) = ∑ l, (c l : ℤ) := by
      rw [Finset.sum_eq_single i₀ (fun j _ hj => by simp [hj]) (fun h => absurd (Finset.mem_univ _) h)]
      simp
    simp only [Pi.add_apply, Nat.cast_add, Finset.sum_add_distrib, hsingle]

theorem PsiNum_monMulFrac (c : Fin (N + 1) → ℕ) (x : ProjSpaceCech.GradedModule.Frac ((twistGradedModule φ π).shift (m : ℤ)) I) :
    PsiNum φ π m (i₀ := i₀) (monMulFrac φ π m hi₀ c x)
      = restrictFun (Wop_le_top φ) (∏ l, uTop φ i₀ l ^ c l) * PsiNum φ π m x := by
  unfold PsiNum monMulFrac
  simp only
  rw [twistMonMul_shift_apply, invProd_add, invProd_single_self φ hi₀, mul_one, map_mul]
  have hsingle : (∑ j, ((Pi.single i₀ (∑ l, c l) : Fin (N + 1) → ℕ) j : ℤ)) = ∑ l, (c l : ℤ) := by
    rw [Finset.sum_eq_single i₀ (fun j _ hj => by simp [hj]) (fun h => absurd (Finset.mem_univ _) h)]
    simp
  have hdeg : (∑ j, ((x.denExp + Pi.single i₀ (∑ l, c l) : Fin (N + 1) → ℕ) j : ℤ)) + m - ∑ l, (c l : ℤ) = (∑ j, (x.denExp j : ℤ)) + m := by
    simp only [Pi.add_apply, Nat.cast_add, Finset.sum_add_distrib, hsingle]
    ring
  rw [hdeg, mul_assoc]

end MonMul

end AlgebraicGeometry.ProjSpace.GMSec

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Spec.map_comp Scheme.mem_basicOpen Scheme.basicOpen_res Surjective Scheme.Hom Proj.basicOpenIsoAway IsFinite Scheme.preimage_basicOpen Spec Spec.map Proj.basicOpenToSpec Scheme Scheme.Hom.appTop Proj.mem_basicOpen Scheme.Opens.topIso_hom Scheme.Hom.comp_appTop Proj IsFinite.finite_app Proj.stalkIso' Proj.basicOpenIsoSpec_inv_ι Proj.isAffineOpen_basicOpen Proj.basicOpen Proj.basicOpen_mul Scheme.basicOpen_mul IsAffineOpen Scheme.Opens IsAffineHom Scheme.Opens.ι_appTop Proj.awayToSection Proj.basicOpenToSpec_app_top Proj.basicOpenIsoSpec_hom Scheme.basicOpen_le ProjectiveSpectrum.Proj.awayToSection_germ Scheme.ΓSpecIso_inv_naturality_assoc Scheme.ΓSpecIso ProjSpace.π ProjSpace.X_mem_one ProjSpace.awayι_comp_π ProjSpace.val_algebraMap ProjSpace.awayMk_monomial Scheme.TwoAffineOpenCover Scheme.TwoAffineOpenCover.algebraOfHom ProjSpace.twistGradedModule"
namespace ProjSpace
p2m_export "AlgebraicGeometry.ProjSpace" "π X_mem_one awayι_comp_π ratio val_algebraMap awayMk_monomial map pullbackChart frameUnit restrictFun TwistCompat restrictFun_restrictFun restrictFun_irrel restrictFun_refl restrictFun_algebraMap' twistObj twistObj.smul_val twistObj.algebraMap_smul twist pullbackOverlap pullbackOverlap_eq_inf frameUnit_cocycle frameUnit_self twistObj.add_val twistObj.zero_val twistFam twistGradedModule isAffineOpen_pullbackChart isAffineOpen_pullbackOverlap twistObj.ext"
namespace GMSec
p2m_open "AlgebraicGeometry.ProjSpace AlgebraicGeometry"

attribute [local instance] MvPolynomial.gradedAlgebra

variable {A : Type u} [CommRing A] {N : ℕ} {X : Scheme.{u}}
  (φ : X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) A))

theorem prod_frameUnit_pow_eq (i₀ : Fin (N + 1)) (e : Fin (N + 1) →₀ ℕ) (d : ℕ) (hd : e.degree = d)
    (hm : MvPolynomial.monomial e (1 : A) ∈ (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) A) (d • 1)) :
    (∏ l, frameUnit φ i₀ l ^ e l)
      = (φ.app (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) A) (MvPolynomial.X i₀))).hom
          ((Proj.awayToSection _ (MvPolynomial.X i₀)).hom
            (HomogeneousLocalization.Away.mk _ (X_mem_one A N i₀) d (MvPolynomial.monomial e (1 : A)) hm)) := by
  rw [ProjSpace.awayMk_monomial A N i₀ d e hd 1 hm, map_one, one_mul, map_prod, map_prod]
  refine Finset.prod_congr rfl fun l _ => ?_
  rw [map_pow, map_pow]
  rfl

end AlgebraicGeometry.ProjSpace.GMSec

end

noncomputable section

open CategoryTheory Opposite MvPolynomial HomogeneousLocalization TopologicalSpace

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Spec.map_comp Scheme.mem_basicOpen Scheme.basicOpen_res Surjective Scheme.Hom Proj.basicOpenIsoAway IsFinite Scheme.preimage_basicOpen Spec Spec.map Proj.basicOpenToSpec Scheme Scheme.Hom.appTop Proj.mem_basicOpen Scheme.Opens.topIso_hom Scheme.Hom.comp_appTop Proj IsFinite.finite_app Proj.stalkIso' Proj.basicOpenIsoSpec_inv_ι Proj.isAffineOpen_basicOpen Proj.basicOpen Proj.basicOpen_mul Scheme.basicOpen_mul IsAffineOpen Scheme.Opens IsAffineHom Scheme.Opens.ι_appTop Proj.awayToSection Proj.basicOpenToSpec_app_top Proj.basicOpenIsoSpec_hom Scheme.basicOpen_le ProjectiveSpectrum.Proj.awayToSection_germ Scheme.ΓSpecIso_inv_naturality_assoc Scheme.ΓSpecIso ProjSpace.π ProjSpace.X_mem_one ProjSpace.awayι_comp_π ProjSpace.val_algebraMap ProjSpace.awayMk_monomial Scheme.TwoAffineOpenCover Scheme.TwoAffineOpenCover.algebraOfHom ProjSpace.twistGradedModule"
namespace ProjSpace
p2m_export "AlgebraicGeometry.ProjSpace" "π X_mem_one awayι_comp_π ratio val_algebraMap awayMk_monomial map pullbackChart frameUnit restrictFun TwistCompat restrictFun_restrictFun restrictFun_irrel restrictFun_refl restrictFun_algebraMap' twistObj twistObj.smul_val twistObj.algebraMap_smul twist pullbackOverlap pullbackOverlap_eq_inf frameUnit_cocycle frameUnit_self twistObj.add_val twistObj.zero_val twistFam twistGradedModule isAffineOpen_pullbackChart isAffineOpen_pullbackOverlap twistObj.ext"
namespace GMSec
p2m_open "AlgebraicGeometry.ProjSpace AlgebraicGeometry"

attribute [local instance] MvPolynomial.gradedAlgebra

variable {A : Type u} [CommRing A] {N : ℕ} {X : Scheme.{u}}
  (φ : X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) A))

local notation "𝒜" => MvPolynomial.homogeneousSubmodule (Fin (N + 1)) A

def fracFun (i : Fin (N + 1)) (k : ℕ) (p : MvPolynomial (Fin (N + 1)) A) (hp : p ∈ 𝒜 (k • 1)) : Γ(X, pullbackChart φ i) :=
  (φ.app (Proj.basicOpen 𝒜 (MvPolynomial.X i))).hom
    ((Proj.awayToSection 𝒜 (MvPolynomial.X i)).hom (HomogeneousLocalization.Away.mk 𝒜 (X_mem_one A N i) k p hp))

theorem exists_fracFun_eq (i : Fin (N + 1)) (t : Γ(Proj 𝒜, Proj.basicOpen 𝒜 (MvPolynomial.X i))) :
    ∃ (k : ℕ) (p : MvPolynomial (Fin (N + 1)) A) (hp : p ∈ 𝒜 (k • 1)),
      (φ.app (Proj.basicOpen 𝒜 (MvPolynomial.X i))).hom t = fracFun φ i k p hp := by
  set z := (Proj.basicOpenIsoAway 𝒜 (MvPolynomial.X i) (X_mem_one A N i) one_pos).inv t with hz
  obtain ⟨k, p, hp, hkp⟩ := HomogeneousLocalization.Away.mk_surjective 𝒜 (X_mem_one A N i) z
  refine ⟨k, p, hp, ?_⟩
  unfold fracFun
  rw [hkp, hz]
  congr 1
  exact (congrArg (fun ψ => CommRingCat.Hom.hom ψ t)
    (Proj.basicOpenIsoAway 𝒜 (MvPolynomial.X i) (X_mem_one A N i) one_pos).inv_hom_id).symm

theorem exists_chart_generators [IsFinite φ] (i : Fin (N + 1)) :
    ∃ (S : Finset Γ(X, pullbackChart φ i)), ∀ s : Γ(X, pullbackChart φ i),
      ∃ (k : Γ(X, pullbackChart φ i) → ℕ) (p : Γ(X, pullbackChart φ i) → MvPolynomial (Fin (N + 1)) A)
        (hp : ∀ g, p g ∈ 𝒜 (k g • 1)),
        s = ∑ g ∈ S, fracFun φ i (k g) (p g) (hp g) * g := by
  classical
  letI alg : Algebra Γ(Proj 𝒜, Proj.basicOpen 𝒜 (MvPolynomial.X i)) Γ(X, pullbackChart φ i) :=
    (φ.app (Proj.basicOpen 𝒜 (MvPolynomial.X i))).hom.toAlgebra
  haveI : Module.Finite Γ(Proj 𝒜, Proj.basicOpen 𝒜 (MvPolynomial.X i)) Γ(X, pullbackChart φ i) :=
    IsFinite.finite_app φ _ (Proj.isAffineOpen_basicOpen 𝒜 _ (X_mem_one A N i) one_pos)
  obtain ⟨S, hS⟩ := Module.Finite.fg_top (R := Γ(Proj 𝒜, Proj.basicOpen 𝒜 (MvPolynomial.X i))) (M := Γ(X, pullbackChart φ i))
  refine ⟨S, fun s => ?_⟩
  have hs : s ∈ Submodule.span Γ(Proj 𝒜, Proj.basicOpen 𝒜 (MvPolynomial.X i)) (S : Set Γ(X, pullbackChart φ i)) := by
    rw [hS]; exact Submodule.mem_top
  obtain ⟨c, _, hc⟩ := Submodule.mem_span_finset.mp hs
  choose k p hp hkp using fun g : Γ(X, pullbackChart φ i) => exists_fracFun_eq φ i (c g)
  refine ⟨k, p, hp, ?_⟩
  rw [← hc]
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [← hkp g]
  rfl

end AlgebraicGeometry.ProjSpace.GMSec

end

noncomputable section

open CategoryTheory Opposite MvPolynomial HomogeneousLocalization TopologicalSpace

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Spec.map_comp Scheme.mem_basicOpen Scheme.basicOpen_res Surjective Scheme.Hom Proj.basicOpenIsoAway IsFinite Scheme.preimage_basicOpen Spec Spec.map Proj.basicOpenToSpec Scheme Scheme.Hom.appTop Proj.mem_basicOpen Scheme.Opens.topIso_hom Scheme.Hom.comp_appTop Proj IsFinite.finite_app Proj.stalkIso' Proj.basicOpenIsoSpec_inv_ι Proj.isAffineOpen_basicOpen Proj.basicOpen Proj.basicOpen_mul Scheme.basicOpen_mul IsAffineOpen Scheme.Opens IsAffineHom Scheme.Opens.ι_appTop Proj.awayToSection Proj.basicOpenToSpec_app_top Proj.basicOpenIsoSpec_hom Scheme.basicOpen_le ProjectiveSpectrum.Proj.awayToSection_germ Scheme.ΓSpecIso_inv_naturality_assoc Scheme.ΓSpecIso ProjSpace.π ProjSpace.X_mem_one ProjSpace.awayι_comp_π ProjSpace.val_algebraMap ProjSpace.awayMk_monomial Scheme.TwoAffineOpenCover Scheme.TwoAffineOpenCover.algebraOfHom ProjSpace.twistGradedModule"
namespace ProjSpace
p2m_export "AlgebraicGeometry.ProjSpace" "π X_mem_one awayι_comp_π ratio val_algebraMap awayMk_monomial map pullbackChart frameUnit restrictFun TwistCompat restrictFun_restrictFun restrictFun_irrel restrictFun_refl restrictFun_algebraMap' twistObj twistObj.smul_val twistObj.algebraMap_smul twist pullbackOverlap pullbackOverlap_eq_inf frameUnit_cocycle frameUnit_self twistObj.add_val twistObj.zero_val twistFam twistGradedModule isAffineOpen_pullbackChart isAffineOpen_pullbackOverlap twistObj.ext"
namespace GMSec
p2m_open "AlgebraicGeometry.ProjSpace AlgebraicGeometry"

attribute [local instance] MvPolynomial.gradedAlgebra

variable {A : Type u} [CommRing A] {N : ℕ} {X : Scheme.{u}}
  (φ : X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) A)) (π : X ⟶ Spec (.of A))

local notation "𝒜" => MvPolynomial.homogeneousSubmodule (Fin (N + 1)) A

section Build

variable [IsFinite φ]

def genSet (i : Fin (N + 1)) : Finset Γ(X, pullbackChart φ i) := (exists_chart_generators φ i).choose

theorem genSet_spec (i : Fin (N + 1)) (s : Γ(X, pullbackChart φ i)) :
    ∃ (k : Γ(X, pullbackChart φ i) → ℕ) (p : Γ(X, pullbackChart φ i) → MvPolynomial (Fin (N + 1)) A)
      (hp : ∀ g, p g ∈ 𝒜 (k g • 1)), s = ∑ g ∈ genSet φ i, fracFun φ i (k g) (p g) (hp g) * g :=
  (exists_chart_generators φ i).choose_spec s

def Gens : Type u := Σ i : Fin (N + 1), (genSet φ i : Set Γ(X, pullbackChart φ i))

scoped instance : Fintype (Gens φ) := by unfold Gens; infer_instance

theorem mem_singleton_self' (i : Fin (N + 1)) : i ∈ ({i} : Finset (Fin (N + 1))) := Finset.mem_singleton_self i

def genTarget (i : Fin (N + 1)) (g : Γ(X, pullbackChart φ i)) : twistObj π φ 0 (interI φ {i}) :=
  twistObjOfFun φ π 0 (interI_le φ (mem_singleton_self' i)) (restrictFun (Wop_le_self φ) g)

def genFrac (t : Gens φ) : ProjSpaceCech.GradedModule.Frac ((twistGradedModule φ π).shift ((0 : ℕ) : ℤ)) {t.1} :=
  (Quotient.exists_rep ((Psi_surjective φ π 0 (mem_singleton_self' t.1) (genTarget φ π t.1 t.2)).choose)).choose

theorem Psi_genFrac (t : Gens φ) :
    Psi φ π 0 (mem_singleton_self' t.1) (ProjSpaceCech.GradedModule.sec.mk _ _ (genFrac φ π t)) = genTarget φ π t.1 t.2 := by
  have h1 := (Quotient.exists_rep ((Psi_surjective φ π 0 (mem_singleton_self' t.1) (genTarget φ π t.1 t.2)).choose)).choose_spec
  have h2 := (Psi_surjective φ π 0 (mem_singleton_self' t.1) (genTarget φ π t.1 t.2)).choose_spec
  rw [← h2]
  exact congrArg _ h1

theorem PsiNum_genFrac (t : Gens φ) :
    PsiNum φ π 0 (i₀ := t.1) (genFrac φ π t) = restrictFun (Wop_le_self φ) (t.2 : Γ(X, pullbackChart φ t.1)) := by
  have h := congrArg (fun g : twistObj π φ 0 (interI φ {t.1}) => g.val t.1) (Psi_genFrac φ π t)
  rwa [Psi_mk_val_self, genTarget, twistObjOfFun_val_self] at h

def genDeg (t : Gens φ) : ℤ := ∑ j, ((genFrac φ π t).denExp j : ℤ)

theorem genFrac_num_mem (t : Gens φ) : (genFrac φ π t).num ∈ (twistGradedModule φ π).grade (genDeg φ π t) := by
  have h := (genFrac φ π t).hnum

  change (genFrac φ π t).num ∈ (twistGradedModule φ π).grade (_ + ((0 : ℕ) : ℤ)) at h
  simpa [genDeg] using h

abbrev GIdx : Type := Fin (Fintype.card (Gens φ))

def gen (t : GIdx φ) : Gens φ := (Fintype.equivFin (Gens φ)).symm t

abbrev Fgen : ProjSpaceCech.GradedModule A N :=
  ProjSpaceCech.GradedModule.pi fun t : GIdx φ => ProjSpaceCech.GradedModule.FD A N (-genDeg φ π (gen φ t))

def psi0Lin : (Fgen φ π).M →ₗ[A] (twistGradedModule φ π).M where
  toFun v := ∑ t : GIdx φ, ProjSpaceCech.GradedModule.evalLin (twistGradedModule φ π) (genFrac φ π (gen φ t)).num (v t)
  map_add' v w := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun t _ => by
      show ProjSpaceCech.GradedModule.evalLin _ _ (v t + w t) = _
      exact map_add _ _ _
  map_smul' r v := by
    rw [RingHom.id_apply, Finset.smul_sum]
    exact Finset.sum_congr rfl fun t _ => by
      show ProjSpaceCech.GradedModule.evalLin _ _ (r • v t) = _
      exact map_smul _ _ _

theorem psi0Lin_apply (v : (Fgen φ π).M) :
    psi0Lin φ π v = ∑ t : GIdx φ, ProjSpaceCech.GradedModule.evalLin (twistGradedModule φ π) (genFrac φ π (gen φ t)).num (v t) := rfl

def psi0 : ProjSpaceCech.GradedModule.Hom (Fgen φ π) (twistGradedModule φ π) where
  toLinearMap := psi0Lin φ π
  mem_grade d v hv := by
    rw [psi0Lin_apply]
    refine Submodule.sum_mem _ fun t _ => ?_
    exact ProjSpaceCech.GradedModule.evalLin_mem_grade _ (genFrac_num_mem φ π (gen φ t)) (hv t (Set.mem_univ t))
  xMul_comm j := by
    refine LinearMap.ext fun v => ?_
    rw [LinearMap.comp_apply, LinearMap.comp_apply, psi0Lin_apply, psi0Lin_apply, map_sum]
    refine Finset.sum_congr rfl fun t _ => ?_
    exact ProjSpaceCech.GradedModule.evalLin_X_mul _ _ j (v t)

theorem psi0_single (t : GIdx φ) (p : MvPolynomial (Fin (N + 1)) A) :
    (psi0 φ π).toLinearMap (Pi.single t p : (Fgen φ π).M)
      = ProjSpaceCech.GradedModule.evalLin (twistGradedModule φ π) (genFrac φ π (gen φ t)).num p := by
  classical
  show psi0Lin φ π (Pi.single t p) = _
  rw [psi0Lin_apply,
    Finset.sum_eq_single t (fun t' _ ht' => by rw [Pi.single_eq_of_ne ht']; exact map_zero _) (fun h => absurd (Finset.mem_univ t) h),
    Pi.single_eq_same]

theorem ker_psi0_stable (j : Fin (N + 1)) : ∀ v ∈ LinearMap.ker (psi0 φ π).toLinearMap,
    (Fgen φ π).xMul j v ∈ LinearMap.ker (psi0 φ π).toLinearMap := by
  intro v hv
  rw [LinearMap.mem_ker] at hv ⊢
  rw [← LinearMap.comp_apply, (psi0 φ π).xMul_comm j, LinearMap.comp_apply, hv, map_zero]

abbrev Mgen : ProjSpaceCech.GradedModule A N :=
  ProjSpaceCech.GradedModule.quot (Fgen φ π) (LinearMap.ker (psi0 φ π).toLinearMap) (ker_psi0_stable φ π)

theorem mem_Mgen_grade_iff (d : ℤ) (z : (Fgen φ π).M ⧸ LinearMap.ker (psi0 φ π).toLinearMap) :
    z ∈ (Mgen φ π).grade d ↔ z ∈ ((Fgen φ π).grade d).map (LinearMap.ker (psi0 φ π).toLinearMap).mkQ := Iff.rfl

def mkQHom : ProjSpaceCech.GradedModule.Hom (Fgen φ π) (Mgen φ π) where
  toLinearMap := (LinearMap.ker (psi0 φ π).toLinearMap).mkQ
  mem_grade d v hv := (mem_Mgen_grade_iff φ π d _).mpr (Submodule.mem_map_of_mem hv)
  xMul_comm j := rfl

theorem Mgen_isFG : (Mgen φ π).IsFG :=
  ⟨{ J := GIdx φ, d₀ := fun t => -genDeg φ π (gen φ t), hom := mkQHom φ π,
     surj := fun d z hz => by
       obtain ⟨v, hv, rfl⟩ := Submodule.mem_map.mp ((mem_Mgen_grade_iff φ π d z).mp hz)
       exact ⟨v, hv, rfl⟩ }⟩

def psi : ProjSpaceCech.GradedModule.Hom (Mgen φ π) (twistGradedModule φ π) where
  toLinearMap := (LinearMap.ker (psi0 φ π).toLinearMap).liftQ (psi0 φ π).toLinearMap le_rfl
  mem_grade d z hz := by
    obtain ⟨v, hv, rfl⟩ := Submodule.mem_map.mp ((mem_Mgen_grade_iff φ π d z).mp hz)
    exact (psi0 φ π).mem_grade d v hv
  xMul_comm j := by
    refine LinearMap.ext fun z => ?_
    obtain ⟨v, rfl⟩ := Submodule.mkQ_surjective _ z
    exact LinearMap.congr_fun ((psi0 φ π).xMul_comm j) v

theorem psi_mkQ (v : (Fgen φ π).M) :
    (psi φ π).toLinearMap ((LinearMap.ker (psi0 φ π).toLinearMap).mkQ v) = (psi0 φ π).toLinearMap v := rfl

theorem psi_injective : Function.Injective (psi φ π).toLinearMap := by
  rw [← LinearMap.ker_eq_bot]
  show LinearMap.ker ((LinearMap.ker (psi0 φ π).toLinearMap).liftQ (psi0 φ π).toLinearMap le_rfl) = ⊥
  rw [Submodule.ker_liftQ, Submodule.mkQ_map_self]

end Build

end AlgebraicGeometry.ProjSpace.GMSec
p2m_reactivate "P2MW.S_AlgebraicGeometry_ProjSpace_exists_isFG_hom_injective_saturated_twistGradedModule.AlgebraicGeometry P2MW.S_AlgebraicGeometry_ProjSpace_exists_isFG_hom_injective_saturated_twistGradedModule.AlgebraicGeometry.ProjSpace P2MW.S_AlgebraicGeometry_ProjSpace_exists_isFG_hom_injective_saturated_twistGradedModule.AlgebraicGeometry.ProjSpace.GMSec"
p2m_reactivate "P2MW.S_AlgebraicGeometry_ProjSpace_exists_isFG_hom_injective_saturated_twistGradedModule.AlgebraicGeometry P2MW.S_AlgebraicGeometry_ProjSpace_exists_isFG_hom_injective_saturated_twistGradedModule.AlgebraicGeometry.ProjSpace"
p2m_reactivate "P2MW.S_AlgebraicGeometry_ProjSpace_exists_isFG_hom_injective_saturated_twistGradedModule.AlgebraicGeometry"

end
p2m_reactivate "P2MW.S_AlgebraicGeometry_ProjSpace_exists_isFG_hom_injective_saturated_twistGradedModule.AlgebraicGeometry P2MW.S_AlgebraicGeometry_ProjSpace_exists_isFG_hom_injective_saturated_twistGradedModule.AlgebraicGeometry.ProjSpace P2MW.S_AlgebraicGeometry_ProjSpace_exists_isFG_hom_injective_saturated_twistGradedModule.AlgebraicGeometry.ProjSpace.GMSec"

noncomputable section

open CategoryTheory Opposite MvPolynomial HomogeneousLocalization TopologicalSpace

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Spec.map_comp Scheme.mem_basicOpen Scheme.basicOpen_res Surjective Scheme.Hom Proj.basicOpenIsoAway IsFinite Scheme.preimage_basicOpen Spec Spec.map Proj.basicOpenToSpec Scheme Scheme.Hom.appTop Proj.mem_basicOpen Scheme.Opens.topIso_hom Scheme.Hom.comp_appTop Proj IsFinite.finite_app Proj.stalkIso' Proj.basicOpenIsoSpec_inv_ι Proj.isAffineOpen_basicOpen Proj.basicOpen Proj.basicOpen_mul Scheme.basicOpen_mul IsAffineOpen Scheme.Opens IsAffineHom Scheme.Opens.ι_appTop Proj.awayToSection Proj.basicOpenToSpec_app_top Proj.basicOpenIsoSpec_hom Scheme.basicOpen_le ProjectiveSpectrum.Proj.awayToSection_germ Scheme.ΓSpecIso_inv_naturality_assoc Scheme.ΓSpecIso ProjSpace.π ProjSpace.X_mem_one ProjSpace.awayι_comp_π ProjSpace.val_algebraMap ProjSpace.awayMk_monomial Scheme.TwoAffineOpenCover Scheme.TwoAffineOpenCover.algebraOfHom ProjSpace.twistGradedModule"
namespace ProjSpace
p2m_export "AlgebraicGeometry.ProjSpace" "π X_mem_one awayι_comp_π ratio val_algebraMap awayMk_monomial map pullbackChart frameUnit restrictFun TwistCompat restrictFun_restrictFun restrictFun_irrel restrictFun_refl restrictFun_algebraMap' twistObj twistObj.smul_val twistObj.algebraMap_smul twist pullbackOverlap pullbackOverlap_eq_inf frameUnit_cocycle frameUnit_self twistObj.add_val twistObj.zero_val twistFam twistGradedModule isAffineOpen_pullbackChart isAffineOpen_pullbackOverlap twistObj.ext"
namespace GMSec
p2m_open "AlgebraicGeometry.ProjSpace AlgebraicGeometry"

attribute [local instance] MvPolynomial.gradedAlgebra

variable {A : Type u} [CommRing A] {N : ℕ} {X : Scheme.{u}}
  (φ : X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) A))

local notation "𝒜" => MvPolynomial.homogeneousSubmodule (Fin (N + 1)) A

theorem app_awayToSection_algebraMap (j : Fin (N + 1)) (r : A) :
    (φ.app (Proj.basicOpen 𝒜 (MvPolynomial.X j))).hom
        ((Proj.awayToSection 𝒜 (MvPolynomial.X j)).hom (algebraMap A (Away 𝒜 (MvPolynomial.X j)) r))
      = (Scheme.TwoAffineOpenCover.algebraOfHom (φ ≫ ProjSpace.π A N) (pullbackChart φ j)).algebraMap r := by

  have hRHS : (Scheme.TwoAffineOpenCover.algebraOfHom (φ ≫ ProjSpace.π A N) (pullbackChart φ j)).algebraMap r
      = (X.presheaf.map (homOfLE (le_top : pullbackChart φ j ≤ ⊤)).op).hom
          ((φ ≫ ProjSpace.π A N).appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom r)) := rfl
  rw [hRHS]

  have hIι : (Proj.basicOpen 𝒜 (MvPolynomial.X j)).ι ≫ ProjSpace.π A N
      = Proj.basicOpenToSpec 𝒜 (MvPolynomial.X j)
        ≫ Spec.map (CommRingCat.ofHom (algebraMap A (Away 𝒜 (MvPolynomial.X j)))) := by
    rw [← ProjSpace.awayι_comp_π A N j, ← Proj.basicOpenIsoSpec_inv_ι 𝒜 _ (X_mem_one A N j) one_pos,
      ← Category.assoc (Proj.basicOpenToSpec 𝒜 _), ← Proj.basicOpenIsoSpec_hom 𝒜 _ (X_mem_one A N j) one_pos,
      Iso.hom_inv_id_assoc]
  have hres := (Scheme.ΓSpecIso (.of A)).inv ≫= congrArg Scheme.Hom.appTop hIι
    =≫ (Proj.basicOpen 𝒜 (MvPolynomial.X j : MvPolynomial (Fin (N + 1)) A)).topIso.hom
  simp only [Scheme.Hom.comp_appTop, Spec.map_comp, Category.assoc] at hres
  rw [← Scheme.ΓSpecIso_inv_naturality_assoc,
    show (Proj.basicOpenToSpec 𝒜 (MvPolynomial.X j : MvPolynomial (Fin (N + 1)) A)).appTop
      = (Proj.basicOpenToSpec 𝒜 _).app ⊤ from rfl,
    Proj.basicOpenToSpec_app_top] at hres
  simp only [Category.assoc] at hres
  rw [Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id, Scheme.Opens.ι_appTop, Scheme.Opens.topIso_hom] at hres
  have hres' := congrArg (fun ψ => CommRingCat.Hom.hom ψ r) hres
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at hres'

  have hιnat := congrArg (fun ψ => CommRingCat.Hom.hom ψ ((ProjSpace.π A N).appTop.hom ((Scheme.ΓSpecIso (.of A)).inv.hom r)))
    (φ.naturality (homOfLE (le_top : Proj.basicOpen 𝒜 (MvPolynomial.X j : MvPolynomial (Fin (N + 1)) A) ≤ ⊤)).op)
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at hιnat
  rw [show ((φ ≫ ProjSpace.π A N).appTop : _) = (ProjSpace.π A N).appTop ≫ φ.appTop from rfl, CommRingCat.hom_comp,
    RingHom.comp_apply]
  refine ((congrArg _ (hres'.symm.trans ?_)).trans hιnat).trans
    (congrArg (fun α => (X.presheaf.map α).hom _) (Subsingleton.elim _ _))
  rw [← CommRingCat.comp_apply]
  exact congrArg (fun ψ => CommRingCat.Hom.hom ψ _)
    ((Eq.symm (CategoryTheory.Functor.map_comp (Proj 𝒜).presheaf _ _)).trans
      (congrArg ((Proj 𝒜).presheaf.map) (Subsingleton.elim _ _)))

theorem awayMk_eq_sum_monomial (j : Fin (N + 1)) (k : ℕ) (p : MvPolynomial (Fin (N + 1)) A) (hp : p ∈ 𝒜 (k • 1))
    (s : Finset (Fin (N + 1) →₀ ℕ)) (hsum : ∑ c ∈ s, MvPolynomial.monomial c (p.coeff c) = p)
    (hmono : ∀ c ∈ s, MvPolynomial.monomial c (1 : A) ∈ 𝒜 (k • 1)) :
    HomogeneousLocalization.Away.mk 𝒜 (X_mem_one A N j) k p hp
      = ∑ c ∈ s.attach, algebraMap A _ (p.coeff c)
          * HomogeneousLocalization.Away.mk 𝒜 (X_mem_one A N j) k (MvPolynomial.monomial c (1 : A)) (hmono c c.2) := by
  classical
  apply HomogeneousLocalization.val_injective
  have hval : (HomogeneousLocalization.val : Away 𝒜 (MvPolynomial.X j : MvPolynomial (Fin (N + 1)) A) → _)
      = algebraMap (Away 𝒜 (MvPolynomial.X j : MvPolynomial (Fin (N + 1)) A))
          (Localization.Away (MvPolynomial.X j : MvPolynomial (Fin (N + 1)) A)) := rfl
  rw [HomogeneousLocalization.Away.val_mk, hval, map_sum]
  simp only [map_mul, ← hval, HomogeneousLocalization.Away.val_mk, ProjSpace.val_algebraMap, ← Localization.mk_one_eq_algebraMap,
    Localization.mk_mul, one_mul, MvPolynomial.C_mul_monomial, mul_one]
  rw [Finset.sum_attach s (fun c => Localization.mk (MvPolynomial.monomial c (p.coeff c))
      (⟨(MvPolynomial.X j : MvPolynomial (Fin (N + 1)) A) ^ k, k, rfl⟩ : Submonoid.powers (MvPolynomial.X j : MvPolynomial (Fin (N + 1)) A))),
    ← Localization.mk_sum, hsum]

theorem fracFun_eq_sum (j : Fin (N + 1)) (k : ℕ) (p : MvPolynomial (Fin (N + 1)) A) (hp : p ∈ 𝒜 (k • 1)) :
    fracFun φ j k p hp
      = ∑ c ∈ p.support, (Scheme.TwoAffineOpenCover.algebraOfHom (φ ≫ ProjSpace.π A N) (pullbackChart φ j)).algebraMap (p.coeff c)
          * ∏ l, frameUnit φ j l ^ c l := by
  classical
  have hhom : p.IsHomogeneous k := by simpa using hp
  have hw : ∀ c ∈ p.support, Finsupp.weight (1 : Fin (N + 1) → ℕ) c = k := fun c hc => hhom (MvPolynomial.mem_support_iff.mp hc)
  have hdeg : ∀ c ∈ p.support, c.degree = k := fun c hc => by rw [Finsupp.degree_eq_weight_one]; exact hw c hc
  have hmono : ∀ c ∈ p.support, MvPolynomial.monomial c (1 : A) ∈ 𝒜 (k • 1) := fun c hc => by
    simpa using MvPolynomial.isHomogeneous_monomial (1 : A) (hdeg c hc)
  unfold fracFun
  rw [awayMk_eq_sum_monomial j k p hp p.support p.as_sum.symm hmono, map_sum, map_sum,
    ← Finset.sum_attach p.support (fun c => (Scheme.TwoAffineOpenCover.algebraOfHom (φ ≫ ProjSpace.π A N) (pullbackChart φ j)).algebraMap
      (p.coeff c) * ∏ l, frameUnit φ j l ^ c l)]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [map_mul, map_mul, app_awayToSection_algebraMap, prod_frameUnit_pow_eq φ j c k (hdeg c c.2) (hmono c c.2)]
  rfl

end AlgebraicGeometry.ProjSpace.GMSec
p2m_reactivate "P2MW.S_AlgebraicGeometry_ProjSpace_exists_isFG_hom_injective_saturated_twistGradedModule.AlgebraicGeometry P2MW.S_AlgebraicGeometry_ProjSpace_exists_isFG_hom_injective_saturated_twistGradedModule.AlgebraicGeometry.ProjSpace P2MW.S_AlgebraicGeometry_ProjSpace_exists_isFG_hom_injective_saturated_twistGradedModule.AlgebraicGeometry.ProjSpace.GMSec"
p2m_reactivate "P2MW.S_AlgebraicGeometry_ProjSpace_exists_isFG_hom_injective_saturated_twistGradedModule.AlgebraicGeometry P2MW.S_AlgebraicGeometry_ProjSpace_exists_isFG_hom_injective_saturated_twistGradedModule.AlgebraicGeometry.ProjSpace P2MW.S_AlgebraicGeometry_ProjSpace_exists_isFG_hom_injective_saturated_twistGradedModule.AlgebraicGeometry.ProjSpace.GMSec"
p2m_reactivate "P2MW.S_AlgebraicGeometry_ProjSpace_exists_isFG_hom_injective_saturated_twistGradedModule.AlgebraicGeometry P2MW.S_AlgebraicGeometry_ProjSpace_exists_isFG_hom_injective_saturated_twistGradedModule.AlgebraicGeometry.ProjSpace P2MW.S_AlgebraicGeometry_ProjSpace_exists_isFG_hom_injective_saturated_twistGradedModule.AlgebraicGeometry.ProjSpace.GMSec"

end
p2m_reactivate "P2MW.S_AlgebraicGeometry_ProjSpace_exists_isFG_hom_injective_saturated_twistGradedModule.AlgebraicGeometry P2MW.S_AlgebraicGeometry_ProjSpace_exists_isFG_hom_injective_saturated_twistGradedModule.AlgebraicGeometry.ProjSpace P2MW.S_AlgebraicGeometry_ProjSpace_exists_isFG_hom_injective_saturated_twistGradedModule.AlgebraicGeometry.ProjSpace.GMSec"

noncomputable section

open CategoryTheory Opposite MvPolynomial HomogeneousLocalization TopologicalSpace

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Spec.map_comp Scheme.mem_basicOpen Scheme.basicOpen_res Surjective Scheme.Hom Proj.basicOpenIsoAway IsFinite Scheme.preimage_basicOpen Spec Spec.map Proj.basicOpenToSpec Scheme Scheme.Hom.appTop Proj.mem_basicOpen Scheme.Opens.topIso_hom Scheme.Hom.comp_appTop Proj IsFinite.finite_app Proj.stalkIso' Proj.basicOpenIsoSpec_inv_ι Proj.isAffineOpen_basicOpen Proj.basicOpen Proj.basicOpen_mul Scheme.basicOpen_mul IsAffineOpen Scheme.Opens IsAffineHom Scheme.Opens.ι_appTop Proj.awayToSection Proj.basicOpenToSpec_app_top Proj.basicOpenIsoSpec_hom Scheme.basicOpen_le ProjectiveSpectrum.Proj.awayToSection_germ Scheme.ΓSpecIso_inv_naturality_assoc Scheme.ΓSpecIso ProjSpace.π ProjSpace.X_mem_one ProjSpace.awayι_comp_π ProjSpace.val_algebraMap ProjSpace.awayMk_monomial Scheme.TwoAffineOpenCover Scheme.TwoAffineOpenCover.algebraOfHom ProjSpace.twistGradedModule"
namespace ProjSpace
p2m_export "AlgebraicGeometry.ProjSpace" "π X_mem_one awayι_comp_π ratio val_algebraMap awayMk_monomial map pullbackChart frameUnit restrictFun TwistCompat restrictFun_restrictFun restrictFun_irrel restrictFun_refl restrictFun_algebraMap' twistObj twistObj.smul_val twistObj.algebraMap_smul twist pullbackOverlap pullbackOverlap_eq_inf frameUnit_cocycle frameUnit_self twistObj.add_val twistObj.zero_val twistFam twistGradedModule isAffineOpen_pullbackChart isAffineOpen_pullbackOverlap twistObj.ext"
namespace GMSec
p2m_open "AlgebraicGeometry.ProjSpace AlgebraicGeometry"

attribute [local instance] MvPolynomial.gradedAlgebra

variable {A : Type u} [CommRing A] {N : ℕ} {X : Scheme.{u}}
  (φ : X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) A)) (π : X ⟶ Spec (.of A))

local notation "𝒜" => MvPolynomial.homogeneousSubmodule (Fin (N + 1)) A

theorem twistObj_sum_val {m : ℕ} {U : X.Opens} {ι : Type*} (s : Finset ι) (f : ι → twistObj π φ m U) (i : Fin (N + 1)) :
    (∑ a ∈ s, f a).val i = ∑ a ∈ s, (f a).val i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [twistObj.zero_val]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, twistObj.add_val, Pi.add_apply, ih]

theorem eq_single_of_supp {j : Fin (N + 1)} (b : Fin (N + 1) → ℕ) (hb : ∀ l ∉ ({j} : Finset (Fin (N + 1))), b l = 0) :
    b = Pi.single j (b j) := by
  funext l
  by_cases h : l = j
  · subst h; simp
  · rw [Pi.single_eq_of_ne h, hb l (by simpa using h)]

theorem sum_cast_eq_of_supp {j : Fin (N + 1)} (b : Fin (N + 1) → ℕ) (hb : ∀ l ∉ ({j} : Finset (Fin (N + 1))), b l = 0) :
    (∑ l, (b l : ℤ)) = b j := by
  rw [Finset.sum_eq_single j (fun l _ hl => by rw [hb l (by simpa using hl), Nat.cast_zero]) (fun h => absurd (Finset.mem_univ j) h)]

section Sat

variable [IsFinite φ]

def Good (j : Fin (N + 1)) (z : ProjSpaceCech.GradedModule.sec ((twistGradedModule φ π).shift ((0 : ℕ) : ℤ)) {j}) : Prop :=
  ∃ (b : Fin (N + 1) → ℕ) (hb : ∀ l ∉ ({j} : Finset (Fin (N + 1))), b l = 0) (v : (Fgen φ π).M)
    (hv : v ∈ (Fgen φ π).grade (∑ l, (b l : ℤ)))
    (hnum : (psi0 φ π).toLinearMap v ∈ ((twistGradedModule φ π).shift ((0 : ℕ) : ℤ)).grade (∑ l, (b l : ℤ))),
    z = ProjSpaceCech.GradedModule.sec.mk ((twistGradedModule φ π).shift ((0 : ℕ) : ℤ)) {j} ⟨b, hb, (psi0 φ π).toLinearMap v, hnum⟩

theorem psi0_mem_shift_grade {d : ℤ} {v : (Fgen φ π).M} (hv : v ∈ (Fgen φ π).grade d) :
    (psi0 φ π).toLinearMap v ∈ ((twistGradedModule φ π).shift ((0 : ℕ) : ℤ)).grade d := by
  show (psi0 φ π).toLinearMap v ∈ (twistGradedModule φ π).grade (d + ((0 : ℕ) : ℤ))
  rw [Nat.cast_zero, add_zero]
  exact (psi0 φ π).mem_grade d v hv

theorem monMul_shift_eq (k : ℤ) (a : Fin (N + 1) → ℕ) :
    ProjSpaceCech.GradedModule.monMul ((twistGradedModule φ π).shift k) a = ProjSpaceCech.GradedModule.monMul (twistGradedModule φ π) a := rfl

theorem good_zero (j : Fin (N + 1)) : Good φ π j 0 := by
  refine ⟨0, fun _ _ => rfl, 0, Submodule.zero_mem _, by rw [map_zero]; exact Submodule.zero_mem _, ?_⟩
  have h0 : (psi0 φ π).toLinearMap 0 = 0 := map_zero _
  show (0 : ProjSpaceCech.GradedModule.sec ((twistGradedModule φ π).shift ((0 : ℕ) : ℤ)) {j}) = _
  simp only [h0]
  rfl

theorem good_add (j : Fin (N + 1)) {z w : ProjSpaceCech.GradedModule.sec ((twistGradedModule φ π).shift ((0 : ℕ) : ℤ)) {j}}
    (hz : Good φ π j z) (hw : Good φ π j w) : Good φ π j (z + w) := by
  obtain ⟨b₁, hb₁, v₁, hv₁, hn₁, rfl⟩ := hz
  obtain ⟨b₂, hb₂, v₂, hv₂, hn₂, rfl⟩ := hw
  refine ⟨b₁ + b₂, ProjSpaceCech.GradedModule.Frac.supp_add {j} hb₁ hb₂,
    ProjSpaceCech.GradedModule.monMul (Fgen φ π) b₂ v₁ + ProjSpaceCech.GradedModule.monMul (Fgen φ π) b₁ v₂, ?_, ?_, ?_⟩
  · refine Submodule.add_mem _ ?_ ?_
    · have h := ProjSpaceCech.GradedModule.monMul_mem_grade (Fgen φ π) b₂ _ v₁ hv₁
      convert h using 2; simp only [Pi.add_apply, Nat.cast_add, Finset.sum_add_distrib]
    · have h := ProjSpaceCech.GradedModule.monMul_mem_grade (Fgen φ π) b₁ _ v₂ hv₂
      convert h using 2; simp only [Pi.add_apply, Nat.cast_add, Finset.sum_add_distrib]; ring
  · exact psi0_mem_shift_grade φ π (by
      refine Submodule.add_mem _ ?_ ?_
      · have h := ProjSpaceCech.GradedModule.monMul_mem_grade (Fgen φ π) b₂ _ v₁ hv₁
        convert h using 2; simp only [Pi.add_apply, Nat.cast_add, Finset.sum_add_distrib]
      · have h := ProjSpaceCech.GradedModule.monMul_mem_grade (Fgen φ π) b₁ _ v₂ hv₂
        convert h using 2; simp only [Pi.add_apply, Nat.cast_add, Finset.sum_add_distrib]; ring)
  ·
    apply (ProjSpaceCech.GradedModule.sec_mk_eq _ {j}).mpr
    refine ⟨0, fun _ _ => rfl, ?_⟩
    simp only [zero_add, map_add, monMul_shift_eq, (psi0 φ π).map_monMul]
    exact (map_add _ _ _).symm

theorem good_smul_monMulFrac (t : Gens φ) (r : A) (c : Fin (N + 1) → ℕ) :
    Good φ π t.1 (r • ProjSpaceCech.GradedModule.sec.mk _ {t.1} (monMulFrac φ π 0 (mem_singleton_self' t.1) c (genFrac φ π t))) := by
  classical
  set t' : GIdx φ := Fintype.equivFin (Gens φ) t with ht'
  have hgen : gen φ t' = t := by simp [gen, ht']

  let cf : Fin (N + 1) →₀ ℕ := Finsupp.equivFunOnFinite.symm c
  have hcf : (⇑cf : Fin (N + 1) → ℕ) = c := by simp [cf]
  have hψ : (psi0 φ π).toLinearMap (Pi.single t' (MvPolynomial.monomial cf r) : (Fgen φ π).M)
      = r • ProjSpaceCech.GradedModule.monMul ((twistGradedModule φ π).shift ((0 : ℕ) : ℤ)) c (genFrac φ π t).num := by
    rw [psi0_single, ProjSpaceCech.GradedModule.evalLin_monomial, hcf, hgen]
    rfl
  refine ⟨(monMulFrac φ π 0 (mem_singleton_self' t.1) c (genFrac φ π t)).denExp,
    (monMulFrac φ π 0 (mem_singleton_self' t.1) c (genFrac φ π t)).hden,
    Pi.single t' (MvPolynomial.monomial cf r), ?_, ?_, ?_⟩
  ·
    intro k _
    by_cases hk : k = t'
    · subst hk
      rw [Pi.single_eq_same]
      show MvPolynomial.monomial cf r ∈ ProjSpaceCech.GradedModule.freeGrade A N (_ + -genDeg φ π (gen φ _))
      rw [hgen]
      have hsingle : (∑ l, ((Pi.single t.1 (∑ l, c l) : Fin (N + 1) → ℕ) l : ℤ)) = ((∑ l, c l : ℕ) : ℤ) := by
        rw [sum_cast_eq_of_supp (j := t.1) _ (fun l hl => Pi.single_eq_of_ne (by simpa using hl) _), Pi.single_eq_same]
      have hsum : (∑ l, (((monMulFrac φ π 0 (mem_singleton_self' t.1) c (genFrac φ π t)).denExp l : ℕ) : ℤ)) + -genDeg φ π t
          = ((∑ l, c l : ℕ) : ℤ) := by
        simp only [monMulFrac, genDeg, Pi.add_apply, Nat.cast_add, Finset.sum_add_distrib, hsingle]
        ring
      rw [hsum, ProjSpaceCech.GradedModule.freeGrade_of_nonneg A N (by positivity), Int.toNat_natCast,
        MvPolynomial.mem_homogeneousSubmodule]
      intro d' hd'
      rw [MvPolynomial.coeff_monomial] at hd'
      split_ifs at hd' with h
      · subst h
        rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (fun _ => by simp)]
        simp [hcf]
      · exact absurd rfl hd'
    · rw [Pi.single_eq_of_ne hk]
      exact Submodule.zero_mem _
  · rw [hψ]
    exact Submodule.smul_mem _ r (monMulFrac φ π 0 (mem_singleton_self' t.1) c (genFrac φ π t)).hnum
  · rw [ProjSpaceCech.GradedModule.sec_mk_smul]
    apply (ProjSpaceCech.GradedModule.sec_mk_eq _ {t.1}).mpr
    refine ⟨0, fun _ _ => rfl, ?_⟩
    dsimp only
    rw [hψ]
    rfl

end Sat
p2m_reactivate "P2MW.S_AlgebraicGeometry_ProjSpace_exists_isFG_hom_injective_saturated_twistGradedModule.AlgebraicGeometry P2MW.S_AlgebraicGeometry_ProjSpace_exists_isFG_hom_injective_saturated_twistGradedModule.AlgebraicGeometry.ProjSpace P2MW.S_AlgebraicGeometry_ProjSpace_exists_isFG_hom_injective_saturated_twistGradedModule.AlgebraicGeometry.ProjSpace.GMSec"

end AlgebraicGeometry.ProjSpace.GMSec
p2m_reactivate "P2MW.S_AlgebraicGeometry_ProjSpace_exists_isFG_hom_injective_saturated_twistGradedModule.AlgebraicGeometry P2MW.S_AlgebraicGeometry_ProjSpace_exists_isFG_hom_injective_saturated_twistGradedModule.AlgebraicGeometry.ProjSpace P2MW.S_AlgebraicGeometry_ProjSpace_exists_isFG_hom_injective_saturated_twistGradedModule.AlgebraicGeometry.ProjSpace.GMSec"
p2m_reactivate "P2MW.S_AlgebraicGeometry_ProjSpace_exists_isFG_hom_injective_saturated_twistGradedModule.AlgebraicGeometry P2MW.S_AlgebraicGeometry_ProjSpace_exists_isFG_hom_injective_saturated_twistGradedModule.AlgebraicGeometry.ProjSpace P2MW.S_AlgebraicGeometry_ProjSpace_exists_isFG_hom_injective_saturated_twistGradedModule.AlgebraicGeometry.ProjSpace.GMSec"
p2m_reactivate "P2MW.S_AlgebraicGeometry_ProjSpace_exists_isFG_hom_injective_saturated_twistGradedModule.AlgebraicGeometry P2MW.S_AlgebraicGeometry_ProjSpace_exists_isFG_hom_injective_saturated_twistGradedModule.AlgebraicGeometry.ProjSpace P2MW.S_AlgebraicGeometry_ProjSpace_exists_isFG_hom_injective_saturated_twistGradedModule.AlgebraicGeometry.ProjSpace.GMSec"

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Spec.map_comp Scheme.mem_basicOpen Scheme.basicOpen_res Surjective Scheme.Hom Proj.basicOpenIsoAway IsFinite Scheme.preimage_basicOpen Spec Spec.map Proj.basicOpenToSpec Scheme Scheme.Hom.appTop Proj.mem_basicOpen Scheme.Opens.topIso_hom Scheme.Hom.comp_appTop Proj IsFinite.finite_app Proj.stalkIso' Proj.basicOpenIsoSpec_inv_ι Proj.isAffineOpen_basicOpen Proj.basicOpen Proj.basicOpen_mul Scheme.basicOpen_mul IsAffineOpen Scheme.Opens IsAffineHom Scheme.Opens.ι_appTop Proj.awayToSection Proj.basicOpenToSpec_app_top Proj.basicOpenIsoSpec_hom Scheme.basicOpen_le ProjectiveSpectrum.Proj.awayToSection_germ Scheme.ΓSpecIso_inv_naturality_assoc Scheme.ΓSpecIso ProjSpace.π ProjSpace.X_mem_one ProjSpace.awayι_comp_π ProjSpace.val_algebraMap ProjSpace.awayMk_monomial Scheme.TwoAffineOpenCover Scheme.TwoAffineOpenCover.algebraOfHom ProjSpace.twistGradedModule"
namespace ProjSpace
p2m_export "AlgebraicGeometry.ProjSpace" "π X_mem_one awayι_comp_π ratio val_algebraMap awayMk_monomial map pullbackChart frameUnit restrictFun TwistCompat restrictFun_restrictFun restrictFun_irrel restrictFun_refl restrictFun_algebraMap' twistObj twistObj.smul_val twistObj.algebraMap_smul twist pullbackOverlap pullbackOverlap_eq_inf frameUnit_cocycle frameUnit_self twistObj.add_val twistObj.zero_val twistFam twistGradedModule isAffineOpen_pullbackChart isAffineOpen_pullbackOverlap twistObj.ext"
namespace GMSec
p2m_open "AlgebraicGeometry.ProjSpace AlgebraicGeometry"

attribute [local instance] MvPolynomial.gradedAlgebra

variable {A : Type u} [CommRing A] {N : ℕ} {X : Scheme.{u}}
  (φ : X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) A))

section Sat2

variable [IsFinite φ]

theorem good_sum (π : X ⟶ Spec (.of A)) (j : Fin (N + 1)) {ι : Type*} (s : Finset ι)
    (f : ι → ProjSpaceCech.GradedModule.sec ((twistGradedModule φ π).shift ((0 : ℕ) : ℤ)) {j}) (hf : ∀ a ∈ s, Good φ π j (f a)) :
    Good φ π j (∑ a ∈ s, f a) :=
  Finset.sum_induction f (Good φ π j) (fun _ _ hz hw => good_add φ π j hz hw) (good_zero φ π j) hf

omit [IsFinite φ] in
theorem pullbackChart_le_Wop (j : Fin (N + 1)) : pullbackChart φ j ≤ Wop φ {j} j :=
  le_inf (le_iInf fun i => le_iInf fun hi => by rw [Finset.mem_singleton.mp hi]) le_rfl

omit [IsFinite φ] in
theorem restrictFun_prod_uTop' (j : Fin (N + 1)) (c : Fin (N + 1) → ℕ) :
    restrictFun (Wop_le_top φ (I := {j})) (∏ l, uTop φ j l ^ c l) = restrictFun (Wop_le_self φ) (∏ l, frameUnit φ j l ^ c l) := by
  simp only [map_prod, map_pow, uTop, restrictFun_restrictFun]

theorem psi_saturated (π : X ⟶ Spec (.of A)) (hπ : φ ≫ ProjSpace.π A N = π) (j : Fin (N + 1)) (e : ℤ)
    (x : (twistGradedModule φ π).M) (hx : x ∈ (twistGradedModule φ π).grade e) :
    ∃ K : ℕ, ∃ x' ∈ (Mgen φ π).grade (e + K),
      (psi φ π).toLinearMap x' = ((twistGradedModule φ π).xMul j ^ K) x := by
  classical
  subst hπ

  by_cases he : 0 ≤ e
  swap
  · have hx0 : x = 0 := by
      funext d
      show x d = 0
      by_cases hd : d = e
      · subst hd; exact hx.2.1 (lt_of_not_ge he)
      · exact hx.1 d hd
    refine ⟨0, 0, Submodule.zero_mem _, ?_⟩
    rw [hx0, map_zero, map_zero]

  have hj : j ∈ ({j} : Finset (Fin (N + 1))) := mem_singleton_self' j
  set a : Fin (N + 1) → ℕ := Pi.single j e.toNat with ha_def
  have ha : ∀ l ∉ ({j} : Finset (Fin (N + 1))), a l = 0 := fun l hl => by
    rw [ha_def, Pi.single_eq_of_ne (by simpa using hl)]
  have hasum : (∑ l, (a l : ℤ)) = e := by
    rw [sum_cast_eq_of_supp a ha, ha_def, Pi.single_eq_same, Int.toNat_of_nonneg he]
  have hxnum : x ∈ ((twistGradedModule φ (φ ≫ ProjSpace.π A N)).shift ((0 : ℕ) : ℤ)).grade (∑ l, (a l : ℤ)) := by
    show x ∈ (twistGradedModule φ (φ ≫ ProjSpace.π A N)).grade (_ + ((0 : ℕ) : ℤ))
    rw [hasum, Nat.cast_zero, add_zero]; exact hx
  let X₀ : ProjSpaceCech.GradedModule.Frac ((twistGradedModule φ (φ ≫ ProjSpace.π A N)).shift ((0 : ℕ) : ℤ)) {j} := ⟨a, ha, x, hxnum⟩

  set s : Γ(X, pullbackChart φ j) := restrictFun (pullbackChart_le_Wop φ j) (PsiNum φ (φ ≫ ProjSpace.π A N) 0 (i₀ := j) X₀) with hs
  obtain ⟨k, p, hp, hsum⟩ := genSet_spec φ j s
  have hs0 : PsiNum φ (φ ≫ ProjSpace.π A N) 0 (i₀ := j) X₀ = restrictFun (Wop_le_self φ) s := by
    rw [hs, restrictFun_restrictFun, restrictFun_self]

  let term : (genSet φ j) → (Fin (N + 1) →₀ ℕ) → ProjSpaceCech.GradedModule.sec ((twistGradedModule φ (φ ≫ ProjSpace.π A N)).shift ((0 : ℕ) : ℤ)) {j} :=
    fun g cc => ((p g).coeff cc) • ProjSpaceCech.GradedModule.sec.mk _ {j}
      (monMulFrac φ (φ ≫ ProjSpace.π A N) 0 hj (⇑cc) (genFrac φ (φ ≫ ProjSpace.π A N) ⟨j, g⟩))
  set Y := ∑ g ∈ (genSet φ j).attach, ∑ cc ∈ (p g).support, term g cc with hY
  have hY_good : Good φ (φ ≫ ProjSpace.π A N) j Y :=
    good_sum φ (φ ≫ ProjSpace.π A N) j _ _ fun g _ => good_sum φ (φ ≫ ProjSpace.π A N) j _ _ fun cc _ => good_smul_monMulFrac φ (φ ≫ ProjSpace.π A N) ⟨j, g⟩ _ _

  have hterm : ∀ (g : genSet φ j) (cc : Fin (N + 1) →₀ ℕ),
      (Psi φ (φ ≫ ProjSpace.π A N) 0 hj (term g cc)).val j
        = restrictFun (Wop_le_self φ) ((Scheme.TwoAffineOpenCover.algebraOfHom (φ ≫ ProjSpace.π A N) (pullbackChart φ j)).algebraMap ((p g).coeff cc)
            * ∏ l, frameUnit φ j l ^ cc l) * restrictFun (Wop_le_self φ) (g : Γ(X, pullbackChart φ j)) := by
    intro g cc
    simp only [term, map_smul]
    rw [twistObj.algebraMap_smul, twistObj.smul_val, Psi_mk_val_self, PsiNum_monMulFrac, restrictFun_prod_uTop',
      PsiNum_genFrac, restrictFun_algebraMap' (φ ≫ ProjSpace.π A N), map_mul, restrictFun_algebraMap' (φ ≫ ProjSpace.π A N), mul_assoc]

  have hPsi : Psi φ (φ ≫ ProjSpace.π A N) 0 hj (ProjSpaceCech.GradedModule.sec.mk _ {j} X₀) = Psi φ (φ ≫ ProjSpace.π A N) 0 hj Y := by
    apply twistObj_eq_of_val_eq φ (φ ≫ ProjSpace.π A N) 0 (interI_le φ hj)
    rw [Psi_mk_val_self, hY, map_sum, twistObj_sum_val, hs0, hsum, map_sum, ← Finset.sum_attach (genSet φ j)]
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [map_sum, twistObj_sum_val, map_mul, fracFun_eq_sum, map_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun cc _ => ?_
    rw [hterm, map_mul]
  have hXY : ProjSpaceCech.GradedModule.sec.mk _ {j} X₀ = Y := Psi_injective φ (φ ≫ ProjSpace.π A N) 0 hj hPsi

  obtain ⟨b, hb, v, hv, hnum, hYeq⟩ := hY_good
  rw [hYeq] at hXY
  obtain ⟨c', hc', hrel⟩ := (ProjSpaceCech.GradedModule.sec_mk_eq _ {j}).mp hXY

  have hrel' : ProjSpaceCech.GradedModule.monMul ((twistGradedModule φ (φ ≫ ProjSpace.π A N)).shift ((0 : ℕ) : ℤ)) (c' + b) x
      = ProjSpaceCech.GradedModule.monMul ((twistGradedModule φ (φ ≫ ProjSpace.π A N)).shift ((0 : ℕ) : ℤ)) (c' + a)
          ((psi0 φ (φ ≫ ProjSpace.π A N)).toLinearMap v) := hrel
  set K : ℕ := (c' + b) j with hK
  have hcb : c' + b = Pi.single j K := eq_single_of_supp (c' + b) (ProjSpaceCech.GradedModule.Frac.supp_add {j} hc' hb)
  have hKsum : (K : ℤ) = (∑ l, (c' l : ℤ)) + ∑ l, (b l : ℤ) := by
    rw [← sum_cast_eq_of_supp (c' + b) (ProjSpaceCech.GradedModule.Frac.supp_add {j} hc' hb)]
    simp only [Pi.add_apply, Nat.cast_add, Finset.sum_add_distrib]
  refine ⟨K, (LinearMap.ker (psi0 φ (φ ≫ ProjSpace.π A N)).toLinearMap).mkQ (ProjSpaceCech.GradedModule.monMul (Fgen φ (φ ≫ ProjSpace.π A N)) (c' + a) v), ?_, ?_⟩
  · refine (mem_Mgen_grade_iff φ (φ ≫ ProjSpace.π A N) _ _).mpr (Submodule.mem_map_of_mem ?_)
    have h := ProjSpaceCech.GradedModule.monMul_mem_grade (Fgen φ (φ ≫ ProjSpace.π A N)) (c' + a) _ v hv
    convert h using 2
    simp only [Pi.add_apply, Nat.cast_add, Finset.sum_add_distrib, hasum, hKsum]
    ring
  · rw [psi_mkQ, (psi0 φ (φ ≫ ProjSpace.π A N)).map_monMul]
    refine hrel'.symm.trans ?_
    rw [monMul_shift_eq, hcb, ProjSpaceCech.GradedModule.monMul_single]
    rfl

end Sat2
p2m_reactivate "P2MW.S_AlgebraicGeometry_ProjSpace_exists_isFG_hom_injective_saturated_twistGradedModule.AlgebraicGeometry P2MW.S_AlgebraicGeometry_ProjSpace_exists_isFG_hom_injective_saturated_twistGradedModule.AlgebraicGeometry.ProjSpace P2MW.S_AlgebraicGeometry_ProjSpace_exists_isFG_hom_injective_saturated_twistGradedModule.AlgebraicGeometry.ProjSpace.GMSec"

end AlgebraicGeometry.ProjSpace.GMSec
p2m_reactivate "P2MW.S_AlgebraicGeometry_ProjSpace_exists_isFG_hom_injective_saturated_twistGradedModule.AlgebraicGeometry P2MW.S_AlgebraicGeometry_ProjSpace_exists_isFG_hom_injective_saturated_twistGradedModule.AlgebraicGeometry.ProjSpace P2MW.S_AlgebraicGeometry_ProjSpace_exists_isFG_hom_injective_saturated_twistGradedModule.AlgebraicGeometry.ProjSpace.GMSec"
p2m_reactivate "P2MW.S_AlgebraicGeometry_ProjSpace_exists_isFG_hom_injective_saturated_twistGradedModule.AlgebraicGeometry P2MW.S_AlgebraicGeometry_ProjSpace_exists_isFG_hom_injective_saturated_twistGradedModule.AlgebraicGeometry.ProjSpace P2MW.S_AlgebraicGeometry_ProjSpace_exists_isFG_hom_injective_saturated_twistGradedModule.AlgebraicGeometry.ProjSpace.GMSec"
p2m_reactivate "P2MW.S_AlgebraicGeometry_ProjSpace_exists_isFG_hom_injective_saturated_twistGradedModule.AlgebraicGeometry P2MW.S_AlgebraicGeometry_ProjSpace_exists_isFG_hom_injective_saturated_twistGradedModule.AlgebraicGeometry.ProjSpace P2MW.S_AlgebraicGeometry_ProjSpace_exists_isFG_hom_injective_saturated_twistGradedModule.AlgebraicGeometry.ProjSpace.GMSec"

end
p2m_reactivate "P2MW.S_AlgebraicGeometry_ProjSpace_exists_isFG_hom_injective_saturated_twistGradedModule.AlgebraicGeometry P2MW.S_AlgebraicGeometry_ProjSpace_exists_isFG_hom_injective_saturated_twistGradedModule.AlgebraicGeometry.ProjSpace P2MW.S_AlgebraicGeometry_ProjSpace_exists_isFG_hom_injective_saturated_twistGradedModule.AlgebraicGeometry.ProjSpace.GMSec"

namespace AlgebraicGeometry p2m_export "AlgebraicGeometry" "Spec.map_comp Scheme.mem_basicOpen Scheme.basicOpen_res Surjective Scheme.Hom Proj.basicOpenIsoAway IsFinite Scheme.preimage_basicOpen Spec Spec.map Proj.basicOpenToSpec Scheme Scheme.Hom.appTop Proj.mem_basicOpen Scheme.Opens.topIso_hom Scheme.Hom.comp_appTop Proj IsFinite.finite_app Proj.stalkIso' Proj.basicOpenIsoSpec_inv_ι Proj.isAffineOpen_basicOpen Proj.basicOpen Proj.basicOpen_mul Scheme.basicOpen_mul IsAffineOpen Scheme.Opens IsAffineHom Scheme.Opens.ι_appTop Proj.awayToSection Proj.basicOpenToSpec_app_top Proj.basicOpenIsoSpec_hom Scheme.basicOpen_le ProjectiveSpectrum.Proj.awayToSection_germ Scheme.ΓSpecIso_inv_naturality_assoc Scheme.ΓSpecIso ProjSpace.π ProjSpace.X_mem_one ProjSpace.awayι_comp_π ProjSpace.val_algebraMap ProjSpace.awayMk_monomial Scheme.TwoAffineOpenCover Scheme.TwoAffineOpenCover.algebraOfHom ProjSpace.twistGradedModule" namespace ProjSpace p2m_export "AlgebraicGeometry.ProjSpace" "π X_mem_one awayι_comp_π ratio val_algebraMap awayMk_monomial map pullbackChart frameUnit restrictFun TwistCompat restrictFun_restrictFun restrictFun_irrel restrictFun_refl restrictFun_algebraMap' twistObj twistObj.smul_val twistObj.algebraMap_smul twist pullbackOverlap pullbackOverlap_eq_inf frameUnit_cocycle frameUnit_self twistObj.add_val twistObj.zero_val twistFam twistGradedModule isAffineOpen_pullbackChart isAffineOpen_pullbackOverlap twistObj.ext" end AlgebraicGeometry.ProjSpace
p2m_open_scoped "AlgebraicGeometry AlgebraicGeometry.ProjSpace" in

theorem AlgebraicGeometry.ProjSpace.exists_isFG_hom_injective_saturated_twistGradedModule'
    {A : Type u} [CommRing A] {N : ℕ} {X : Scheme.{u}}
    (φ : X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) A)) [IsFinite φ]
    (π : X ⟶ Spec (.of A)) (hπ : φ ≫ ProjSpace.π A N = π) :
    ∃ (M' : ProjSpaceCech.GradedModule A N) (ψ : ProjSpaceCech.GradedModule.Hom M' (ProjSpace.twistGradedModule φ π)),
      M'.IsFG ∧ Function.Injective ψ.toLinearMap ∧
      ∀ (j : Fin (N + 1)) (e : ℤ), ∀ x ∈ (ProjSpace.twistGradedModule φ π).grade e,
        ∃ k : ℕ, ∃ x' ∈ M'.grade (e + k), ψ.toLinearMap x' = ((ProjSpace.twistGradedModule φ π).xMul j ^ k) x :=
  ⟨ProjSpace.GMSec.Mgen φ π, ProjSpace.GMSec.psi φ π, ProjSpace.GMSec.Mgen_isFG φ π, ProjSpace.GMSec.psi_injective φ π,
    fun j e x hx => ProjSpace.GMSec.psi_saturated φ π hπ j e x hx⟩

theorem solution
    {A : Type u} [CommRing A] {N : ℕ} {X : Scheme.{u}}
    (φ : X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) A)) [IsFinite φ]
    (π : X ⟶ Spec (.of A)) (hπ : φ ≫ ProjSpace.π A N = π) :
    ∃ (M' : ProjSpaceCech.GradedModule A N) (ψ : ProjSpaceCech.GradedModule.Hom M' (ProjSpace.twistGradedModule φ π)),
      M'.IsFG ∧ Function.Injective ψ.toLinearMap ∧
      ∀ (j : Fin (N + 1)) (e : ℤ), ∀ x ∈ (ProjSpace.twistGradedModule φ π).grade e,
        ∃ k : ℕ, ∃ x' ∈ M'.grade (e + k), ψ.toLinearMap x' = ((ProjSpace.twistGradedModule φ π).xMul j ^ k) x :=
  AlgebraicGeometry.ProjSpace.exists_isFG_hom_injective_saturated_twistGradedModule' φ π hπ

end
p2m_reactivate "P2MW.S_AlgebraicGeometry_ProjSpace_exists_isFG_hom_injective_saturated_twistGradedModule.AlgebraicGeometry P2MW.S_AlgebraicGeometry_ProjSpace_exists_isFG_hom_injective_saturated_twistGradedModule.AlgebraicGeometry.ProjSpace P2MW.S_AlgebraicGeometry_ProjSpace_exists_isFG_hom_injective_saturated_twistGradedModule.AlgebraicGeometry.ProjSpace.GMSec"

end S_AlgebraicGeometry_ProjSpace_exists_isFG_hom_injective_saturated_twistGradedModule
end P2MW
export P2MW.S_AlgebraicGeometry_ProjSpace_exists_isFG_hom_injective_saturated_twistGradedModule (solution)
