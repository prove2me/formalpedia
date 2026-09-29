-- Prove2me | solution 1 for AlgebraicGeometry.OModulePresheaf.Leray.isQuasicoherent_relHPresheaf_chow
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/ebc0ef56-e1a4-56f7-8fe6-7855e937a9be

import Mathlib
import Definitions.Def_AlgebraicGeometry_ProjSpaceCover
import Definitions.Def_AlgebraicGeometry_OModulePresheafLerayBicomplex
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_OModulePresheaf_Leray_isQuasicoherent_relHPresheaf_chow

set_option autoImplicit false
set_option maxHeartbeats 6400000
set_option synthInstance.maxHeartbeats 1600000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

noncomputable section

universe u

p2m_open "CategoryTheory AlgebraicGeometry P2MW.S_AlgebraicGeometry_OModulePresheaf_Leray_isQuasicoherent_relHPresheaf_chow.AlgebraicGeometry TopologicalSpace Opposite CategoryTheory.Limits"

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Spec.map_comp Scheme.Hom.map_appLE IsLocallyNoetherian Scheme.basicOpen_res IsProper LocallyOfFiniteType.isLocallyNoetherian Scheme.Hom IsAffineOpen.fromSpec_top QuasiCompact Scheme.preimage_basicOpen IsAffineOpen.SpecMap_appLE_fromSpec LocallyOfFiniteType Spec Spec.map Scheme QuasiCompact.compactSpace_of_compactSpace Scheme.isoSpec_Spec_inv IsClosedImmersion IsSeparated isAffineOpen_top IsAffineOpen IsNoetherian Scheme.Hom.appLE_map Scheme.ΓSpecIso ProjSpace.stdCoverPullback ChowDatumProj Scheme.OrderedAffineCover OModulePresheaf Scheme.TwoAffineOpenCover Scheme.TwoAffineOpenCover.algebraOfHom Scheme.OrderedAffineCover.fiberAffineOpen OModulePresheaf.Leray.relHPresheaf Scheme.OrderedAffineCoverOf Scheme.OrderedAffineCoverOf.moduleSections"
namespace OModulePresheaf
p2m_export "AlgebraicGeometry.OModulePresheaf" "d IsQuasicoherent res res_smul mk obj moduleSections Leray.relHPresheaf Hom"
namespace Leray
p2m_export "AlgebraicGeometry.OModulePresheaf.Leray" "relAltC relAltd relAltHB relAltH pullOpen relAltC_modΓ relAltd_Γsmul relRes relRes_comm relResKer relHPresheaf"
p2m_open "AlgebraicGeometry.OModulePresheaf.Leray AlgebraicGeometry.OModulePresheaf AlgebraicGeometry"

attribute [local instance] MvPolynomial.gradedAlgebra

section Local

variable {R : Type u} [CommRing R]

theorem res_res' {V : Scheme.{u}} {O₁ O₂ O₃ : V.Opens} (h12 : O₁ ≤ O₂) (h23 : O₂ ≤ O₃) (x : Γ(V, O₃)) :
    (V.presheaf.map (homOfLE h12).op).hom ((V.presheaf.map (homOfLE h23).op).hom x)
      = (V.presheaf.map (homOfLE (h12.trans h23)).op).hom x := by
  rw [← CommRingCat.comp_apply, ← V.presheaf.map_comp]; rfl

theorem res_refl' {V : Scheme.{u}} {O : V.Opens} (h : O ≤ O) (x : Γ(V, O)) :
    (V.presheaf.map (homOfLE h).op).hom x = x := by
  have : (homOfLE h : O ⟶ O) = 𝟙 O := rfl
  rw [this, op_id, V.presheaf.map_id]; rfl

theorem algebraOfHom_compat {V : Scheme.{u}} (π : V ⟶ Spec (CommRingCat.of R)) (W : V.Opens) :
    ∀ c, letI := Scheme.TwoAffineOpenCover.algebraOfHom π W
      algebraMap R Γ(V, W) c = (V.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op).hom
        (π.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom c)) :=
  fun _ => rfl

theorem specMap_algebraMap_eq_fromSpec_comp {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
    {U : X.Opens} (hU : IsAffineOpen U) :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom f U
    Spec.map (CommRingCat.ofHom (algebraMap R Γ(X, U))) = hU.fromSpec ≫ f := by
  letI := Scheme.TwoAffineOpenCover.algebraOfHom f U
  have halg : CommRingCat.ofHom (algebraMap R Γ(X, U))
      = (Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ f.appLE ⊤ U (le_top : U ≤ f ⁻¹ᵁ ⊤) := rfl
  rw [halg, Spec.map_comp, ← Scheme.isoSpec_Spec_inv, ← IsAffineOpen.fromSpec_top,
    IsAffineOpen.SpecMap_appLE_fromSpec f (isAffineOpen_top (Spec (CommRingCat.of R))) hU
      (le_top : U ≤ f ⁻¹ᵁ ⊤)]

theorem isNoeth_of_proper [IsNoetherianRing R] {V : Scheme.{u}}
    (π : V ⟶ Spec (CommRingCat.of R)) [IsProper π] : IsNoetherian V := by
  haveI : LocallyOfFiniteType π := inferInstance
  haveI : IsLocallyNoetherian (Spec (CommRingCat.of R)) := inferInstance
  haveI : IsLocallyNoetherian V := LocallyOfFiniteType.isLocallyNoetherian π
  haveI : CompactSpace V := QuasiCompact.compactSpace_of_compactSpace π
  exact {}

end Local

section RelHPresheafChow

variable {R : Type u} [CommRing R] {Z : Scheme.{u}}
variable (πZ : Z ⟶ Spec (CommRingCat.of R)) (D : ChowDatumProj πZ)

theorem isQuasicoherent_relHPresheaf_chow' [IsSeparated πZ] (b : ℕ) :
    (relHPresheaf D.p πZ (ProjSpace.stdCoverPullback D.ιN) b).IsQuasicoherent := by
  haveI : IsClosedImmersion D.ιN := D.hιN_closed
  haveI : IsSeparated (D.p ≫ πZ) := inferInstance
  set K' := ProjSpace.stdCoverPullback D.ιN
  letI : ∀ O : D.V'.Opens, Module R Γ(D.V', O) := Scheme.OrderedAffineCoverOf.moduleSections (D.p ≫ πZ)
  intro U f

  set g : ∀ {q} (τ : K'.Idx q),
      Γ(D.V', K'.inter τ ⊓ (Opens.map D.p.base).obj U.1) := fun τ =>
    (D.p.appLE U.1 (K'.inter τ ⊓ (Opens.map D.p.base).obj U.1) inf_le_right).hom f
  have hbo : ∀ {q} (τ : K'.Idx q),
      D.V'.basicOpen (g τ) = K'.inter τ
        ⊓ (Opens.map D.p.base).obj (Z.basicOpen f) := fun τ => by
    rw [show g τ = (D.V'.presheaf.map (homOfLE inf_le_right).op).hom ((D.p.app U.1).hom f) from rfl,
      Scheme.basicOpen_res, ← Scheme.preimage_basicOpen,
      inf_assoc, inf_eq_right.mpr ((Opens.map D.p.base).monotone (Z.basicOpen_le f))]
  have haff : ∀ {q} (τ : K'.Idx q),
      IsAffineOpen (K'.inter τ ⊓ (Opens.map D.p.base).obj U.1) := fun τ =>
    Scheme.OrderedAffineCover.fiberAffineOpen D.p πZ (K'.isAffineOpen_inter (D.p ≫ πZ) τ) U.2

  let resC : ∀ q, relAltC D.p πZ K' U.1 q
      →ₗ[R] relAltC D.p πZ K' (Z.basicOpen f) q := fun q =>
    relRes D.p πZ K' (Z.basicOpen_le f) q
  have hres_d : ∀ q, resC (q + 1) ∘ₗ relAltd D.p πZ K' U.1 q
      = relAltd D.p πZ K' (Z.basicOpen f) q ∘ₗ resC q := fun q =>
    relRes_comm D.p πZ K' (Z.basicOpen_le f) q
  have hres_smul : ∀ q (a : Γ(Z, U.1)) (y : relAltC D.p πZ K' U.1 q),
      resC q (a • y) = (Z.presheaf.map (homOfLE (Z.basicOpen_le f)).op).hom a • resC q y :=
    fun q a y => funext fun τ =>
      (pullOpen D.p πZ (K'.inter τ)).res_smul
        (Z.basicOpen_le f) a (y τ)

  have hCsurj : ∀ q (x : relAltC D.p πZ K' (Z.basicOpen f) q),
      ∃ (N : ℕ) (y : relAltC D.p πZ K' U.1 q),
        resC q y = (Z.presheaf.map (homOfLE (Z.basicOpen_le f)).op).hom (f ^ N) • x := by
    intro q x

    have hex : ∀ (τ : K'.Idx q)
        (x' : Γ(D.V', K'.inter τ ⊓ (Opens.map D.p.base).obj (Z.basicOpen f))),
        ∃ (n : ℕ) (a : Γ(D.V', K'.inter τ ⊓ (Opens.map D.p.base).obj U.1)),
        (D.V'.presheaf.map (homOfLE (inf_le_inf_left _
            ((Opens.map D.p.base).monotone (Z.basicOpen_le f)))).op).hom a
          = (D.V'.presheaf.map (homOfLE (inf_le_inf_left _
              ((Opens.map D.p.base).monotone (Z.basicOpen_le f)))).op).hom (g τ) ^ n * x' :=
      fun τ x' => by
      haveI := (haff τ).isLocalization_basicOpen (g τ)
      obtain ⟨⟨a, _, n, rfl⟩, ha⟩ :=
        IsLocalization.surj (S := Γ(D.V', D.V'.basicOpen (g τ))) (.powers (g τ))
          ((D.V'.presheaf.map (homOfLE (hbo τ).le).op).hom x')
      have ha' : (D.V'.presheaf.map (homOfLE (D.V'.basicOpen_le (g τ))).op).hom a
          = (D.V'.presheaf.map (homOfLE (hbo τ).le).op).hom x'
            * (D.V'.presheaf.map (homOfLE (D.V'.basicOpen_le (g τ))).op).hom (g τ ^ n) := ha.symm
      refine ⟨n, a, ?_⟩
      rw [← res_res' (hbo τ).ge (D.V'.basicOpen_le (g τ)),
        ← res_res' (hbo τ).ge (D.V'.basicOpen_le (g τ)), ha',
        map_mul, res_res', res_refl', map_pow, map_pow,
        res_res', mul_comm]
    choose n a ha using fun τ => hex τ (x τ)
    refine ⟨Finset.univ.sup n, fun τ => g τ ^ (Finset.univ.sup n - n τ) * a τ, funext fun τ => ?_⟩

    have hcore : ∀ (x' : Γ(D.V', K'.inter τ
        ⊓ (Opens.map D.p.base).obj (Z.basicOpen f))),
        (D.V'.presheaf.map (homOfLE (inf_le_inf_left _
            ((Opens.map D.p.base).monotone (Z.basicOpen_le f)))).op).hom
            (g τ ^ (Finset.univ.sup n - n τ) * a τ)
          = (D.V'.presheaf.map (homOfLE (inf_le_inf_left _
              ((Opens.map D.p.base).monotone (Z.basicOpen_le f)))).op).hom
              (g τ) ^ Finset.univ.sup n * x'
          → (D.V'.presheaf.map (homOfLE (inf_le_inf_left _
              ((Opens.map D.p.base).monotone (Z.basicOpen_le f)))).op).hom
              (g τ ^ (Finset.univ.sup n - n τ) * a τ)
            = (D.p.appLE (Z.basicOpen f) (K'.inter τ
                  ⊓ (Opens.map D.p.base).obj (Z.basicOpen f)) inf_le_right).hom
                ((Z.presheaf.map (homOfLE (Z.basicOpen_le f)).op).hom (f ^ Finset.univ.sup n))
              * x' := fun x' hx' => hx'.trans (congrArg (· * x') (by
      rw [← CommRingCat.comp_apply, Scheme.Hom.map_appLE, ← Scheme.Hom.appLE_map _ inf_le_right
          (homOfLE (inf_le_inf_left _ ((Opens.map D.p.base).monotone (Z.basicOpen_le f)))).op,
        CommRingCat.comp_apply, map_pow, map_pow])).symm
    exact hcore (x τ) (by
      rw [map_mul, map_pow, ha, ← mul_assoc, ← pow_add,
        Nat.sub_add_cancel (Finset.le_sup (Finset.mem_univ τ))])

  have hCann : ∀ q (y : relAltC D.p πZ K' U.1 q), resC q y = 0 →
      ∃ M : ℕ, (f ^ M : Γ(Z, U.1)) • y = 0 := by
    intro q y hy

    have hex : ∀ (τ : K'.Idx q)
        (y' : Γ(D.V', K'.inter τ ⊓ (Opens.map D.p.base).obj U.1)),
        (D.V'.presheaf.map (homOfLE (inf_le_inf_left _
            ((Opens.map D.p.base).monotone (Z.basicOpen_le f)))).op).hom y' = 0 →
        ∃ m, g τ ^ m * y' = 0 := fun τ y' hy' => by
      haveI := (haff τ).isLocalization_basicOpen (g τ)
      obtain ⟨⟨_, m, rfl⟩, hm⟩ :=
        (IsLocalization.map_eq_zero_iff (S := Γ(D.V', D.V'.basicOpen (g τ)))
          (.powers (g τ)) y').mp (by
          rw [show algebraMap _ _ y'
            = (D.V'.presheaf.map (homOfLE (D.V'.basicOpen_le (g τ))).op).hom y' from rfl,
            ← res_res' (hbo τ).le (inf_le_inf_left _
              ((Opens.map D.p.base).monotone (Z.basicOpen_le f))), hy', map_zero])
      exact ⟨m, hm⟩
    choose m hm using fun τ => hex τ (y τ) (congrFun hy τ)
    refine ⟨Finset.univ.sup m, funext fun τ => ?_⟩
    have hcore : ∀ (y' : Γ(D.V', K'.inter τ ⊓ (Opens.map D.p.base).obj U.1)),
        g τ ^ m τ * y' = 0 →
        (D.p.appLE U.1 _ inf_le_right).hom (f ^ Finset.univ.sup m) * y' = 0 := fun y' hy0 => by
      rw [map_pow, ← Nat.sub_add_cancel (Finset.le_sup (Finset.mem_univ τ)), pow_add,
        mul_assoc, hy0, mul_zero]
    exact hcore (y τ) (hm τ)

  refine ⟨fun x => x.inductionOn' fun x₀ => ?_, fun y => y.inductionOn' fun y₀ hy => ?_⟩
  ·
    obtain ⟨N, y, hyN⟩ := hCsurj b x₀.1
    obtain ⟨M, hM⟩ := hCann (b + 1) (relAltd D.p πZ K' U.1 b y) (by
      rw [← LinearMap.comp_apply, hres_d, LinearMap.comp_apply, hyN,
        relAltd_Γsmul, LinearMap.mem_ker.mp x₀.2, smul_zero])
    refine ⟨M + N, Submodule.Quotient.mk ⟨(f ^ M : Γ(Z, U.1)) • y, LinearMap.mem_ker.mpr
      ((relAltd_Γsmul D.p πZ K' U.1 b _ y).trans hM)⟩,
      congrArg Submodule.Quotient.mk (Subtype.ext
        (show resC b ((f ^ M : Γ(Z, U.1)) • y) = _ from ?_))⟩
    simp only [hres_smul, hyN, map_pow, smul_smul, ← pow_add]; rfl
  ·
    have hyB : (relResKer D.p πZ K' (Z.basicOpen_le f) b y₀)
        ∈ relAltHB D.p πZ K' (Z.basicOpen f) b :=
      (Submodule.Quotient.mk_eq_zero _).mp hy
    rcases b with _ | b'
    · obtain ⟨M, hM⟩ := hCann 0 y₀.1 (congrArg Subtype.val ((Submodule.mem_bot R).mp hyB))
      exact ⟨M, (Submodule.Quotient.mk_eq_zero _).mpr
        ((Submodule.mem_bot R).mpr (Subtype.ext hM))⟩
    · obtain ⟨w, hw⟩ := hyB
      obtain ⟨N, w', hw'⟩ := hCsurj b' w
      obtain ⟨M, hM⟩ := hCann (b' + 1)
        ((f ^ N : Γ(Z, U.1)) • y₀.1 - relAltd D.p πZ K' U.1 b' w') (by
        rw [map_sub, hres_smul, ← LinearMap.comp_apply, hres_d, LinearMap.comp_apply, hw',
          relAltd_Γsmul,
          show resC (b' + 1) y₀.1
            = relAltd D.p πZ K' (Z.basicOpen f) b' w from hw.symm,
          sub_self])
      refine ⟨M + N, (Submodule.Quotient.mk_eq_zero _).mpr ⟨(f ^ M : Γ(Z, U.1)) • w', ?_⟩⟩
      refine (eq_comm.mpr (sub_eq_zero.mp ?_) :
        relAltd D.p πZ K' U.1 b' ((f ^ M : Γ(Z, U.1)) • w')
          = (f ^ (M + N) : Γ(Z, U.1)) • y₀.1)
      rw [relAltd_Γsmul D.p πZ K' U.1 b' _ w', pow_add, mul_smul, ← smul_sub]
      exact hM

end RelHPresheafChow

end AlgebraicGeometry.OModulePresheaf.Leray

attribute [local instance] MvPolynomial.gradedAlgebra in
theorem solution {R : Type u} [CommRing R]
    {Z : Scheme.{u}} (πZ : Z ⟶ Spec (.of R)) [IsSeparated πZ] (D : ChowDatumProj πZ) (b : ℕ) :
    (OModulePresheaf.Leray.relHPresheaf D.p πZ (ProjSpace.stdCoverPullback D.ιN) b).IsQuasicoherent :=
  AlgebraicGeometry.OModulePresheaf.Leray.isQuasicoherent_relHPresheaf_chow' πZ D b

end

end S_AlgebraicGeometry_OModulePresheaf_Leray_isQuasicoherent_relHPresheaf_chow
end P2MW
export P2MW.S_AlgebraicGeometry_OModulePresheaf_Leray_isQuasicoherent_relHPresheaf_chow (solution)
