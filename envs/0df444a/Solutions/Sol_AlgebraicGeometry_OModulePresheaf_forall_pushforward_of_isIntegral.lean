-- Prove2me | solution 1 for AlgebraicGeometry.OModulePresheaf.forall_pushforward_of_isIntegral
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/f95b5ee8-f6d1-5d01-b036-286368f5a06b

import Mathlib
import Definitions.Def_AlgebraicGeometry_OModulePresheafConstructions
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_basicOpen_sections_free_of_isIntegral
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_OModulePresheaf_forall_pushforward_of_isIntegral

set_option autoImplicit false

universe u

p2m_open "CategoryTheory AlgebraicGeometry P2MW.S_AlgebraicGeometry_OModulePresheaf_forall_pushforward_of_isIntegral.AlgebraicGeometry TopologicalSpace Opposite"

noncomputable section

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Scheme.Hom.map_appLE IsLocallyNoetherian Scheme.basicOpen_res IsProper Scheme.IdealSheafData.coe_support_vanishingIdeal LocallyOfFiniteType.isLocallyNoetherian Scheme.Hom QuasiCompact Scheme.preimage_basicOpen LocallyOfFiniteType Spec IsIntegral Scheme.IdealSheafData.range_subschemeι Scheme Scheme.IdealSheafData.vanishingIdeal QuasiCompact.compactSpace_of_compactSpace IsClosedImmersion IsSeparated IsLocallyNoetherian.component_noetherian IsAffineOpen IsNoetherian Scheme.IdealSheafData Scheme.Hom.appLE_eq_app OModulePresheaf.ker OModulePresheaf.im OModulePresheaf.coker OModulePresheaf.kerImSES OModulePresheaf.imCokerSES OModulePresheaf.pushforward OModulePresheaf.pushforwardUnit Scheme.OrderedAffineCover.isAffineOpen_inf_of_isSeparated OModulePresheaf.Hom OModulePresheaf.AffSES Scheme.OrderedAffineCover OModulePresheaf OModulePresheaf.unit Scheme.TwoAffineOpenCover Scheme.TwoAffineOpenCover.algebraOfHom OModulePresheaf.exists_basicOpen_sections_free_of_isIntegral"
namespace OModulePresheaf
p2m_export "AlgebraicGeometry.OModulePresheaf" "prod fstHom sndHom pow zero restrOpen ker im coker kerImSES imCokerSES pushforward pushforwardUnit Hom AffSES res_refl_apply res_res CechFinite IsCoherent IsQuasicoherent SupportedIn unit res res_smul res_refl isScalarTower mk obj res_comp exists_basicOpen_sections_free_of_isIntegral"
namespace PivotQAux
p2m_open "AlgebraicGeometry.OModulePresheaf AlgebraicGeometry"

variable {R : Type u} [CommRing R] {V : Scheme.{u}} {π : V ⟶ Spec (.of R)}

theorem support_vanishingIdeal' (Z : Closeds V) :
    (Scheme.IdealSheafData.vanishingIdeal Z).support = Z :=
  SetLike.coe_injective (Scheme.IdealSheafData.coe_support_vanishingIdeal Z)

theorem isNoetherian_of_isProper [IsNoetherianRing R] (π : V ⟶ Spec (.of R)) [IsProper π] :
    IsNoetherian V := by
  haveI : LocallyOfFiniteType π := inferInstance
  haveI : IsLocallyNoetherian (Spec (CommRingCat.of R)) := inferInstance
  haveI : IsLocallyNoetherian V := LocallyOfFiniteType.isLocallyNoetherian π
  haveI : CompactSpace V := QuasiCompact.compactSpace_of_compactSpace π
  exact {}

section KerImCoker

variable {F G : OModulePresheaf π} (φ : Hom F G)

theorem isCoherent_ker [IsLocallyNoetherian V] (hF : F.IsCoherent) : (ker φ).IsCoherent := fun U => by
  haveI := hF U
  haveI : IsNoetherianRing Γ(V, U.1) := IsLocallyNoetherian.component_noetherian U
  haveI : _root_.IsNoetherian Γ(V, U.1) (F.obj U.1) := isNoetherian_of_isNoetherianRing_of_finite _ _
  exact Module.Finite.of_injective ((kerImSES φ).inc.appSections U.1) ((kerImSES φ).injective U.1)

theorem isCoherent_im (hF : F.IsCoherent) : (im φ).IsCoherent := fun U => by
  haveI := hF U
  exact Module.Finite.of_surjective ((kerImSES φ).proj.appSections U.1) ((kerImSES φ).surjective U.1)

theorem isCoherent_coker (hG : G.IsCoherent) : (coker φ).IsCoherent := fun U => by
  haveI := hG U
  exact Module.Finite.of_surjective ((imCokerSES φ).proj.appSections U.1) ((imCokerSES φ).surjective U.1)

theorem isQuasicoherent_coker (hG : G.IsQuasicoherent) (hF : F.IsQuasicoherent) :
    (coker φ).IsQuasicoherent := fun U f => by
  refine ⟨fun x => x.inductionOn' fun x₀ => ?_, fun y => y.inductionOn' fun y₀ hy => ?_⟩
  · obtain ⟨n, y, hy⟩ := (hG U f).1 x₀
    exact ⟨n, Submodule.Quotient.mk y, congrArg Submodule.Quotient.mk hy⟩
  · obtain ⟨z, hz⟩ := (Submodule.Quotient.mk_eq_zero _).mp hy
    obtain ⟨n, w, hw⟩ := (hF U f).1 z
    have h1 : G.res (V.basicOpen_le f) ((f ^ n : Γ(V, U.1)) • y₀ - φ.app U.1 w) = 0 := by
      rw [map_sub, G.res_smul, ← hz, ← φ.app_smul, ← hw]
      exact sub_eq_zero.mpr (φ.naturality_apply (V.basicOpen_le f) w)
    obtain ⟨m, hm⟩ := (hG U f).2 _ h1
    rw [smul_sub, sub_eq_zero, smul_smul, ← pow_add] at hm
    exact ⟨m + n, (Submodule.Quotient.mk_eq_zero _).mpr
      ⟨(f ^ m : Γ(V, U.1)) • w, (φ.app_smul U.1 _ _).trans hm.symm⟩⟩

theorem isQuasicoherent_ker (hF : F.IsQuasicoherent) (hG : G.IsQuasicoherent) :
    (ker φ).IsQuasicoherent := fun U f => by
  refine ⟨fun x => ?_, fun y hy => ?_⟩
  · obtain ⟨n, y', hy'⟩ := (hF U f).1 x.1
    have h1 : G.res (V.basicOpen_le f) (φ.app U.1 y') = 0 := by
      have hnat := φ.naturality_apply (V.basicOpen_le f) y'
      rw [hy', φ.app_smul, LinearMap.mem_ker.mp x.2, smul_zero] at hnat
      exact hnat.symm
    obtain ⟨m, hm⟩ := (hG U f).2 _ h1
    refine ⟨m + n, ⟨(f ^ m : Γ(V, U.1)) • y',
      LinearMap.mem_ker.mpr ((φ.app_smul U.1 _ _).trans hm)⟩, Subtype.ext ?_⟩
    show F.res (V.basicOpen_le f) ((f ^ m : Γ(V, U.1)) • y')
      = (V.presheaf.map (homOfLE (V.basicOpen_le f)).op).hom (f ^ (m + n)) • x.1
    rw [F.res_smul, hy', smul_smul, ← map_mul, ← pow_add]
  · exact ((hF U f).2 y.1 (congrArg Subtype.val hy)).imp fun n hn => Subtype.ext hn

theorem isQuasicoherent_im (hF : F.IsQuasicoherent) (hG : G.IsQuasicoherent) :
    (im φ).IsQuasicoherent := fun U f => by
  refine ⟨fun x => ?_, fun y hy => ?_⟩
  · obtain ⟨s, hs⟩ := x.2
    obtain ⟨n, y', hy'⟩ := (hF U f).1 s
    refine ⟨n, ⟨φ.app U.1 y', y', rfl⟩, Subtype.ext ?_⟩
    show G.res (V.basicOpen_le f) (φ.app U.1 y')
      = (V.presheaf.map (homOfLE (V.basicOpen_le f)).op).hom (f ^ n) • x.1
    rw [← φ.naturality_apply, hy', φ.app_smul, hs]
  · exact ((hG U f).2 y.1 (congrArg Subtype.val hy)).imp fun n hn => Subtype.ext hn

end KerImCoker

theorem isCoherent_prod {F G : OModulePresheaf π} (hF : F.IsCoherent) (hG : G.IsCoherent) :
    (F.prod G).IsCoherent :=
  fun U => by haveI := hF U; haveI := hG U; exact Module.Finite.prod

theorem isQuasicoherent_prod {F G : OModulePresheaf π} (hF : F.IsQuasicoherent) (hG : G.IsQuasicoherent) :
    (F.prod G).IsQuasicoherent := fun U f => by
  refine ⟨fun x => ?_, fun y hy => ?_⟩
  · obtain ⟨n₁, y₁, hy₁⟩ := (hF U f).1 x.1; obtain ⟨n₂, y₂, hy₂⟩ := (hG U f).1 x.2
    exact ⟨n₁ + n₂, ((f ^ n₂ : Γ(V, U.1)) • y₁, (f ^ n₁ : Γ(V, U.1)) • y₂), Prod.ext
      (show F.res _ ((f ^ n₂ : Γ(V, U.1)) • y₁) = _ • x.1 by
        rw [F.res_smul, hy₁, smul_smul, ← map_mul, ← pow_add, Nat.add_comm])
      (show G.res _ ((f ^ n₁ : Γ(V, U.1)) • y₂) = _ • x.2 by
        rw [G.res_smul, hy₂, smul_smul, ← map_mul, ← pow_add])⟩
  · obtain ⟨n₁, hn₁⟩ := (hF U f).2 y.1 (congrArg Prod.fst hy)
    obtain ⟨n₂, hn₂⟩ := (hG U f).2 y.2 (congrArg Prod.snd hy)
    exact ⟨n₁ + n₂, Prod.ext
      (show (f ^ (n₁ + n₂) : Γ(V, U.1)) • y.1 = 0 by
        rw [Nat.add_comm, pow_add, mul_smul, hn₁, smul_zero])
      (show (f ^ (n₁ + n₂) : Γ(V, U.1)) • y.2 = 0 by
        rw [pow_add, mul_smul, hn₂, smul_zero])⟩

theorem isCoherent_pow {F : OModulePresheaf π} (n : ℕ) (hF : F.IsCoherent) : (F.pow n).IsCoherent :=
  fun U => by haveI := hF U; exact Module.Finite.pi

theorem isQuasicoherent_pow {F : OModulePresheaf π} (n : ℕ) (hF : F.IsQuasicoherent) :
    (F.pow n).IsQuasicoherent := fun U f => by
  refine ⟨fun x => ?_, fun y hy => ?_⟩
  · choose m y' hy' using fun i => (hF U f).1 (x i)
    refine ⟨∑ i, m i, fun i => (f ^ ((∑ j, m j) - m i) : Γ(V, U.1)) • y' i, funext fun i => ?_⟩
    show F.res _ ((f ^ ((∑ j, m j) - m i) : Γ(V, U.1)) • y' i)
      = (V.presheaf.map (homOfLE (V.basicOpen_le f)).op).hom (f ^ ∑ j, m j) • x i
    rw [F.res_smul, hy' i, smul_smul, ← map_mul, ← pow_add,
      Nat.sub_add_cancel (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i))]
  · choose m hm using fun i => (hF U f).2 (y i) (congrFun hy i)
    refine ⟨∑ i, m i, funext fun i => show (f ^ ∑ j, m j : Γ(V, U.1)) • y i = 0 from ?_⟩
    rw [show (∑ j, m j) = ((∑ j, m j) - m i) + m i from (Nat.sub_add_cancel
        (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i))).symm,
      pow_add, mul_smul, hm i, smul_zero]

theorem isQuasicoherent_restrOpen {F : OModulePresheaf π} (W₀ : V.Opens)
    (haff : ∀ U : V.affineOpens, IsAffineOpen (U.1 ⊓ W₀)) (hF : F.IsQuasicoherent) :
    (F.restrOpen W₀).IsQuasicoherent := fun U f => by
  have hbo : V.basicOpen ((V.presheaf.map (homOfLE (inf_le_left : U.1 ⊓ W₀ ≤ U.1)).op).hom f)
      = V.basicOpen f ⊓ W₀ := by
    rw [Scheme.basicOpen_res, inf_right_comm, inf_eq_right.mpr (V.basicOpen_le f)]
  obtain ⟨hs, ha⟩ := hF ⟨U.1 ⊓ W₀, haff U⟩
    ((V.presheaf.map (homOfLE (inf_le_left : U.1 ⊓ W₀ ≤ U.1)).op).hom f)
  refine ⟨fun x => ?_, fun y hy => ?_⟩
  · let x₀ : F.obj (V.basicOpen f ⊓ W₀) := x
    obtain ⟨n, y, hy⟩ := hs (F.res hbo.le x₀)
    refine ⟨n, y, show F.res (inf_le_inf_right W₀ (V.basicOpen_le f)) y
      = (V.presheaf.map (homOfLE (inf_le_left : V.basicOpen f ⊓ W₀ ≤ V.basicOpen f)).op).hom
          ((V.presheaf.map (homOfLE (V.basicOpen_le f)).op).hom (f ^ n)) • x₀ from ?_⟩
    have key := congrArg (F.res hbo.ge) hy
    rw [F.res_res, F.res_smul, F.res_res, F.res_refl_apply] at key
    refine key.trans (congrArg (· • x₀) ?_)
    simp only [map_pow, ← CommRingCat.comp_apply, ← V.presheaf.map_comp, ← op_comp, homOfLE_comp]
  · let y₀ : F.obj (U.1 ⊓ W₀) := y
    refine (ha y₀ ?_).imp fun n hn => ?_
    · exact (F.res_res hbo.le (inf_le_inf_right W₀ (V.basicOpen_le f)) y₀).symm.trans
        ((congrArg (F.res hbo.le) (show F.res _ y = 0 from hy)).trans (map_zero _))
    · show (V.presheaf.map (homOfLE (inf_le_left : U.1 ⊓ W₀ ≤ U.1)).op).hom (f ^ n) • y₀ = 0
      rw [map_pow]; exact hn

section PushUnit

variable {Z : Scheme.{u}} (i : Z ⟶ V) [IsClosedImmersion i]

theorem isCoherent_pushforwardUnit : (pushforwardUnit π i).IsCoherent := fun U => by
  show @Module.Finite Γ(V, U.1) Γ(Z, i ⁻¹ᵁ U.1) _ _
    (Module.compHom _ (i.appLE U.1 (i ⁻¹ᵁ U.1) le_rfl).hom)
  letI : Algebra Γ(V, U.1) Γ(Z, i ⁻¹ᵁ U.1) := (i.appLE U.1 (i ⁻¹ᵁ U.1) le_rfl).hom.toAlgebra
  exact Module.Finite.of_surjective (Algebra.linearMap _ _) fun x =>
    (i.app_surjective U.1 U.2 x).imp fun a ha =>
      show (i.appLE U.1 _ le_rfl).hom a = x by rw [Scheme.Hom.appLE_eq_app]; exact ha

theorem isQuasicoherent_unit (π : V ⟶ Spec (.of R)) : (unit π).IsQuasicoherent := by
  intro U f
  haveI := U.2.isLocalization_basicOpen f
  refine ⟨fun x₀ => ?_, fun y hy => ?_⟩
  · let x : Γ(V, V.basicOpen f) := x₀
    obtain ⟨⟨y, _, n, rfl⟩, hxy⟩ :=
      IsLocalization.surj (S := Γ(V, V.basicOpen f)) (.powers f) x
    exact ⟨n, y, hxy.symm.trans (mul_comm x _)⟩
  · obtain ⟨⟨_, n, rfl⟩, hc⟩ :=
      (IsLocalization.map_eq_zero_iff (S := Γ(V, V.basicOpen f)) (.powers f) y).mp hy
    exact ⟨n, hc⟩

theorem isQuasicoherent_pushforwardUnit : (pushforwardUnit π i).IsQuasicoherent := fun U f => by
  let S := unit (i ≫ π)
  set g : Γ(Z, i ⁻¹ᵁ U.1) := (i.app U.1).hom f with hg_def
  have hbo : i ⁻¹ᵁ V.basicOpen f = Z.basicOpen g := Scheme.preimage_basicOpen i f
  obtain ⟨hs, ha⟩ := isQuasicoherent_unit (i ≫ π) ⟨i ⁻¹ᵁ U.1, U.2.preimage i⟩ g
  have hpow : ∀ n (y : Γ(Z, i ⁻¹ᵁ U.1)),
      (f ^ n : Γ(V, U.1)) • (show (pushforwardUnit π i).obj U.1 from y) = g ^ n * y := fun n y => by
    show (i.appLE U.1 (i ⁻¹ᵁ U.1) le_rfl).hom (f ^ n) * y = _
    rw [map_pow, Scheme.Hom.appLE_eq_app]
  refine ⟨fun x => ?_, fun y hy => ?_⟩
  · let x₀ : Γ(Z, i ⁻¹ᵁ V.basicOpen f) := x
    obtain ⟨n, y, hny⟩ := hs (S.res hbo.ge x₀)
    refine ⟨n, y, ?_⟩
    have key := congrArg (S.res hbo.le) hny
    rw [S.res_res, S.res_smul, S.res_res, S.res_refl_apply] at key
    show S.res ((Opens.map i.base).monotone (V.basicOpen_le f)) y
      = (i.appLE (V.basicOpen f) (i ⁻¹ᵁ V.basicOpen f) le_rfl).hom
          ((V.presheaf.map (homOfLE (V.basicOpen_le f)).op).hom (f ^ n)) * x₀
    refine key.trans ?_
    congr 1
    rw [← CommRingCat.comp_apply (f := V.presheaf.map _), Scheme.Hom.map_appLE,
      ← CommRingCat.comp_apply, ← Functor.map_comp, ← op_comp, homOfLE_comp, map_pow,
      map_pow]
    congr 1
  · refine (ha y ?_).imp fun n hn => (hpow n y).trans hn
    refine (S.res_res hbo.ge ((Opens.map i.base).monotone (V.basicOpen_le f)) y).symm.trans ?_
    exact (congrArg (S.res hbo.ge)
      (show S.res ((Opens.map i.base).monotone (V.basicOpen_le f)) y = 0 from hy)).trans
        (map_zero _)

end PushUnit

def affSESPowSucc (F : OModulePresheaf π) (m : ℕ) : AffSES (F.pow m) (F.pow (m + 1)) F := by
  let ιapp : ∀ U : V.affineOpens, (F.pow m).obj U.1 →ₗ[R] (F.pow (m + 1)).obj U.1 :=
    fun U => LinearMap.pi fun k =>
      Fin.lastCases (0 : (Fin m → F.obj U.1) →ₗ[R] F.obj U.1) (fun j => LinearMap.proj j) k
  have hlast : ∀ (U : V.affineOpens) (g : (F.pow m).obj U.1), ιapp U g (Fin.last m) = 0 := by
    intro U g
    change (Fin.lastCases (0 : (Fin m → F.obj U.1) →ₗ[R] F.obj U.1)
      (fun j => LinearMap.proj j) (Fin.last m) : _ →ₗ[R] _) g = 0
    rw [Fin.lastCases_last]; rfl
  have hcast : ∀ (U : V.affineOpens) (g : (F.pow m).obj U.1) (j : Fin m),
      ιapp U g j.castSucc = (g : Fin m → F.obj U.1) j := by
    intro U g j
    change (Fin.lastCases (0 : (Fin m → F.obj U.1) →ₗ[R] F.obj U.1)
      (fun j => LinearMap.proj j) j.castSucc : _ →ₗ[R] _) g = g j
    rw [Fin.lastCases_castSucc]; rfl
  exact
    { inc :=
        { app := ιapp
          app_smul := fun U a g => funext fun k => by
            refine Fin.lastCases ?_ (fun j => ?_) k
            · rw [show (a • ιapp U g) (Fin.last m) = a • ιapp U g (Fin.last m) from rfl,
                hlast U (a • g), hlast U g, smul_zero]
            · rw [show (a • ιapp U g) j.castSucc = a • ιapp U g j.castSucc from rfl,
                hcast U (a • g) j, hcast U g j]; rfl
          naturality := fun {U U'} h => LinearMap.ext fun g => funext fun k => by
            refine Fin.lastCases ?_ (fun j => ?_) k
            · rw [LinearMap.comp_apply, LinearMap.comp_apply,
                show (F.pow (m + 1)).res h (ιapp U' g) (Fin.last m)
                  = F.res h (ιapp U' g (Fin.last m)) from rfl,
                hlast U, hlast U', map_zero]
            · rw [LinearMap.comp_apply, LinearMap.comp_apply,
                show (F.pow (m + 1)).res h (ιapp U' g) j.castSucc
                  = F.res h (ιapp U' g j.castSucc) from rfl,
                hcast U, hcast U']; rfl }
      proj :=
        { app := fun U => LinearMap.proj (R := R) (φ := fun _ : Fin (m + 1) => F.obj U.1)
            (Fin.last m)
          app_smul := fun U a x => rfl
          naturality := fun {U U'} h => rfl }
      injective := fun U g g' hgg' => funext fun j =>
        (hcast U g j).symm.trans ((congrFun hgg' j.castSucc).trans (hcast U g' j))
      surjective := fun U x => ⟨fun _ => x, rfl⟩
      exact := fun U => le_antisymm
        (LinearMap.range_le_ker_iff.mpr (LinearMap.ext fun g => hlast U g))
        (fun g hg => ⟨fun j => g j.castSucc, funext fun k => Fin.lastCases
          ((hlast U _).trans (LinearMap.mem_ker.mp hg).symm)
          (fun j => hcast U _ j) k⟩) }

theorem pow_of_ext (Q : OModulePresheaf π → Prop)
    (h0 : ∀ G : OModulePresheaf π, (∀ U : V.affineOpens, Subsingleton (G.obj U.1)) → Q G)
    (hext : ∀ (G₁ G₂ G₃ : OModulePresheaf π), Nonempty (AffSES G₁ G₂ G₃) →
      G₁.IsCoherent → G₁.IsQuasicoherent → G₂.IsCoherent → G₂.IsQuasicoherent →
      G₃.IsCoherent → G₃.IsQuasicoherent → Q G₁ → Q G₃ → Q G₂)
    {F : OModulePresheaf π} (hFc : F.IsCoherent) (hFq : F.IsQuasicoherent) (hF : Q F) (n : ℕ) :
    Q (F.pow n) := by
  induction n with
  | zero => exact h0 _ fun U => ⟨fun a b => funext fun k => k.elim0⟩
  | succ m ih =>
    exact hext (F.pow m) (F.pow (m + 1)) F ⟨affSESPowSucc F m⟩ (isCoherent_pow m hFc)
      (isQuasicoherent_pow m hFq) (isCoherent_pow (m + 1) hFc) (isQuasicoherent_pow (m + 1) hFq) hFc hFq ih hF

end AlgebraicGeometry.OModulePresheaf.PivotQAux

end

set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 1600000 in
open _root_.AlgebraicGeometry.OModulePresheaf _root_.P2MW.S_AlgebraicGeometry_OModulePresheaf_forall_pushforward_of_isIntegral.AlgebraicGeometry.OModulePresheaf in

theorem solution
    {R : Type u} [CommRing R] [IsNoetherianRing R] {V : Scheme.{u}} (π : V ⟶ Spec (.of R)) [IsProper π]
    (Z₀ : Closeds V) (hZ₀ : (Z₀ : Set V).Nonempty)
    (hint : IsIntegral (Scheme.IdealSheafData.vanishingIdeal Z₀).subscheme)
    (Q : OModulePresheaf π → Prop)
    (h0 : ∀ G : OModulePresheaf π, (∀ U : V.affineOpens, Subsingleton (G.obj U.1)) → Q G)
    (hext : ∀ (G₁ G₂ G₃ : OModulePresheaf π), Nonempty (OModulePresheaf.AffSES G₁ G₂ G₃) →
      G₁.IsCoherent → G₁.IsQuasicoherent → G₂.IsCoherent → G₂.IsQuasicoherent →
      G₃.IsCoherent → G₃.IsQuasicoherent →
      (Q G₁ → Q G₃ → Q G₂) ∧ (Q G₁ → Q G₂ → Q G₃) ∧ (Q G₂ → Q G₃ → Q G₁))
    (hO : Q (OModulePresheaf.pushforwardUnit π (Scheme.IdealSheafData.vanishingIdeal Z₀).subschemeι))
    (ih : ∀ Y' < Z₀, ∀ G : OModulePresheaf π, G.IsCoherent → G.IsQuasicoherent → G.SupportedIn Y' → Q G)
    (H : OModulePresheaf ((Scheme.IdealSheafData.vanishingIdeal Z₀).subschemeι ≫ π))
    (hc : (OModulePresheaf.pushforward π (Scheme.IdealSheafData.vanishingIdeal Z₀).subschemeι H).IsCoherent)
    (hq : (OModulePresheaf.pushforward π (Scheme.IdealSheafData.vanishingIdeal Z₀).subschemeι H).IsQuasicoherent)
    (hs : (OModulePresheaf.pushforward π (Scheme.IdealSheafData.vanishingIdeal Z₀).subschemeι H).SupportedIn Z₀) :
    Q (OModulePresheaf.pushforward π (Scheme.IdealSheafData.vanishingIdeal Z₀).subschemeι H) := by
  haveI : IsSeparated π := inferInstance
  haveI : IsNoetherian V := PivotQAux.isNoetherian_of_isProper π
  haveI : IsLocallyNoetherian V := inferInstance
  let Z₀S := (Scheme.IdealSheafData.vanishingIdeal Z₀).subscheme
  let iZ := (Scheme.IdealSheafData.vanishingIdeal Z₀).subschemeι
  let G : OModulePresheaf π := OModulePresheaf.pushforward π iZ H
  let O : OModulePresheaf π := OModulePresheaf.pushforwardUnit π iZ
  haveI := hint
  haveI : IsProper (iZ ≫ π) := inferInstance
  have hOc : O.IsCoherent := PivotQAux.isCoherent_pushforwardUnit iZ
  have hOq : O.IsQuasicoherent := PivotQAux.isQuasicoherent_pushforwardUnit iZ
  show Q G

  obtain ⟨r, Z₁, hZ₁_lt, P, hPc, hPq, α, β, hαbij, hβbij⟩ :
      ∃ (r : ℕ) (Z₁ : Closeds V), Z₁ < Z₀ ∧
        ∃ (P : OModulePresheaf π), P.IsCoherent ∧ P.IsQuasicoherent ∧
        ∃ (α : OModulePresheaf.Hom P G) (β : OModulePresheaf.Hom P (O.pow r)),
          (∀ U : V.affineOpens, ((U : V.Opens) : Set V) ∩ Z₁ = ∅ →
            Function.Bijective (α.app U.1)) ∧
          (∀ U : V.affineOpens, ((U : V.Opens) : Set V) ∩ Z₁ = ∅ →
            Function.Bijective (β.app U.1)) := by

    obtain ⟨U₀, f, hW₀Z, r, y, hψbij⟩ :=
      AlgebraicGeometry.OModulePresheaf.exists_basicOpen_sections_free_of_isIntegral π hZ₀ hint H hc hq
    set W₀ := V.basicOpen f
    have hW₀U₀ : W₀ ≤ U₀.1 := V.basicOpen_le f
    set Z₁ : Closeds V := ⟨(Z₀ : Set V) \ W₀, Z₀.2.sdiff W₀.2⟩
    have hZ₁_lt : Z₁ < Z₀ := ⟨fun x hx => hx.1,
      fun h => let ⟨x, hxW, hxZ⟩ := hW₀Z; (h hxZ).2 hxW⟩
    set Or := O.pow r

    let ψ₀ : ∀ (W : V.Opens), W ≤ U₀.1 → Or.obj W →ₗ[R] G.obj W := fun W hWU =>
      letI := (fun O => (Scheme.TwoAffineOpenCover.algebraOfHom (iZ ≫ π) O).toModule) (iZ ⁻¹ᵁ W)
      haveI := H.isScalarTower (iZ ⁻¹ᵁ W)
      ∑ i, ({ toFun := fun mm => (mm i : Γ(Z₀S, iZ ⁻¹ᵁ W)) •
                H.res ((Opens.map iZ.base).monotone hWU) (y i)
              map_add' := fun a b => add_smul _ _ _
              map_smul' := fun c a => smul_assoc c _ _ } :
        (Fin r → Γ(Z₀S, iZ ⁻¹ᵁ W)) →ₗ[R] H.obj (iZ ⁻¹ᵁ W))
    have hψ₀_apply : ∀ {W} (hWU : W ≤ U₀.1) (m : Fin r → Γ(Z₀S, iZ ⁻¹ᵁ W)),
        ψ₀ W hWU m = ∑ i, m i • H.res ((Opens.map iZ.base).monotone hWU) (y i) :=
      fun {W} hWU m => by
        letI := (fun O => (Scheme.TwoAffineOpenCover.algebraOfHom (iZ ≫ π) O).toModule) (iZ ⁻¹ᵁ W)
        exact LinearMap.sum_apply (M₂ := H.obj (iZ ⁻¹ᵁ W)) _ _ m
    have hψ₀_Γlin : ∀ {W} (hWU : W ≤ U₀.1) (b : Γ(V, W)) (m : Or.obj W),
        ψ₀ W hWU (b • m) = b • ψ₀ W hWU m := fun {W} hWU b m => by
      letI := (fun O => (Scheme.TwoAffineOpenCover.algebraOfHom (iZ ≫ π) O).toModule) (iZ ⁻¹ᵁ W)
      let m' : Fin r → Γ(Z₀S, iZ ⁻¹ᵁ W) := m
      let bm' : Fin r → Γ(Z₀S, iZ ⁻¹ᵁ W) := b • m
      refine (hψ₀_apply hWU bm').trans
        (Eq.trans ?_ (congrArg (b • ·) (hψ₀_apply hWU m').symm))
      show (∑ i, bm' i • H.res ((Opens.map iZ.base).monotone hWU) (y i) : H.obj (iZ ⁻¹ᵁ W))
        = (iZ.appLE W (iZ ⁻¹ᵁ W) le_rfl).hom b
            • ∑ i, m' i • H.res ((Opens.map iZ.base).monotone hWU) (y i)
      rw [Finset.smul_sum]
      exact Finset.sum_congr rfl fun i _ => mul_smul _ (m' i) _
    have hψ₀_nat : ∀ {W W' : V.Opens} (hWW' : W ≤ W') (hW'U : W' ≤ U₀.1) (m : Or.obj W'),
        G.res hWW' (ψ₀ W' hW'U m) = ψ₀ W (hWW'.trans hW'U) (Or.res hWW' m) :=
      fun {W W'} hWW' hW'U m => by
        letI := (fun O => (Scheme.TwoAffineOpenCover.algebraOfHom (iZ ≫ π) O).toModule) (iZ ⁻¹ᵁ W')
        letI := (fun O => (Scheme.TwoAffineOpenCover.algebraOfHom (iZ ≫ π) O).toModule) (iZ ⁻¹ᵁ W)
        let m' : Fin r → Γ(Z₀S, iZ ⁻¹ᵁ W') := m
        let rm' : Fin r → Γ(Z₀S, iZ ⁻¹ᵁ W) := Or.res hWW' m
        refine (congrArg (G.res hWW') (hψ₀_apply hW'U m')).trans
          (Eq.trans ?_ (hψ₀_apply (hWW'.trans hW'U) rm').symm)
        show (H.res ((Opens.map iZ.base).monotone hWW')
              (∑ i, m' i • H.res ((Opens.map iZ.base).monotone hW'U) (y i)) : H.obj (iZ ⁻¹ᵁ W))
          = ∑ i, rm' i • H.res ((Opens.map iZ.base).monotone (hWW'.trans hW'U)) (y i)
        rw [map_sum]
        exact Finset.sum_congr rfl fun i _ =>
          (H.res_smul ((Opens.map iZ.base).monotone hWW') (m' i) _).trans
            (congrArg (rm' i • ·) (LinearMap.congr_fun (H.res_comp _ _).symm (y i)))
    let δapp : ∀ U : V.Opens, G.obj U × Or.obj U →ₗ[R] G.obj (U ⊓ W₀) := fun U =>
      (G.res (inf_le_left : U ⊓ W₀ ≤ U)).comp (LinearMap.fst R _ _) -
        (ψ₀ (U ⊓ W₀) (inf_le_right.trans hW₀U₀)).comp
          ((Or.res (inf_le_left : U ⊓ W₀ ≤ U)).comp (LinearMap.snd R _ _))
    let δ : OModulePresheaf.Hom (G.prod Or) (G.restrOpen W₀) :=
      { app := δapp
        app_smul := fun U a xm =>
          (congrArg₂ (· - ·) (G.res_smul inf_le_left a xm.1)
            ((congrArg (ψ₀ (U ⊓ W₀) (inf_le_right.trans hW₀U₀))
              (Or.res_smul inf_le_left a xm.2)).trans
              (hψ₀_Γlin (inf_le_right.trans hW₀U₀) _ _))).trans
            (smul_sub ((V.presheaf.map (homOfLE (inf_le_left : U ⊓ W₀ ≤ U)).op).hom a)
              (G.res inf_le_left xm.1)
              (ψ₀ (U ⊓ W₀) (inf_le_right.trans hW₀U₀) (Or.res inf_le_left xm.2))).symm
        naturality := fun {U U'} h => LinearMap.ext fun xm =>
          (congrArg₂ (· - ·)
            ((LinearMap.congr_fun (G.res_comp inf_le_left h).symm xm.1).trans
              (LinearMap.congr_fun (G.res_comp (inf_le_inf_right W₀ h) inf_le_left) xm.1))
            ((congrArg (ψ₀ (U ⊓ W₀) (inf_le_right.trans hW₀U₀))
              ((LinearMap.congr_fun (Or.res_comp inf_le_left h).symm xm.2).trans
                (LinearMap.congr_fun
                  (Or.res_comp (inf_le_inf_right W₀ h) inf_le_left) xm.2))).trans
              (hψ₀_nat (inf_le_inf_right W₀ h) (inf_le_right.trans hW₀U₀)
                (Or.res inf_le_left xm.2)).symm)).trans
            (map_sub (G.res (inf_le_inf_right W₀ h)) _ _).symm }
    let P := OModulePresheaf.ker δ
    let ιP := (OModulePresheaf.kerImSES δ).inc
    let α := (G.fstHom Or).comp ιP
    let β := (G.sndHom Or).comp ιP

    have hαβbij : ∀ U : V.affineOpens, ((U : V.Opens) : Set V) ∩ Z₁ = ∅ →
        Function.Bijective (α.app U.1) ∧ Function.Bijective (β.app U.1) := fun U hU => by
      have hrange : Set.range iZ.base = (Z₀ : Set V) :=
        (Scheme.IdealSheafData.range_subschemeι _).trans
          (congrArg SetLike.coe (PivotQAux.support_vanishingIdeal' Z₀))
      have hpre_le : iZ ⁻¹ᵁ U.1 ≤ iZ ⁻¹ᵁ (U.1 ⊓ W₀) := fun z hz =>
        ⟨hz, not_not.mp fun hnw => Set.eq_empty_iff_forall_notMem.mp hU (iZ.base z)
          ⟨hz, hrange ▸ Set.mem_range_self z, hnw⟩⟩
      have hGres_bij : Function.Bijective (G.res (inf_le_left : U.1 ⊓ W₀ ≤ U.1)) := by
        change Function.Bijective (H.res _)
        exact ⟨Function.LeftInverse.injective (g := H.res hpre_le) fun a =>
            LinearMap.congr_fun ((H.res_comp hpre_le _).symm.trans (H.res_refl _)) a,
          Function.RightInverse.surjective (g := H.res hpre_le) fun a =>
            LinearMap.congr_fun ((H.res_comp _ hpre_le).symm.trans (H.res_refl _)) a⟩
      have hOrres_bij : Function.Bijective (Or.res (inf_le_left : U.1 ⊓ W₀ ≤ U.1)) := by
        let S := OModulePresheaf.unit (iZ ≫ π)
        have hSbij : Function.Bijective (S.res
            ((Opens.map iZ.base).monotone (inf_le_left : U.1 ⊓ W₀ ≤ U.1))) :=
          ⟨Function.LeftInverse.injective (g := S.res hpre_le) fun a =>
              LinearMap.congr_fun ((S.res_comp hpre_le _).symm.trans (S.res_refl _)) a,
            Function.RightInverse.surjective (g := S.res hpre_le) fun a =>
              LinearMap.congr_fun ((S.res_comp _ hpre_le).symm.trans (S.res_refl _)) a⟩
        exact ⟨fun a b hab => funext fun i => hSbij.1 (congrFun hab i),
          fun c => ⟨fun i => (hSbij.2 (c i)).choose, funext fun i => (hSbij.2 (c i)).choose_spec⟩⟩
      have hψ₀_bij : Function.Bijective (ψ₀ (U.1 ⊓ W₀) (inf_le_right.trans hW₀U₀)) :=
        (funext (hψ₀_apply (W := U.1 ⊓ W₀) (inf_le_right.trans hW₀U₀)) :
            ⇑(ψ₀ (U.1 ⊓ W₀) (inf_le_right.trans hW₀U₀)) = _).symm ▸
          hψbij (U.1 ⊓ W₀) inf_le_right
            (Scheme.OrderedAffineCover.isAffineOpen_inf_of_isSeparated π U.2 (U₀.2.basicOpen f))
      have hψOr_bij := hψ₀_bij.comp hOrres_bij
      have hδeq : ∀ (p : P.obj U.1), G.res inf_le_left p.1.1
          = ψ₀ (U.1 ⊓ W₀) (inf_le_right.trans hW₀U₀) (Or.res inf_le_left p.1.2) := fun p =>
        sub_eq_zero.mp (LinearMap.mem_ker.mp p.2)
      refine ⟨⟨fun p₁ p₂ hp => Subtype.ext (Prod.ext hp (hψOr_bij.1
          ((hδeq p₁).symm.trans ((congrArg (G.res inf_le_left) (show p₁.1.1 = p₂.1.1 from hp)).trans
            (hδeq p₂))))), fun x =>
          let ⟨m, hm⟩ := hψOr_bij.2 (G.res inf_le_left x)
          ⟨⟨(x, m), LinearMap.mem_ker.mpr (sub_eq_zero.mpr hm.symm)⟩, rfl⟩⟩,
        ⟨fun p₁ p₂ hp => Subtype.ext (Prod.ext (hGres_bij.1
          ((hδeq p₁).trans ((congrArg _ (congrArg (Or.res inf_le_left)
            (show p₁.1.2 = p₂.1.2 from hp))).trans (hδeq p₂).symm))) hp), fun m =>
          let ⟨x, hx⟩ := hGres_bij.2 (ψ₀ _ (inf_le_right.trans hW₀U₀) (Or.res inf_le_left m))
          ⟨⟨(x, m), LinearMap.mem_ker.mpr (sub_eq_zero.mpr hx)⟩, rfl⟩⟩⟩

    have haff : ∀ U : V.affineOpens, IsAffineOpen (U.1 ⊓ W₀) := fun U =>
      Scheme.OrderedAffineCover.isAffineOpen_inf_of_isSeparated π U.2 (U₀.2.basicOpen f)
    exact ⟨r, Z₁, hZ₁_lt, P,
      PivotQAux.isCoherent_ker δ (PivotQAux.isCoherent_prod hc
        (PivotQAux.isCoherent_pow r hOc)),
      PivotQAux.isQuasicoherent_ker δ (PivotQAux.isQuasicoherent_prod hq
        (PivotQAux.isQuasicoherent_pow r hOq)) (PivotQAux.isQuasicoherent_restrOpen W₀ haff hq),
      α, β, fun U hU => (hαβbij U hU).1, fun U hU => (hαβbij U hU).2⟩

  have hOr : Q (O.pow r) :=
    PivotQAux.pow_of_ext Q h0 (fun G₁ G₂ G₃ hS h1c h1q h2c h2q h3c h3q =>
      (hext G₁ G₂ G₃ hS h1c h1q h2c h2q h3c h3q).1) hOc hOq hO r
  have hOrc : (O.pow r).IsCoherent := PivotQAux.isCoherent_pow r hOc
  have hOrq : (O.pow r).IsQuasicoherent := PivotQAux.isQuasicoherent_pow r hOq

  have hflk : ∀ {F' G' : OModulePresheaf π} (φ : OModulePresheaf.Hom F' G')
      (_ : F'.IsCoherent) (_ : F'.IsQuasicoherent)
      (_ : G'.IsCoherent) (_ : G'.IsQuasicoherent)
      (_ : ∀ U : V.affineOpens, ((U : V.Opens) : Set V) ∩ Z₁ = ∅ →
        Function.Bijective (φ.app U.1)),
      ((OModulePresheaf.ker φ).IsCoherent ∧ (OModulePresheaf.ker φ).IsQuasicoherent ∧
        Q (OModulePresheaf.ker φ)) ∧
      ((OModulePresheaf.im φ).IsCoherent ∧ (OModulePresheaf.im φ).IsQuasicoherent) ∧
      ((OModulePresheaf.coker φ).IsCoherent ∧ (OModulePresheaf.coker φ).IsQuasicoherent ∧
        Q (OModulePresheaf.coker φ)) := by
    intro F' G' φ hF'c hF'q hG'c hG'q hbij
    have hkc := PivotQAux.isCoherent_ker φ hF'c
    have hkq := PivotQAux.isQuasicoherent_ker φ hF'q hG'q
    have hcc := PivotQAux.isCoherent_coker φ hG'c
    have hcq := PivotQAux.isQuasicoherent_coker φ hG'q hF'q
    exact ⟨⟨hkc, hkq, ih Z₁ hZ₁_lt _ hkc hkq
        (fun U hU => ⟨fun a b => Subtype.ext ((hbij U hU).1 (a.2.trans b.2.symm))⟩)⟩,
      ⟨PivotQAux.isCoherent_im φ hF'c, PivotQAux.isQuasicoherent_im φ hF'q hG'q⟩,
      ⟨hcc, hcq, ih Z₁ hZ₁_lt _ hcc hcq
        (fun U hU => Submodule.Quotient.subsingleton_iff.mpr
          (LinearMap.range_eq_top.mpr (hbij U hU).2))⟩⟩

  obtain ⟨⟨hkβc, hkβq, hkβ⟩, ⟨hiβc, hiβq⟩, ⟨hcβc, hcβq, hcβ⟩⟩ := hflk β hPc hPq hOrc hOrq hβbij
  have himβ : Q (OModulePresheaf.im β) :=
    (hext _ _ _ ⟨(OModulePresheaf.imCokerSES β).toAffSES⟩ hiβc hiβq hOrc hOrq hcβc hcβq).2.2 hOr hcβ
  have hP : Q P :=
    (hext _ _ _ ⟨(OModulePresheaf.kerImSES β).toAffSES⟩ hkβc hkβq hPc hPq hiβc hiβq).1 hkβ himβ
  obtain ⟨⟨hkαc, hkαq, hkα⟩, ⟨hiαc, hiαq⟩, ⟨hcαc, hcαq, hcα⟩⟩ := hflk α hPc hPq hc hq hαbij
  have himα : Q (OModulePresheaf.im α) :=
    (hext _ _ _ ⟨(OModulePresheaf.kerImSES α).toAffSES⟩ hkαc hkαq hPc hPq hiαc hiαq).2.1 hkα hP
  exact (hext _ _ _ ⟨(OModulePresheaf.imCokerSES α).toAffSES⟩ hiαc hiαq hc hq hcαc hcαq).1 himα hcα

end S_AlgebraicGeometry_OModulePresheaf_forall_pushforward_of_isIntegral
end P2MW
export P2MW.S_AlgebraicGeometry_OModulePresheaf_forall_pushforward_of_isIntegral (solution)
