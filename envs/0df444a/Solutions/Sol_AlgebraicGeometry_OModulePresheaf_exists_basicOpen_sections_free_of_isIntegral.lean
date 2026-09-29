-- Prove2me | solution 1 for AlgebraicGeometry.OModulePresheaf.exists_basicOpen_sections_free_of_isIntegral
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/1ae9e34d-3832-5b33-a1be-d3dd0eaf2874

import Definitions.Def_AlgebraicGeometry_OModulePresheafConstructions
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_basicOpen_sections_free_of_isIntegral

set_option autoImplicit false

universe u

p2m_open "CategoryTheory AlgebraicGeometry P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_basicOpen_sections_free_of_isIntegral.AlgebraicGeometry TopologicalSpace Opposite"

noncomputable section

section
p2m_open "CategoryTheory AlgebraicGeometry P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_basicOpen_sections_free_of_isIntegral.AlgebraicGeometry TopologicalSpace Opposite"
namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Scheme.Hom.map_appLE IsLocallyNoetherian Scheme.basicOpen_res IsProper Scheme.IdealSheafData.coe_support_vanishingIdeal basicOpen_eq_bot_iff LocallyOfFiniteType.isLocallyNoetherian Scheme.Hom QuasiCompact Scheme.preimage_basicOpen LocallyOfFiniteType Spec IsIntegral Scheme.IdealSheafData.range_subschemeι Scheme Scheme.IdealSheafData.vanishingIdeal QuasiCompact.compactSpace_of_compactSpace IsClosedImmersion IsLocallyNoetherian.component_noetherian IsAffineOpen IsNoetherian Scheme.Hom.appLE_map IsIntegral.component_integral Scheme.IdealSheafData Scheme.Hom.appLE_eq_app OModulePresheaf.pushforward OModulePresheaf.pushforwardUnit OModulePresheaf"
namespace OModulePresheaf
p2m_export "AlgebraicGeometry.OModulePresheaf" "prod pow restrOpen ker coker kerImSES imCokerSES pushforward pushforwardUnit Hom res_refl_apply res_res d IsCoherent IsQuasicoherent unit res res_smul res_refl mk module obj res_comp"
namespace GenericFreenessAux
p2m_open "AlgebraicGeometry.OModulePresheaf AlgebraicGeometry"

theorem support_vanishingIdeal' {V : Scheme.{u}} (Z : Closeds V) :
    (Scheme.IdealSheafData.vanishingIdeal Z).support = Z :=
  SetLike.coe_injective (Scheme.IdealSheafData.coe_support_vanishingIdeal Z)

end AlgebraicGeometry.OModulePresheaf.GenericFreenessAux
end

set_option autoImplicit false

section

p2m_open "CategoryTheory AlgebraicGeometry P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_basicOpen_sections_free_of_isIntegral.AlgebraicGeometry TopologicalSpace Opposite"

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Scheme.Hom.map_appLE IsLocallyNoetherian Scheme.basicOpen_res IsProper Scheme.IdealSheafData.coe_support_vanishingIdeal basicOpen_eq_bot_iff LocallyOfFiniteType.isLocallyNoetherian Scheme.Hom QuasiCompact Scheme.preimage_basicOpen LocallyOfFiniteType Spec IsIntegral Scheme.IdealSheafData.range_subschemeι Scheme Scheme.IdealSheafData.vanishingIdeal QuasiCompact.compactSpace_of_compactSpace IsClosedImmersion IsLocallyNoetherian.component_noetherian IsAffineOpen IsNoetherian Scheme.Hom.appLE_map IsIntegral.component_integral Scheme.IdealSheafData Scheme.Hom.appLE_eq_app OModulePresheaf.pushforward OModulePresheaf.pushforwardUnit OModulePresheaf"
namespace OModulePresheaf
p2m_export "AlgebraicGeometry.OModulePresheaf" "prod pow restrOpen ker coker kerImSES imCokerSES pushforward pushforwardUnit Hom res_refl_apply res_res d IsCoherent IsQuasicoherent unit res res_smul res_refl mk module obj res_comp"
namespace GenericFreenessAux
p2m_open "AlgebraicGeometry.OModulePresheaf AlgebraicGeometry"

variable {R : Type u} [CommRing R] {V : Scheme.{u}} {π : V ⟶ Spec (.of R)}

section KerCoker

variable {F G : OModulePresheaf π} (φ : Hom F G)

theorem isCoherent_ker [IsLocallyNoetherian V] (hF : F.IsCoherent) : (ker φ).IsCoherent := fun U => by
  haveI := hF U
  haveI : IsNoetherianRing Γ(V, U.1) := IsLocallyNoetherian.component_noetherian U
  haveI : _root_.IsNoetherian Γ(V, U.1) (F.obj U.1) := isNoetherian_of_isNoetherianRing_of_finite _ _
  exact Module.Finite.of_injective ((kerImSES φ).inc.appSections U.1) ((kerImSES φ).injective U.1)

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

end KerCoker

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

theorem eq_zero_of_res_basicOpen_eq_zero {F : OModulePresheaf π} (hF : F.IsQuasicoherent)
    (U : V.affineOpens) {ι : Type*} [Fintype ι] (h : ι → Γ(V, U.1))
    (hcov : U.1 ≤ ⨆ j, V.basicOpen (h j)) (x : F.obj U.1)
    (hx : ∀ j, F.res (V.basicOpen_le (h j)) x = 0) : x = 0 := by
  choose n hn using fun j => (hF U (h j)).2 x (hx j)
  have hspan : Ideal.span (Set.range fun j => (h j) ^ (n j + 1)) = ⊤ := by
    rw [← U.2.self_le_iSup_basicOpen_iff]
    exact (hcov.trans (iSup_mono fun j =>
        (V.basicOpen_pow (h j) (n j).succ_pos).ge)).trans
      (iSup_le fun j => le_iSup_of_le ⟨_, j, rfl⟩ le_rfl)
  obtain ⟨c, hc⟩ := Ideal.mem_span_range_iff_exists_fun.mp
    (show (1 : Γ(V, U.1)) ∈ Ideal.span _ from hspan ▸ Submodule.mem_top)
  calc x = (1 : Γ(V, U.1)) • x := (one_smul _ x).symm
    _ = (∑ j, c j * (h j) ^ (n j + 1)) • x := by rw [hc]
    _ = ∑ j, c j • ((h j) ^ (n j + 1) • x) := by
        rw [Finset.sum_smul]; exact Finset.sum_congr rfl fun j _ => mul_smul _ _ _
    _ = 0 := Finset.sum_eq_zero fun j _ => by
        rw [pow_succ', mul_smul, hn j, smul_zero, smul_zero]

theorem isNoetherian_of_isProper [IsNoetherianRing R] (π : V ⟶ Spec (.of R)) [IsProper π] :
    IsNoetherian V := by
  haveI : LocallyOfFiniteType π := inferInstance
  haveI : IsLocallyNoetherian (Spec (CommRingCat.of R)) := inferInstance
  haveI : IsLocallyNoetherian V := LocallyOfFiniteType.isLocallyNoetherian π
  haveI : CompactSpace V := QuasiCompact.compactSpace_of_compactSpace π
  exact {}

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

end AlgebraicGeometry.OModulePresheaf.GenericFreenessAux

end

end

set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 1600000 in
open _root_.AlgebraicGeometry.OModulePresheaf _root_.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_basicOpen_sections_free_of_isIntegral.AlgebraicGeometry.OModulePresheaf AlgebraicGeometry.OModulePresheaf.GenericFreenessAux in

theorem solution
    {R : Type u} [CommRing R] [IsNoetherianRing R] {V : Scheme.{u}} (π : V ⟶ Spec (.of R)) [IsProper π]
    {Z₀ : TopologicalSpace.Closeds V} (hZ₀ : (Z₀ : Set V).Nonempty)
    (hint : IsIntegral (Scheme.IdealSheafData.vanishingIdeal Z₀).subscheme)
    (H : OModulePresheaf ((Scheme.IdealSheafData.vanishingIdeal Z₀).subschemeι ≫ π))
    (hc : (OModulePresheaf.pushforward π (Scheme.IdealSheafData.vanishingIdeal Z₀).subschemeι H).IsCoherent)
    (hq : (OModulePresheaf.pushforward π (Scheme.IdealSheafData.vanishingIdeal Z₀).subschemeι H).IsQuasicoherent) :
    ∃ (U₀ : V.affineOpens) (f : Γ(V, U₀.1)), ((V.basicOpen f : Set V) ∩ Z₀).Nonempty ∧
      ∃ (r : ℕ) (y : Fin r → H.obj ((Scheme.IdealSheafData.vanishingIdeal Z₀).subschemeι ⁻¹ᵁ U₀.1)),
        ∀ (W : V.Opens) (hW : W ≤ V.basicOpen f), IsAffineOpen W →
          Function.Bijective (fun m : Fin r →
              Γ((Scheme.IdealSheafData.vanishingIdeal Z₀).subscheme,
                (Scheme.IdealSheafData.vanishingIdeal Z₀).subschemeι ⁻¹ᵁ W) =>
            (∑ i, m i • H.res ((TopologicalSpace.Opens.map
                (Scheme.IdealSheafData.vanishingIdeal Z₀).subschemeι.base).monotone
                  (hW.trans (V.basicOpen_le f))) (y i) :
              H.obj ((Scheme.IdealSheafData.vanishingIdeal Z₀).subschemeι ⁻¹ᵁ W))) := by
  let Z₀S := (Scheme.IdealSheafData.vanishingIdeal Z₀).subscheme
  let iZ := (Scheme.IdealSheafData.vanishingIdeal Z₀).subschemeι
  let G : OModulePresheaf π := OModulePresheaf.pushforward π iZ H
  let O : OModulePresheaf π := OModulePresheaf.pushforwardUnit π iZ
  haveI := hint
  haveI : IsProper (iZ ≫ π) := inferInstance
  have hOq : O.IsQuasicoherent := GenericFreenessAux.isQuasicoherent_pushforwardUnit iZ
  have hZ₀_ne := hZ₀
  show ∃ (U₀ : V.affineOpens) (f : Γ(V, U₀.1)),
      ((V.basicOpen f : Set V) ∩ Z₀).Nonempty ∧
      ∃ (r : ℕ) (y : Fin r → H.obj (iZ ⁻¹ᵁ U₀.1)),
        ∀ (W : V.Opens) (hW : W ≤ V.basicOpen f), IsAffineOpen W →
          Function.Bijective (fun m : Fin r → Γ(Z₀S, iZ ⁻¹ᵁ W) =>
            (∑ i, m i • H.res ((Opens.map iZ.base).monotone
              (hW.trans (V.basicOpen_le f))) (y i) : H.obj (iZ ⁻¹ᵁ W)))

  have hrange : Set.range iZ.base = (Z₀ : Set V) :=
    (Scheme.IdealSheafData.range_subschemeι _).trans
      (congrArg SetLike.coe (support_vanishingIdeal' Z₀))
  obtain ⟨z₀, hz₀⟩ := hZ₀_ne
  obtain ⟨z₀', hz₀'⟩ := (Set.ext_iff.mp hrange z₀).mpr hz₀
  obtain ⟨U₀o, hU₀mem, hz₀U₀, -⟩ := (Opens.isBasis_iff_nbhd.mp V.isBasis_affineOpens)
    (show z₀ ∈ (⊤ : V.Opens) from trivial)
  refine ⟨⟨U₀o, hU₀mem⟩, ?_⟩
  set U₀ : V.affineOpens := ⟨U₀o, hU₀mem⟩
  have hZU₀aff : IsAffineOpen (iZ ⁻¹ᵁ U₀.1) := U₀.2.preimage iZ
  haveI : Nonempty (iZ ⁻¹ᵁ U₀.1) :=
    ⟨⟨z₀', show iZ.base z₀' ∈ U₀.1 from hz₀'.symm ▸ hz₀U₀⟩⟩
  let A := Γ(Z₀S, iZ ⁻¹ᵁ U₀.1)
  let M := H.obj (iZ ⁻¹ᵁ U₀.1)
  haveI hAdom : IsDomain A := IsIntegral.component_integral _
  haveI : IsNoetherian Z₀S := GenericFreenessAux.isNoetherian_of_isProper (iZ ≫ π)
  haveI : IsLocallyNoetherian Z₀S := inferInstance
  haveI hAnoeth : IsNoetherianRing A :=
    IsLocallyNoetherian.component_noetherian ⟨iZ ⁻¹ᵁ U₀.1, hZU₀aff⟩
  letI : Module Γ(V, U₀.1) M := Module.compHom _ (iZ.appLE U₀.1 (iZ ⁻¹ᵁ U₀.1) le_rfl).hom
  haveI hMfin : Module.Finite A M := by
    obtain ⟨s, hs⟩ : (⊤ : Submodule Γ(V, U₀.1) M).FG := (hc U₀).fg_top
    refine ⟨⟨s, top_unique fun x _ => Submodule.span_induction
      (p := fun a _ => a ∈ Submodule.span A (↑s : Set M))
      (fun a ha => Submodule.subset_span ha) (Submodule.zero_mem _)
      (fun _ _ _ _ ha hb => Submodule.add_mem _ ha hb)
      (fun c a _ ha => Submodule.smul_mem _ ((iZ.appLE U₀.1 _ le_rfl).hom c) ha)
      (hs ▸ (Submodule.mem_top : x ∈ ⊤))⟩⟩
  haveI : Module.FinitePresentation A M := Module.finitePresentation_of_finite _ _
  haveI : Module.Finite (FractionRing A) (LocalizedModule (nonZeroDivisors A) M) :=
    Module.Finite.of_isLocalizedModule (Rₚ := FractionRing A)
      (nonZeroDivisors A) (LocalizedModule.mkLinearMap (nonZeroDivisors A) M)
  haveI : Module.Free (FractionRing A) (LocalizedModule (nonZeroDivisors A) M) :=
    Module.free_of_finite_type_torsion_free'
  obtain ⟨g, hg_nzd, hfree, hrank⟩ :=
    Module.FinitePresentation.exists_free_localizedModule_powers
      (R := A) (M := M) (nonZeroDivisors A)
      (LocalizedModule.mkLinearMap (nonZeroDivisors A) M) (FractionRing A)
  set r := Module.finrank (FractionRing A) (LocalizedModule (nonZeroDivisors A) M)
  have hg_ne : g ≠ 0 := nonZeroDivisors.ne_zero hg_nzd
  obtain ⟨f, hf⟩ := iZ.app_surjective U₀.1 U₀.2 g
  refine ⟨f, ?_, r, ?_⟩
  · have hbo : iZ ⁻¹ᵁ V.basicOpen f = Z₀S.basicOpen g :=
      (Scheme.preimage_basicOpen iZ f).trans (by rw [hf])
    have hgne : (Z₀S.basicOpen g : Set Z₀S).Nonempty := by
      rw [Set.nonempty_iff_ne_empty]
      exact fun he => hg_ne ((basicOpen_eq_bot_iff g).mp (SetLike.ext' he))
    rw [← hrange, ← Set.image_preimage_eq_inter_range]
    exact Set.image_nonempty.mpr
      (show (iZ ⁻¹ᵁ V.basicOpen f : Set Z₀S).Nonempty from hbo ▸ hgne)
  haveI : Module.Finite (Localization (.powers g)) (LocalizedModule (.powers g) M) :=
    Module.Finite.of_isLocalizedModule (Rₚ := Localization (.powers g))
      (.powers g) (LocalizedModule.mkLinearMap _ M)
  haveI : Nontrivial (Localization (.powers g)) :=
    (IsLocalization.injective (M := .powers g) (Localization (.powers g))
      (powers_le_nonZeroDivisors_of_noZeroDivisors hg_ne)).nontrivial
  let b' := Module.finBasisOfFinrankEq (Localization (.powers g))
    (LocalizedModule (.powers g) M) hrank
  choose ys hys using fun i => IsLocalizedModule.surj (.powers g)
    (LocalizedModule.mkLinearMap (.powers g) M) (b' i)
  let y : Fin r → M := fun i => (ys i).1
  let bY := b'.isUnitSMul fun i => IsLocalization.map_units (M := .powers g) _ (ys i).2
  have hbY_apply : ∀ i, bY i = LocalizedModule.mkLinearMap (.powers g) M (y i) := fun i =>
    (b'.isUnitSMul_apply _ i).trans ((algebraMap_smul (Localization (.powers g))
      ((ys i).2 : A) (b' i)).trans (hys i))
  refine ⟨y, fun W hW hWaff => ?_⟩

  have hWU₀ : W ≤ U₀.1 := hW.trans (V.basicOpen_le f)
  let ψW : ∀ ⦃W'⦄, W' ≤ U₀.1 → (Fin r → Γ(Z₀S, iZ ⁻¹ᵁ W')) → H.obj (iZ ⁻¹ᵁ W') :=
    fun W' hW' m => ∑ i, m i • H.res ((Opens.map iZ.base).monotone hW') (y i)
  have hψnat : ∀ ⦃W₁ W₂⦄ (h12 : W₁ ≤ W₂) (h2U : W₂ ≤ U₀.1) (m),
      H.res ((Opens.map iZ.base).monotone h12) (ψW h2U m)
        = ψW (h12.trans h2U) (fun i => (Z₀S.presheaf.map
            (homOfLE ((Opens.map iZ.base).monotone h12)).op).hom (m i)) :=
    fun W₁ W₂ h12 h2U m => (map_sum _ _ _).trans (Finset.sum_congr rfl fun i _ =>
      (H.res_smul _ _ _).trans
        (congrArg _ (LinearMap.congr_fun (H.res_comp _ _).symm (y i))))
  choose f' hf'le hf'mem using
    fun p : W => U₀.2.exists_basicOpen_le (V := W) p (hWU₀ p.2)
  obtain ⟨t, ht⟩ := hWaff.isCompact.elim_finite_subcover
    (fun p : W => (V.basicOpen (f' p) : Set V)) (fun p => (V.basicOpen (f' p)).2)
    (fun x hx => Set.mem_iUnion.mpr ⟨⟨x, hx⟩, hf'mem ⟨x, hx⟩⟩)
  let f'' : t → Γ(V, W) := fun p => (V.presheaf.map (homOfLE hWU₀).op).hom (f' p.1)
  have hDeq : ∀ p : t, V.basicOpen (f'' p) = V.basicOpen (f' p.1) := fun p =>
    (Scheme.basicOpen_res _ _ _).trans (inf_eq_right.mpr (hf'le p.1))
  have hcov : W ≤ ⨆ p : t, V.basicOpen (f'' p) := fun x hx => by
    obtain ⟨p, hp, hxp⟩ := Set.mem_iUnion₂.mp (ht hx)
    exact Opens.mem_iSup.mpr ⟨⟨p, hp⟩, (hDeq ⟨p, hp⟩).symm ▸ hxp⟩
  have hψbasic : ∀ p : t,
      Function.Bijective (ψW ((V.basicOpen_le (f'' p)).trans hWU₀)) := fun p => by
    obtain ⟨hGs, hGa⟩ := hq U₀ (f' p.1)
    let hp : A := (iZ.app U₀.1).hom (f' p.1)
    have hpow : ∀ n (w : M), ((f' p.1 : Γ(V, U₀.1)) ^ n) • (show G.obj U₀.1 from w)
        = (hp ^ n : A) • w := fun n w => by
      show (iZ.appLE U₀.1 _ le_rfl).hom (f' p.1 ^ n) • w = _
      rw [map_pow, Scheme.Hom.appLE_eq_app]
    have hbo₀ : iZ ⁻¹ᵁ V.basicOpen (f' p.1) = Z₀S.basicOpen hp :=
      Scheme.preimage_basicOpen iZ (f' p.1)
    have hle_g : Z₀S.basicOpen hp ≤ Z₀S.basicOpen g := hbo₀.ge.trans
      (((Opens.map iZ.base).monotone ((hf'le p.1).trans hW)).trans
        ((Scheme.preimage_basicOpen iZ f).trans (congrArg Z₀S.basicOpen hf)).le)
    suffices ∀ (Wz) (hWz : Wz ≤ iZ ⁻¹ᵁ U₀.1), Wz = Z₀S.basicOpen hp →
        Function.Bijective (fun m : Fin r → Γ(Z₀S, Wz) =>
          (∑ i, m i • H.res hWz (y i) : H.obj Wz)) from
      this _ _ ((congrArg (iZ ⁻¹ᵁ ·) (hDeq p)).trans hbo₀)
    rintro _ hWz rfl
    haveI := hZU₀aff.isLocalization_basicOpen hp
    letI : Module A (H.obj (Z₀S.basicOpen hp)) :=
      Module.compHom _ (algebraMap A Γ(Z₀S, Z₀S.basicOpen hp))
    haveI : IsScalarTower A Γ(Z₀S, Z₀S.basicOpen hp) (H.obj (Z₀S.basicOpen hp)) :=
      IsScalarTower.of_algebraMap_smul fun _ _ => rfl
    let Hres : M →ₗ[A] H.obj (Z₀S.basicOpen hp) :=
      { toFun := H.res hWz, map_add' := map_add _, map_smul' := H.res_smul hWz }
    have hres_fac : ∀ w, Hres w = H.res hbo₀.ge (G.res (V.basicOpen_le (f' p.1)) w) :=
      fun w => LinearMap.congr_fun (H.res_comp hbo₀.ge _) w
    have hge_le : ∀ z, H.res hbo₀.ge (H.res hbo₀.le z) = z := fun z =>
      (LinearMap.congr_fun (H.res_comp hbo₀.ge hbo₀.le).symm z).trans
        (LinearMap.congr_fun (H.res_refl _) z)
    have hle_ge : ∀ z, H.res hbo₀.le (H.res hbo₀.ge z) = z := fun z =>
      (LinearMap.congr_fun (H.res_comp hbo₀.le hbo₀.ge).symm z).trans
        (LinearMap.congr_fun (H.res_refl _) z)
    haveI : IsLocalizedModule (.powers hp) Hres := by
      refine ⟨fun s => (IsLocalization.map_units (M := .powers hp)
          Γ(Z₀S, Z₀S.basicOpen hp) s).map (Algebra.lsmul A _ _), fun z => ?_, fun hz => ?_⟩
      · obtain ⟨n, w, hw⟩ := hGs (H.res hbo₀.le z)
        refine ⟨⟨w, hp ^ n, n, rfl⟩, ((hres_fac w).trans ((congrArg _ hw).trans
          ((H.res_smul hbo₀.ge _ _).trans ?_))).symm⟩
        refine (congrArg₂ (· • · : Γ(Z₀S, Z₀S.basicOpen hp) → _ → _) ?_ (hge_le z) :)
        show (Z₀S.presheaf.map (homOfLE hbo₀.ge).op).hom
            ((iZ.appLE (V.basicOpen (f' p.1)) _ le_rfl).hom
              ((V.presheaf.map (homOfLE (V.basicOpen_le (f' p.1))).op).hom (f' p.1 ^ n)))
          = algebraMap A Γ(Z₀S, Z₀S.basicOpen hp) (hp ^ n)
        rw [← CommRingCat.comp_apply (f := V.presheaf.map _), Scheme.Hom.map_appLE,
          ← CommRingCat.comp_apply, Scheme.Hom.appLE_map, map_pow, map_pow]
        rfl
      · obtain ⟨n, hn⟩ := hGa _ ((hle_ge _).symm.trans ((congrArg (H.res hbo₀.le)
          ((hres_fac _).symm.trans ((map_sub Hres _ _).trans (sub_eq_zero.mpr hz)))).trans
            (map_zero _)))
        exact ⟨⟨hp ^ n, n, rfl⟩,
          sub_eq_zero.mp ((smul_sub _ _ _).symm.trans ((hpow n _).symm.trans hn))⟩
    have hgB : IsUnit (algebraMap A Γ(Z₀S, Z₀S.basicOpen hp) g) := by
      haveI := hZU₀aff.isLocalization_basicOpen g
      show IsUnit ((Z₀S.presheaf.map (homOfLE (Z₀S.basicOpen_le hp)).op).hom g)
      rw [show (homOfLE (Z₀S.basicOpen_le hp) : (Z₀S.basicOpen hp : Z₀S.Opens) ⟶ _)
          = homOfLE hle_g ≫ homOfLE (Z₀S.basicOpen_le g) from (homOfLE_comp _ _).symm,
        op_comp, Functor.map_comp, CommRingCat.comp_apply]
      exact (IsLocalization.Away.algebraMap_isUnit (S := Γ(Z₀S, Z₀S.basicOpen g)) g).map _
    have hψBlin : ∀ (b : Γ(Z₀S, Z₀S.basicOpen hp)) m,
        (fun m : Fin r → _ => ∑ i, m i • H.res hWz (y i)) (b • m)
          = b • (fun m => ∑ i, m i • H.res hWz (y i)) m := fun b m =>
      (Finset.sum_congr rfl fun i _ => show (b * m i) • H.res hWz (y i) = _ from
        mul_smul _ _ _).trans Finset.smul_sum.symm
    refine ⟨fun m₁ m₂ hm => funext fun i => ?_, fun z => ?_⟩
    · obtain ⟨s, hs⟩ := IsLocalization.exist_integer_multiples_of_finite (.powers hp) (m₁ - m₂)
      choose a ha using hs
      have hψ0 : (∑ j, (m₁ - m₂) j • H.res hWz (y j)) = 0 :=
        (Finset.sum_congr rfl fun j _ => sub_smul (m₁ j) (m₂ j) _).trans
          ((Finset.sum_sub_distrib ..).trans (sub_eq_zero.mpr hm))
      have h0 : Hres (∑ i, a i • y i) = 0 := by
        rw [map_sum]
        refine Eq.trans (Finset.sum_congr rfl fun j _ => (Hres.map_smul (a j) (y j)).trans
          (show (algebraMap A Γ(Z₀S, Z₀S.basicOpen hp) (a j)) • H.res hWz (y j)
              = algebraMap A Γ(Z₀S, Z₀S.basicOpen hp) (↑s : A)
                • (m₁ - m₂) j • H.res hWz (y j) by
            rw [ha j]; exact mul_smul _ _ _)) ?_
        rw [← Finset.smul_sum, hψ0, smul_zero]
      obtain ⟨⟨c, hc'⟩, hc⟩ := (IsLocalizedModule.eq_iff_exists (.powers hp) Hres).mp
        (h0.trans (map_zero Hres).symm)
      have hbY0 : ∀ j, algebraMap A (Localization (.powers g)) (c * a j) = 0 := fun j =>
        linearIndependent_iff'.mp bY.linearIndependent Finset.univ _
          ((Finset.sum_congr rfl fun j _ => (algebraMap_smul (Localization (.powers g))
              (c * a j) (bY j)).trans ((mul_smul c (a j) (bY j)).trans
                (congrArg (c • ·) ((hbY_apply j).symm ▸
                  (LocalizedModule.mkLinearMap (.powers g) M).map_smul (a j) (y j) |>.symm))))
            |>.trans (by rw [← Finset.smul_sum, ← map_sum, ← map_smul,
              show (c : A) • ∑ j, a j • y j = 0 from
                (Submonoid.smul_def _ _).symm.trans (hc.trans (smul_zero _)), map_zero]))
          j (Finset.mem_univ _)
      obtain ⟨⟨_, l, rfl⟩, hd⟩ :=
        (IsLocalization.map_eq_zero_iff (.powers g) (Localization (.powers g)) _).mp (hbY0 i)
      refine sub_eq_zero.mp ((((hgB.pow l).mul (IsLocalization.map_units (M := .powers hp)
        Γ(Z₀S, Z₀S.basicOpen hp) ⟨c, hc'⟩)).mul (IsLocalization.map_units (M := .powers hp)
          _ s)).mul_left_cancel (Eq.trans ?_ (mul_zero _).symm))
      rw [mul_assoc _ _ (m₁ i - m₂ i), ← map_pow,
        show algebraMap A Γ(Z₀S, Z₀S.basicOpen hp) (↑s : A) * (m₁ i - m₂ i)
          = algebraMap A _ (a i) from
            (Algebra.smul_def _ _).symm.trans ((Submonoid.smul_def _ _).symm.trans (ha i).symm),
        ← map_mul, ← map_mul, show g ^ l * c * a i = (0 : A) from
          (mul_assoc _ _ _).trans hd, map_zero]
    · obtain ⟨⟨w, s⟩, hw⟩ := IsLocalizedModule.surj (.powers hp) Hres z
      obtain ⟨c, hcc⟩ := IsLocalization.exist_integer_multiples_of_finite (.powers g)
        (fun i => bY.repr (LocalizedModule.mkLinearMap (.powers g) M w) i)
      choose a ha using hcc
      have hmk_eq : LocalizedModule.mkLinearMap (.powers g) M ((c : A) • w)
          = LocalizedModule.mkLinearMap (.powers g) M (∑ j, a j • y j) := by
        rw [map_smul, map_sum]
        refine (congrArg ((c : A) • ·) (bY.sum_repr _).symm).trans
          (Finset.smul_sum.trans (Finset.sum_congr rfl fun j _ => ?_))
        rw [← algebraMap_smul (Localization (.powers g)) (c : A), smul_smul,
          show algebraMap A _ (↑c : A) * bY.repr _ j = algebraMap A _ (a j) from
            (Algebra.smul_def _ _).symm.trans ((Submonoid.smul_def c _).symm.trans (ha j).symm),
          algebraMap_smul, hbY_apply, ← map_smul]
      obtain ⟨d, hd⟩ :=
        (IsLocalizedModule.eq_iff_exists (.powers g) (LocalizedModule.mkLinearMap _ M)).mp
          hmk_eq
      obtain ⟨k, hck⟩ := c.2; obtain ⟨l, hdl⟩ := d.2
      have hu : IsUnit (algebraMap A Γ(Z₀S, Z₀S.basicOpen hp)
          ((d : A) * (c : A) * (s : A))) := by
        rw [map_mul, map_mul, ← hdl, ← hck, map_pow, map_pow]
        exact ((hgB.pow l).mul (hgB.pow k)).mul (IsLocalization.map_units (M := .powers hp) _ s)
      refine ⟨fun i => ↑hu.unit⁻¹ * algebraMap A _ ((d : A) * a i), (hψBlin _ _).trans ?_⟩
      have hSumEq : (∑ j, ((d : A) * a j) • y j) = ((d : A) * (c : A)) • w :=
        (Finset.sum_congr rfl fun j _ => mul_smul _ _ _).trans (Finset.smul_sum.symm.trans
          (((Submonoid.smul_def d _).symm.trans hd.symm).trans
            ((Submonoid.smul_def d _).trans (smul_smul _ _ _))))
      have key : (∑ j, (algebraMap A (Z₀S.presheaf.obj (op (Z₀S.basicOpen hp))) ((d : A) * a j))
          • H.res hWz (y j))
            = algebraMap A (Z₀S.presheaf.obj (op (Z₀S.basicOpen hp))) ((d : A) * (c : A) * (s : A)) • z :=
        (Finset.sum_congr rfl fun j _ => (Hres.map_smul ((d : A) * a j) (y j)).symm).trans
          ((map_sum Hres _ _).symm.trans (by
            rw [hSumEq, Hres.map_smul, ← hw, Submonoid.smul_def, smul_smul] <;> rfl))
      show (↑hu.unit⁻¹ : Γ(Z₀S, Z₀S.basicOpen hp)) • (∑ j, (algebraMap A _ ((d : A) * a j))
        • H.res hWz (y j)) = z
      rw [key, ← mul_smul, hu.val_inv_mul, one_smul]
  refine ⟨fun m₁ m₂ hm => funext fun i => sub_eq_zero.mp ?_, fun x => ?_⟩
  · refine GenericFreenessAux.eq_zero_of_res_basicOpen_eq_zero hOq ⟨W, hWaff⟩ f'' hcov (m₁ i - m₂ i) fun p => ?_
    have hm0 := (hψbasic p).1 ((hψnat (V.basicOpen_le (f'' p)) hWU₀ m₁).symm.trans
      ((congrArg (H.res _) hm).trans (hψnat (V.basicOpen_le (f'' p)) hWU₀ m₂)))
    exact (map_sub (O.res (V.basicOpen_le (f'' p))) (m₁ i) (m₂ i)).trans
      (sub_eq_zero.mpr (congrFun hm0 i))
  · let x' : G.obj W := x
    have hψΓlin : ∀ (b : Γ(V, W)) (m : Fin r → Γ(Z₀S, iZ ⁻¹ᵁ W)),
        ψW hWU₀ ((iZ.appLE W _ le_rfl).hom b • m)
          = (iZ.appLE W _ le_rfl).hom b • ψW hWU₀ m :=
      fun b m => (Finset.sum_congr rfl fun i _ => mul_smul _ _ _).trans Finset.smul_sum.symm
    have hOrq := GenericFreenessAux.isQuasicoherent_pow r hOq
    have step : ∀ p : t, ∃ (Np : ℕ) (m' : Fin r → Γ(Z₀S, iZ ⁻¹ᵁ W)),
        ((f'' p) ^ Np : Γ(V, W)) • x' = ψW hWU₀ m' := fun p => by
      obtain ⟨mp, hmp⟩ := (hψbasic p).2
        (H.res ((Opens.map iZ.base).monotone (V.basicOpen_le (f'' p))) x)
      obtain ⟨np, mp'₀, hmp'⟩ := (hOrq ⟨W, hWaff⟩ (f'' p)).1 mp
      let mp' : Fin r → Γ(Z₀S, iZ ⁻¹ᵁ W) := mp'₀
      let ψWmp' : G.obj W := ψW hWU₀ mp'
      obtain ⟨kp, hkp⟩ := (hq ⟨W, hWaff⟩ (f'' p)).2
        (ψWmp' - ((f'' p : Γ(V, W)) ^ np) • x') (by
          refine (map_sub (G.res (V.basicOpen_le (f'' p))) _ _).trans (sub_eq_zero.mpr ?_)
          refine ((hψnat (V.basicOpen_le (f'' p)) hWU₀ mp').trans ?_).trans
            (G.res_smul (V.basicOpen_le (f'' p)) _ x).symm
          refine (congrArg (ψW ((V.basicOpen_le (f'' p)).trans hWU₀))
            (funext fun i => congrFun hmp' i)).trans ?_
          exact ((Finset.sum_congr rfl fun i _ => mul_smul _ _ _).trans
            Finset.smul_sum.symm).trans (congrArg _ hmp))
      refine ⟨kp + np, (iZ.appLE W _ le_rfl).hom ((f'' p) ^ kp) • mp',
        (?_ : _ = (f'' p ^ kp : Γ(V, W)) • ψWmp').trans (hψΓlin (f'' p ^ kp) mp').symm⟩
      rw [pow_add, mul_smul]
      exact (sub_eq_zero.mp ((smul_sub _ _ _).symm.trans hkp)).symm
    choose N m' hm' using step
    have hspan : Ideal.span (Set.range fun p : t => (f'' p) ^ (N p + 1)) = ⊤ := by
      rw [← hWaff.self_le_iSup_basicOpen_iff]
      exact (hcov.trans (iSup_mono fun p => (V.basicOpen_pow (f'' p) (N p).succ_pos).ge)).trans
        (iSup_le fun p => le_iSup_of_le ⟨_, p, rfl⟩ le_rfl)
    obtain ⟨c, hc⟩ := Ideal.mem_span_range_iff_exists_fun.mp
      (show (1 : Γ(V, W)) ∈ Ideal.span _ from hspan ▸ Submodule.mem_top)
    refine ⟨∑ p, (iZ.appLE W _ le_rfl).hom (c p * f'' p) • m' p,
      ((Finset.sum_congr rfl fun i _ =>
        (congrArg (fun a => a • H.res ((Opens.map iZ.base).monotone hWU₀) (y i))
          (Finset.sum_apply i Finset.univ
            (fun p : t => (iZ.appLE W (iZ ⁻¹ᵁ W) le_rfl).hom (c p * f'' p) • m' p))).trans
          Finset.sum_smul).trans
        Finset.sum_comm).trans ?_⟩
    refine (Finset.sum_congr rfl fun p _ => (hψΓlin (c p * f'' p) (m' p)).trans
        (show (c p * f'' p : Γ(V, W)) • (show G.obj W from ψW hWU₀ (m' p))
          = (c p * (f'' p) ^ (N p + 1)) • x' from by
          rw [← hm' p, smul_smul, mul_assoc, ← pow_succ'])).trans ?_
    exact (Finset.sum_smul (x := x')).symm.trans (hc ▸ one_smul _ x')

end S_AlgebraicGeometry_OModulePresheaf_exists_basicOpen_sections_free_of_isIntegral
end P2MW
export P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_basicOpen_sections_free_of_isIntegral (solution)
