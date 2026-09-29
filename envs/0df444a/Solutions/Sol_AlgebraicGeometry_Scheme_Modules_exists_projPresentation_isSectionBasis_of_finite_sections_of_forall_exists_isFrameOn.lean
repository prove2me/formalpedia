-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.Modules.exists_projPresentation_isSectionBasis_of_finite_sections_of_forall_exists_isFrameOn
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/43b5ce15-d056-57c7-ade0-3cdb79f09aa8

import Definitions.Def_AlgebraicGeometry_FramedPolarisedAbelianScheme
import Definitions.Def_AlgebraicGeometry_ModulesSectionsTensorV2
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_exists_projPresentation_of_iSup_eq_top
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_projPresentation_isSectionBasis_of_finite_sections_of_forall_exists_isFrameOn

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_projPresentation_isSectionBasis_of_finite_sections_of_forall_exists_isFrameOn.AlgebraicGeometry"

attribute [local instance] MvPolynomial.gradedAlgebra

universe u v

namespace FrameL1Aux
variable {X : Scheme.{u}} {M : X.Modules}
theorem map_map {V₁ V₂ V₃ : X.Opens} (h₂₁ : V₂ ≤ V₁) (h₃₂ : V₃ ≤ V₂) (y : Γ(M, V₁)) :
    M.presheaf.map (homOfLE h₃₂).op (M.presheaf.map (homOfLE h₂₁).op y) =
      M.presheaf.map (homOfLE (h₃₂.trans h₂₁)).op y := by
  change (M.presheaf.map (homOfLE h₂₁).op ≫ M.presheaf.map (homOfLE h₃₂).op) y = _
  rw [← Functor.map_comp]; rfl

end FrameL1Aux

namespace AlgebraicGeometry p2m_export "AlgebraicGeometry" "Spec Scheme RingedSpace.isUnit_res_of_isUnit_germ Scheme.Modules Scheme.Modules.map_smul RingedSpace Scheme.ΓSpecIso Scheme.Modules.IsSectionBasis Scheme.Modules.IsInvertible Scheme.Modules.ProjPresentation Scheme.Modules.IsFrameOn Scheme.Modules.exists_projPresentation_of_iSup_eq_top" namespace Scheme p2m_export "AlgebraicGeometry.Scheme" "Γ empty toLocallyRingedSpace Modules Opens Modules.map_smul ΓSpecIso Modules.IsSectionBasis Modules.IsInvertible Modules.ProjPresentation Modules.IsFrameOn Modules.exists_projPresentation_of_iSup_eq_top" namespace Modules p2m_export "AlgebraicGeometry.Scheme.Modules" "presheaf isSheaf map_smul IsSectionBasis IsInvertible ProjPresentation IsFrameOn exists_projPresentation_of_iSup_eq_top" namespace BasisPresentation end AlgebraicGeometry.Scheme.Modules.BasisPresentation
p2m_open_scoped "AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Modules" in
open _root_.AlgebraicGeometry.Scheme.Modules FrameL1Aux in

theorem AlgebraicGeometry.Scheme.Modules.BasisPresentation.isFrameOn_iSup
    {X : Scheme.{u}} {M : X.Modules} {U : X.Opens} {ι : Type v} {s : Γ(M, U)}
    (V : ι → X.Opens) (h : ∀ i, Scheme.Modules.IsFrameOn s (V i)) :
    Scheme.Modules.IsFrameOn s (⨆ i, V i) := by
  intro W hWU hWV

  let Wi : ι → X.Opens := fun i => W ⊓ V i
  have hcov : W ≤ ⨆ i, Wi i := by
    intro x hx
    have hx' : x ∈ (⨆ i, V i : X.Opens) := hWV hx
    rw [Opens.mem_iSup] at hx' ⊢
    obtain ⟨i, hi⟩ := hx'
    exact ⟨i, ⟨hx, hi⟩⟩
  let FM : TopCat.Sheaf Ab X.carrier := ⟨M.presheaf, M.isSheaf⟩
  set sW : Γ(M, W) := M.presheaf.map (homOfLE hWU).op s with hsW
  have key : ∀ i, Function.Bijective fun g : Γ(X, Wi i) =>
      g • (M.presheaf.map (homOfLE (inf_le_left : Wi i ≤ W)).op sW : Γ(M, Wi i)) := by
    intro i
    have := h i (W := Wi i) (inf_le_left.trans hWU) inf_le_right
    rw [hsW, map_map]
    exact this
  constructor
  · intro g g' hgg'
    simp only at hgg'
    apply X.sheaf.eq_of_locally_eq' Wi W (fun i => homOfLE inf_le_left) hcov
    intro i
    apply (key i).1
    change X.presheaf.map (homOfLE (inf_le_left : Wi i ≤ W)).op g • _ =
      X.presheaf.map (homOfLE (inf_le_left : Wi i ≤ W)).op g' • _
    rw [← M.map_smul, ← M.map_smul]
    exact congrArg _ hgg'
  · intro x

    have hloc : ∀ i, ∃! g : Γ(X, Wi i),
        g • (M.presheaf.map (homOfLE (inf_le_left : Wi i ≤ W)).op sW : Γ(M, Wi i)) =
          M.presheaf.map (homOfLE (inf_le_left : Wi i ≤ W)).op x :=
      fun i => (Function.bijective_iff_existsUnique _).1 (key i) _
    choose g hg hguniq using hloc

    have hcomp : TopCat.Presheaf.IsCompatible X.sheaf.1 Wi g := by
      intro i j

      have hb := h i (W := Wi i ⊓ Wi j) ((inf_le_left.trans inf_le_left).trans hWU)
        (inf_le_left.trans inf_le_right)
      apply hb.1
      simp only
      have e1 : M.presheaf.map (homOfLE ((inf_le_left.trans inf_le_left).trans hWU)).op s =
          M.presheaf.map (homOfLE (inf_le_left : Wi i ⊓ Wi j ≤ Wi i)).op
            (M.presheaf.map (homOfLE (inf_le_left : Wi i ≤ W)).op sW) := by
        rw [hsW, map_map, map_map]
      have e2 : M.presheaf.map (homOfLE ((inf_le_left.trans inf_le_left).trans hWU)).op s =
          M.presheaf.map (homOfLE (inf_le_right : Wi i ⊓ Wi j ≤ Wi j)).op
            (M.presheaf.map (homOfLE (inf_le_left : Wi j ≤ W)).op sW) := by
        rw [hsW, map_map, map_map]
      conv_lhs => rw [e1]
      conv_rhs => rw [e2]
      change X.presheaf.map (homOfLE inf_le_left).op (g i) • _ =
        X.presheaf.map (homOfLE inf_le_right).op (g j) • _
      rw [← M.map_smul, ← M.map_smul, hg i, hg j, map_map, map_map]
    obtain ⟨G, hG, -⟩ := X.sheaf.existsUnique_gluing' Wi W (fun i => homOfLE inf_le_left) hcov g hcomp
    let G' : Γ(X, W) := G
    refine ⟨G', ?_⟩
    simp only
    apply FM.eq_of_locally_eq' Wi W (fun i => homOfLE inf_le_left) hcov
    intro i
    change M.presheaf.map (homOfLE inf_le_left).op (G' • sW) = M.presheaf.map (homOfLE inf_le_left).op x
    rw [M.map_smul]
    have : X.presheaf.map (homOfLE (inf_le_left : Wi i ≤ W)).op G' = g i := hG i
    rw [this, hg i]

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Spec Scheme RingedSpace.isUnit_res_of_isUnit_germ Scheme.Modules Scheme.Modules.map_smul RingedSpace Scheme.ΓSpecIso Scheme.Modules.IsSectionBasis Scheme.Modules.IsInvertible Scheme.Modules.ProjPresentation Scheme.Modules.IsFrameOn Scheme.Modules.exists_projPresentation_of_iSup_eq_top"
namespace Scheme
p2m_export "AlgebraicGeometry.Scheme" "Γ empty toLocallyRingedSpace Modules Opens Modules.map_smul ΓSpecIso Modules.IsSectionBasis Modules.IsInvertible Modules.ProjPresentation Modules.IsFrameOn Modules.exists_projPresentation_of_iSup_eq_top"
namespace Modules
p2m_export "AlgebraicGeometry.Scheme.Modules" "presheaf isSheaf map_smul IsSectionBasis IsInvertible ProjPresentation IsFrameOn exists_projPresentation_of_iSup_eq_top"
namespace BasisPresentation
p2m_open "AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme AlgebraicGeometry"

variable {X : Scheme.{u}} {M : X.Modules}

theorem map_map {U V W : X.Opens} (hVU : V ≤ U) (hWV : W ≤ V) (s : Γ(M, U)) :
    M.presheaf.map (homOfLE hWV).op (M.presheaf.map (homOfLE hVU).op s) =
      M.presheaf.map (homOfLE (hWV.trans hVU)).op s := by
  rw [← CategoryTheory.comp_apply, ← M.presheaf.map_comp]
  rfl

theorem isFrameOn_of_map_eq_smul {U W : X.Opens} {s t : Γ(M, U)} (hs : Scheme.Modules.IsFrameOn s W) (hWU : W ≤ U)
    (g : Γ(X, W)) (hg : IsUnit g)
    (ht : M.presheaf.map (homOfLE hWU).op t = g • M.presheaf.map (homOfLE hWU).op s) :
    Scheme.Modules.IsFrameOn t W := by
  intro W' hW'U hW'W
  have e : M.presheaf.map (homOfLE hW'U).op t =
      X.presheaf.map (homOfLE hW'W).op g • M.presheaf.map (homOfLE hW'U).op s := by
    rw [← map_map hWU hW'W t, ht, Scheme.Modules.map_smul, map_map hWU hW'W s]
  have hu : IsUnit (X.presheaf.map (homOfLE hW'W).op g) := hg.map _
  have hcomp : (fun g' : Γ(X, W') => g' • M.presheaf.map (homOfLE hW'U).op t) =
      (fun g' : Γ(X, W') => g' • M.presheaf.map (homOfLE hW'U).op s) ∘ (fun g' : Γ(X, W') => g' * ↑hu.unit) := by
    funext g'
    simp only [Function.comp_apply, e, smul_smul, IsUnit.unit_spec]
  rw [hcomp]
  exact (hs hW'U hW'W).comp (Units.mulRight hu.unit).bijective

end AlgebraicGeometry.Scheme.Modules.BasisPresentation

open AlgebraicGeometry.Scheme.Modules.BasisPresentation

theorem solution
    (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k)) (hX : Nonempty X)
    (𝓝 : X.Modules) (h𝓝 : Scheme.Modules.IsInvertible 𝓝)
    (hfin : letI : Algebra k Γ(X, ⊤) := ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appLE ⊤ ⊤ le_top).hom.toAlgebra
      letI : Module k Γ(𝓝, ⊤) := Module.compHom _ (algebraMap k Γ(X, ⊤))
      Module.Finite k Γ(𝓝, ⊤))
    (hgen : ∀ x : X, ∃ (s : Γ(𝓝, ⊤)) (U : X.Opens), x ∈ U ∧ Scheme.Modules.IsFrameOn s U) :
    ∃ (N : ℕ) (𝔓 : Scheme.Modules.ProjPresentation 𝓝 f N), Scheme.Modules.IsSectionBasis f 𝓝 𝔓.σ := by
  classical
  letI instA : Algebra k Γ(X, ⊤) := ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appLE ⊤ ⊤ le_top).hom.toAlgebra
  letI instM : Module k Γ(𝓝, ⊤) := Module.compHom _ (algebraMap k (X.presheaf.obj (op ⊤)))
  haveI : Module.Finite k Γ(𝓝, ⊤) := hfin
  have hsmul : ∀ (c : k) (m : Γ(𝓝, ⊤)), c • m = (algebraMap k (X.presheaf.obj (op ⊤)) c) • m := fun _ _ => rfl

  obtain ⟨x₀⟩ := hX
  haveI : Nontrivial Γ(𝓝, ⊤) := by
    obtain ⟨s, U, hxU, hs⟩ := hgen x₀
    haveI : Nontrivial Γ(X, U) := (X.presheaf.germ U x₀ hxU).hom.domain_nontrivial
    refine ⟨⟨s, 0, fun h0 => ?_⟩⟩
    have hb := hs (le_top : U ≤ ⊤) (le_refl U)
    have h10 : (1 : Γ(X, U)) = 0 := hb.1 (by simp only [h0, map_zero, smul_zero])
    exact one_ne_zero h10
  have hpos : 0 < Module.finrank k Γ(𝓝, ⊤) := Module.finrank_pos
  obtain ⟨N, hN⟩ : ∃ N : ℕ, Module.finrank k Γ(𝓝, ⊤) = N + 1 := ⟨_, (Nat.succ_pred_eq_of_pos hpos).symm⟩
  let b : Module.Basis (Fin (N + 1)) k Γ(𝓝, ⊤) := Module.finBasisOfFinrankEq k Γ(𝓝, ⊤) hN

  have key : ∀ x : X, ∃ (i : Fin (N + 1)) (W : X.Opens), x ∈ W ∧ Scheme.Modules.IsFrameOn (b i) W := by
    intro x
    obtain ⟨s, U, hxU, hs⟩ := hgen x
    have hbij := hs (le_top : U ≤ ⊤) (le_refl U)
    choose g hg using fun i => hbij.2 (𝓝.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op (b i))
    simp only at hg

    have hsum : ∑ i, (b.repr s i) • b i = s := b.sum_repr s
    have hres : (∑ i, X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op (algebraMap k (X.presheaf.obj (op ⊤)) (b.repr s i)) * g i) •
        𝓝.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op s =
        (1 : Γ(X, U)) • 𝓝.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op s := by
      rw [one_smul, Finset.sum_smul]
      conv_rhs => rw [← hsum, map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← smul_smul, hg i, hsmul, Scheme.Modules.map_smul]
    have hone : ∑ i, X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op (algebraMap k (X.presheaf.obj (op ⊤)) (b.repr s i)) * g i = 1 :=
      hbij.1 hres
    have hunit : ∃ i, IsUnit ((X.presheaf.germ U x hxU).hom (g i)) := by
      by_contra hall
      push Not at hall
      have hmem : ∀ i, (X.presheaf.germ U x hxU).hom
          (X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op (algebraMap k (X.presheaf.obj (op ⊤)) (b.repr s i)) * g i) ∈
          IsLocalRing.maximalIdeal ↑(X.presheaf.stalk x) := fun i => by
        rw [map_mul]
        exact Ideal.mul_mem_left _ _ ((IsLocalRing.mem_maximalIdeal _).mpr (hall i))
      have h1 : (1 : ↑(X.presheaf.stalk x)) ∈ IsLocalRing.maximalIdeal ↑(X.presheaf.stalk x) := by
        have := congrArg (X.presheaf.germ U x hxU).hom hone
        rw [map_sum, map_one] at this
        rw [← this]
        exact Ideal.sum_mem _ (fun i _ => hmem i)
      exact (IsLocalRing.maximalIdeal.isMaximal _).ne_top (Ideal.eq_top_of_isUnit_mem _ h1 isUnit_one)
    obtain ⟨i, hi⟩ := hunit
    obtain ⟨W, iWU, hxW, hW⟩ := RingedSpace.isUnit_res_of_isUnit_germ (X := X.toLocallyRingedSpace.toSheafedSpace)
      U (g i) x hxU hi
    refine ⟨i, W, hxW, ?_⟩
    refine isFrameOn_of_map_eq_smul (hs.mono iWU.le) (le_top : W ≤ ⊤) (X.presheaf.map iWU.op (g i)) hW ?_

    rw [← map_map (le_top : U ≤ ⊤) iWU.le (b i), ← hg i, Scheme.Modules.map_smul,
      map_map (le_top : U ≤ ⊤) iWU.le s]
    rfl

  let V : Fin (N + 1) → X.Opens := fun i => ⨆ p : {W : X.Opens // Scheme.Modules.IsFrameOn (b i) W}, p.1
  have hV : ∀ i, Scheme.Modules.IsFrameOn (b i) (V i) := fun i =>
    AlgebraicGeometry.Scheme.Modules.BasisPresentation.isFrameOn_iSup (fun p : {W : X.Opens // Scheme.Modules.IsFrameOn (b i) W} => p.1) (fun p => p.2)
  have hVtop : iSup V = ⊤ := by
    refine top_le_iff.mp fun x _ => ?_
    obtain ⟨i, W, hxW, hW⟩ := key x
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨i, TopologicalSpace.Opens.mem_iSup.2 ⟨⟨W, hW⟩, hxW⟩⟩
  obtain ⟨𝔓, h𝔓, -⟩ := AlgebraicGeometry.Scheme.Modules.exists_projPresentation_of_iSup_eq_top f 𝓝 N (fun i => b i) V hVtop
    (fun i W hW => hV i (le_top : W ≤ ⊤) hW)
  refine ⟨N, 𝔓, ?_⟩
  show Function.Bijective fun c : Fin (N + 1) → k =>
    ∑ i, ((f.appLE ⊤ ⊤ le_top).hom ((Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom (c i))) • 𝔓.σ i
  rw [h𝔓]
  have hfun : (fun c : Fin (N + 1) → k =>
      ∑ i, ((f.appLE ⊤ ⊤ le_top).hom ((Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom (c i))) • b i) =
      fun c => b.equivFun.symm c := by
    funext c
    rw [Module.Basis.equivFun_symm_apply]
    rfl
  rw [hfun]
  exact b.equivFun.symm.bijective

end S_AlgebraicGeometry_Scheme_Modules_exists_projPresentation_isSectionBasis_of_finite_sections_of_forall_exists_isFrameOn
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_projPresentation_isSectionBasis_of_finite_sections_of_forall_exists_isFrameOn (solution)
