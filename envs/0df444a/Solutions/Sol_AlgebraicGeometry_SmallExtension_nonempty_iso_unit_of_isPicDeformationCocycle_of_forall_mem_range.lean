-- Prove2me | solution 1 for AlgebraicGeometry.SmallExtension.nonempty_iso_unit_of_isPicDeformationCocycle_of_forall_mem_range
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/1ae2af6a-5051-5be5-8fea-f711035b04d2

import Mathlib
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverComap
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCochainPullback
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_CechPicardObstruction
import Theorems.Thm_AlgebraicGeometry_SmallExtension_exists_mem_map_range_and_isFibreReading_of_isAffineOpen
import Theorems.Thm_AlgebraicGeometry_SmallExtension_IsFibreReading_eq_zero_of_isFibreReading_zero_of_flat
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_CechTrivialisation_exists_forall_transition_eq_mul_mul
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_CechTrivialisation_nonempty_iso_unit_of_forall_transition_eq_one
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_SmallExtension_nonempty_iso_unit_of_isPicDeformationCocycle_of_forall_mem_range
p2m_attr_erase "instance" "PresheafOfModules.ExteriorPower.instModulePresheafAb"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.Hom.kaehlerPresheaf_obj PresheafOfModules.exteriorPower_map_ιMulti PresheafOfModules.ExteriorPower.appₗ_apply AlgebraicGeometry.Scheme.Modules.exteriorPower_obj AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_neg AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_zero AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_sub AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_add"

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing AlgebraicGeometry.SmallExtension AlgebraicGeometry.Scheme.TwoAffineOpenCover"

universe u

namespace D2Asm

open Opposite

def sing {X : Scheme.{u}} (𝒰 : X.OrderedAffineCover) (a : 𝒰.ι) : 𝒰.Idx 0 :=
  ⟨fun _ => a, fun x y h => by exfalso; have hx := x.2; have hy := y.2; have := Fin.lt_def.mp h; omega⟩

theorem inter_sing {X : Scheme.{u}} (𝒰 : X.OrderedAffineCover) (a : 𝒰.ι) : 𝒰.inter (sing 𝒰 a) = 𝒰.U a :=
  le_antisymm (𝒰.inter_le (sing 𝒰 a) 0) (le_iInf fun _ => le_rfl)

theorem inter_idx0 {X : Scheme.{u}} (𝒰 : X.OrderedAffineCover) (s₀ : 𝒰.Idx 0) : 𝒰.inter s₀ = 𝒰.U (s₀.1 0) :=
  le_antisymm (𝒰.inter_le s₀ 0) (le_iInf fun j => by
    have hj : j = 0 := Fin.ext (by have := j.2; omega)
    rw [hj])

theorem face_one_zero {X : Scheme.{u}} (𝒰 : X.OrderedAffineCover) (s : 𝒰.Idx 1) :
    𝒰.face s 0 = sing 𝒰 (s.1 1) := by
  apply Subtype.ext; funext j
  have hj : j = 0 := Fin.ext (by have := j.2; omega)
  subst hj; rfl

theorem face_one_one {X : Scheme.{u}} (𝒰 : X.OrderedAffineCover) (s : 𝒰.Idx 1) :
    𝒰.face s 1 = sing 𝒰 (s.1 0) := by
  apply Subtype.ext; funext j
  have hj : j = 0 := Fin.ext (by have := j.2; omega)
  subst hj; rfl

section RC
variable {B₁ : Type u} [CommRing B₁] {k : Type u} [Field k]
variable (V : Type u) [AddCommGroup V] [Module k V] [Module B₁ V] (ιJ : V →ₗ[B₁] B₁)
variable {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of B₁))
variable {Xk : Scheme.{u}} (fk : Xk ⟶ Spec (CommRingCat.of k)) (i : Xk ⟶ X)

theorem rc_add (U : X.Opens) (W : Xk.Opens) (hW : W ≤ i ⁻¹ᵁ U) (δ₁ δ₂ : Γ(X, U))
    (w₁ w₂ : Module.Dual k V →ₗ[k] (OModulePresheaf.unit fk).obj W)
    (h₁ : IsFibreReading V ιJ f fk i U W hW δ₁ w₁) (h₂ : IsFibreReading V ιJ f fk i U W hW δ₂ w₂) :
    IsFibreReading V ιJ f fk i U W hW (δ₁ + δ₂) (w₁ + w₂) := by
  letI := algebraOfHom f U
  obtain ⟨n, v, t, ht, hw⟩ := h₁
  obtain ⟨m, v', t', ht', hw'⟩ := h₂
  refine ⟨n + m, Fin.append v v', Fin.append t t', ?_, fun ξ => ?_⟩
  · rw [Fin.sum_univ_add]; simp only [Fin.append_left, Fin.append_right]; rw [ht, ht']
  · rw [LinearMap.add_apply, hw ξ, hw' ξ, Fin.sum_univ_add]; simp only [Fin.append_left, Fin.append_right]

theorem rc_neg (U : X.Opens) (W : Xk.Opens) (hW : W ≤ i ⁻¹ᵁ U) (δ : Γ(X, U))
    (w : Module.Dual k V →ₗ[k] (OModulePresheaf.unit fk).obj W)
    (h : IsFibreReading V ιJ f fk i U W hW δ w) :
    IsFibreReading V ιJ f fk i U W hW (-δ) (-w) := by
  letI := algebraOfHom f U
  obtain ⟨n, v, t, ht, hw⟩ := h
  refine ⟨n, v, fun j => - t j, ?_, fun ξ => ?_⟩
  · rw [← ht, ← Finset.sum_neg_distrib]; congr 1; ext j; ring
  · rw [LinearMap.neg_apply, hw ξ, ← Finset.sum_neg_distrib]
    congr 1; ext j
    show -(ξ (v j) • (OModulePresheaf.unit fk).res hW ((i.app U).hom (t j))) =
      ξ (v j) • (OModulePresheaf.unit fk).res hW ((i.app U).hom (-t j))
    have e : (i.app U).hom (-t j) = -((i.app U).hom (t j)) := map_neg _ _
    rw [e, ← smul_neg]
    congr 1
    exact (((OModulePresheaf.unit fk).res hW).map_neg _).symm

theorem rc_mul_eq_zero (hJ : ∀ v v' : V, ιJ v * ιJ v' = 0)
    (U : X.Opens) (W : Xk.Opens) (hW : W ≤ i ⁻¹ᵁ U) (δ₁ δ₂ : Γ(X, U))
    (w₁ w₂ : Module.Dual k V →ₗ[k] (OModulePresheaf.unit fk).obj W)
    (h₁ : IsFibreReading V ιJ f fk i U W hW δ₁ w₁) (h₂ : IsFibreReading V ιJ f fk i U W hW δ₂ w₂) :
    δ₁ * δ₂ = 0 := by
  letI := algebraOfHom f U
  obtain ⟨n, v, t, ht, -⟩ := h₁
  obtain ⟨m, v', t', ht', -⟩ := h₂
  rw [← ht, ← ht', Finset.sum_mul_sum]
  refine Finset.sum_eq_zero fun j _ => Finset.sum_eq_zero fun l _ => ?_
  calc algebraMap B₁ Γ(X, U) (ιJ (v j)) * t j * (algebraMap B₁ Γ(X, U) (ιJ (v' l)) * t' l)
      = algebraMap B₁ Γ(X, U) (ιJ (v j) * ιJ (v' l)) * (t j * t' l) := by rw [map_mul]; ring
    _ = 0 := by rw [hJ, map_zero, zero_mul]

theorem rc_res (U U' : X.Opens) (hU : U' ≤ U) (W W' : Xk.Opens) (hW : W ≤ i ⁻¹ᵁ U) (hWW : W' ≤ W)
    (hW' : W' ≤ i ⁻¹ᵁ U') (δ : Γ(X, U))
    (w : Module.Dual k V →ₗ[k] (OModulePresheaf.unit fk).obj W)
    (h : IsFibreReading V ιJ f fk i U W hW δ w) :
    IsFibreReading V ιJ f fk i U' W' hW' ((X.presheaf.map (homOfLE hU).op).hom δ)
      (((OModulePresheaf.unit fk).res hWW).comp w) := by
  letI := algebraOfHom f U
  letI := algebraOfHom f U'
  obtain ⟨n, v, t, ht, hw⟩ := h
  refine ⟨n, v, fun j => (X.presheaf.map (homOfLE hU).op).hom (t j), ?_, fun ξ => ?_⟩
  · rw [← ht, map_sum]
    congr 1; ext j
    rw [map_mul]
    congr 1
    exact ((restrictAlgHom f hU).commutes (ιJ (v j))).symm
  · rw [LinearMap.comp_apply, hw ξ, map_sum]
    congr 1; ext j
    rw [LinearMap.map_smul]
    congr 1

    change (Xk.presheaf.map (homOfLE hWW).op).hom ((Xk.presheaf.map (homOfLE hW).op).hom ((i.app U).hom (t j))) =
      (Xk.presheaf.map (homOfLE hW').op).hom ((i.app U').hom ((X.presheaf.map (homOfLE hU).op).hom (t j)))
    have h₃ : i ⁻¹ᵁ U' ≤ i ⁻¹ᵁ U := fun x hx => hU hx
    have e1 : (i.app U').hom ((X.presheaf.map (homOfLE hU).op).hom (t j)) =
        (Xk.presheaf.map ((TopologicalSpace.Opens.map i.base).map (homOfLE hU)).op).hom ((i.app U).hom (t j)) := by
      have := congrArg (fun φ => φ.hom (t j)) (i.naturality (homOfLE hU).op)
      simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply] at this
      exact this
    rw [e1]
    change (OModulePresheaf.unit fk).res hWW ((OModulePresheaf.unit fk).res hW ((i.app U).hom (t j))) =
      (OModulePresheaf.unit fk).res hW' ((OModulePresheaf.unit fk).res h₃ ((i.app U).hom (t j)))
    rw [OModulePresheaf.res_res, OModulePresheaf.res_res]

end RC

end D2Asm

open D2Asm in
theorem solution
    {B₁ B₀ : Type u} [CommRing B₁] [IsLocalRing B₁] [CommRing B₀]
    (π : B₁ →+* B₀) (hπ : Function.Surjective π)
    (hsmall : RingHom.ker π * maximalIdeal B₁ = ⊥) (hI : RingHom.ker π ≤ maximalIdeal B₁)

    (V : Type u) [AddCommGroup V] [Module (ResidueField B₁) V] [Module.Finite (ResidueField B₁) V]
    [Module B₁ V] [IsScalarTower B₁ (ResidueField B₁) V]
    (ι : V →ₗ[B₁] B₁) (hι : Function.Injective ι)
    (hιI : LinearMap.range ι = Submodule.restrictScalars B₁ (RingHom.ker π))

    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of B₁)) [IsSeparated f] [Flat f]
    {X₀ : Scheme.{u}} (f₀ : X₀ ⟶ Spec (CommRingCat.of B₀)) (g : X₀ ⟶ X) [IsAffineHom g]
    (hg : IsPullback g f₀ f (Spec.map (CommRingCat.ofHom π)))
    {Xk : Scheme.{u}} (fk : Xk ⟶ Spec (CommRingCat.of (ResidueField B₁))) (i : Xk ⟶ X) [IsAffineHom i]
    (hi : IsPullback i fk f (Spec.map (CommRingCat.ofHom (residue B₁))))
    (𝒰 : X.OrderedAffineCover)
    (M : X.Modules) (φ₀ : (Scheme.Modules.pullback g).obj M ≅ SheafOfModules.unit X₀.ringCatSheaf)
    (w : Module.Dual (ResidueField B₁) V →ₗ[ResidueField B₁] (OModulePresheaf.unit fk).cochain (𝒰.comap i) 1)
    (hw : IsPicDeformationCocycle V ι f fk i g 𝒰 M φ₀ w)
    (hcob : ∀ ξ : Module.Dual (ResidueField B₁) V,
      w ξ ∈ LinearMap.range ((OModulePresheaf.unit fk).d (𝒰.comap i) 0)) :
    Nonempty (M ≅ SheafOfModules.unit X.ringCatSheaf) := by
  classical
  obtain ⟨τ, e, e', hee', -, hread⟩ := hw
  set k := ResidueField B₁

  have hJ2 : ∀ v v' : V, ι v * ι v' = 0 := by
    intro v v'
    have hv : ι v ∈ RingHom.ker π := by
      have : ι v ∈ LinearMap.range ι := ⟨v, rfl⟩
      rw [hιI] at this; exact this
    have hv' : ι v' ∈ maximalIdeal B₁ := by
      have : ι v' ∈ LinearMap.range ι := ⟨v', rfl⟩
      rw [hιI] at this; exact hI this
    have := Ideal.mul_mem_mul hv hv'
    rw [hsmall] at this
    exact (Submodule.mem_bot B₁).mp this

  obtain ⟨τ₁, -, hτ₁⟩ := τ.exists_forall_transition_eq_mul_mul e e' hee'
  have hread₁ : ∀ s : 𝒰.Idx 1, IsFibreReading V ι f fk i (𝒰.inter s) ((𝒰.comap i).inter s) (𝒰.comap_inter_le i s)
      (τ₁.transition s - 1) ((LinearMap.proj s).comp w) := fun s => by
    rw [hτ₁]; exact hread s

  obtain ⟨θ, hθ⟩ : ∃ θ : Module.Dual k V →ₗ[k] (OModulePresheaf.unit fk).cochain (𝒰.comap i) 0,
      ∀ ξ, (OModulePresheaf.unit fk).d (𝒰.comap i) 0 (θ ξ) = w ξ := by
    let d0 := (OModulePresheaf.unit fk).d (𝒰.comap i) 0
    obtain ⟨θ, hθ⟩ := Module.projective_lifting_property d0.rangeRestrict
      (LinearMap.codRestrict (LinearMap.range d0) w hcob) (LinearMap.surjective_rangeRestrict d0)
    exact ⟨θ, fun ξ => congrArg Subtype.val (LinearMap.congr_fun hθ ξ)⟩

  have hε : ∀ s₀ : 𝒰.Idx 0, ∃ ε : Γ(X, 𝒰.inter s₀),
      IsFibreReading V ι f fk i (𝒰.inter s₀) ((𝒰.comap i).inter s₀) (𝒰.comap_inter_le i s₀) ε
        ((LinearMap.proj s₀).comp θ) := fun s₀ => by
    obtain ⟨ε, -, hε⟩ := exists_mem_map_range_and_isFibreReading_of_isAffineOpen V ι f fk i hi _
      (by rw [inter_idx0]; exact 𝒰.isAffineOpen _) _ (𝒰.comap_inter_le i s₀) (𝒰.le_comap_inter i s₀)
      ((LinearMap.proj s₀).comp θ)
    exact ⟨ε, hε⟩
  choose ε hε using hε
  have hUle : ∀ a : 𝒰.ι, 𝒰.U a ≤ 𝒰.inter (sing 𝒰 a) := fun a => le_iInf fun _ => le_rfl
  let c : ∀ a : 𝒰.ι, Γ(X, 𝒰.U a) := fun a => 1 - (X.presheaf.map (homOfLE (hUle a)).op).hom (ε (sing 𝒰 a))
  let c' : ∀ a : 𝒰.ι, Γ(X, 𝒰.U a) := fun a => 1 + (X.presheaf.map (homOfLE (hUle a)).op).hom (ε (sing 𝒰 a))
  have hcc' : ∀ a, c a * c' a = 1 := by
    intro a
    have hsq : ε (sing 𝒰 a) * ε (sing 𝒰 a) = 0 :=
      rc_mul_eq_zero V ι f fk i hJ2 _ _ _ _ _ _ _ (hε (sing 𝒰 a)) (hε (sing 𝒰 a))
    have : (X.presheaf.map (homOfLE (hUle a)).op).hom (ε (sing 𝒰 a)) *
        (X.presheaf.map (homOfLE (hUle a)).op).hom (ε (sing 𝒰 a)) = 0 := by
      rw [← map_mul, hsq, map_zero]
    simp only [c, c']
    linear_combination (-1 : Γ(X, 𝒰.U a)) * this
  obtain ⟨τ₂, -, hτ₂⟩ := τ₁.exists_forall_transition_eq_mul_mul c c' hcc'

  haveI : IsSeparated (terminal.from X) := by rw [← terminal.comp_from f]; infer_instance
  haveI : IsAffineHom (pullback.diagonal (terminal.from X)) := inferInstance
  have haff : ∀ s : 𝒰.Idx 1, IsAffineOpen (𝒰.inter s) := fun s =>
    IsAffineOpen.iInf (fun j => 𝒰.isAffineOpen (s.1 j))

  have res_idx : ∀ {s₀ s₀' : 𝒰.Idx 0} (hs : s₀ = s₀') (x : ∀ s₀ : 𝒰.Idx 0, (OModulePresheaf.unit fk).obj ((𝒰.comap i).inter s₀))
      {W : Xk.Opens} (p : W ≤ (𝒰.comap i).inter s₀) (p' : W ≤ (𝒰.comap i).inter s₀'),
      (OModulePresheaf.unit fk).res p (x s₀) = (OModulePresheaf.unit fk).res p' (x s₀') := by
    intro s₀ s₀' hs; subst hs; intro x W p p'; rfl
  have htriv : ∀ s : 𝒰.Idx 1, τ₂.transition s = 1 := by
    intro s
    rw [hτ₂ s]

    have ha : 𝒰.inter s ≤ 𝒰.inter (sing 𝒰 (s.1 0)) := (𝒰.inter_le s 0).trans (hUle (s.1 0))
    have hb : 𝒰.inter s ≤ 𝒰.inter (sing 𝒰 (s.1 1)) := (𝒰.inter_le s 1).trans (hUle (s.1 1))
    have hak : (𝒰.comap i).inter s ≤ (𝒰.comap i).inter (sing 𝒰 (s.1 0)) :=
      le_iInf fun _ => (𝒰.comap i).inter_le s 0
    have hbk : (𝒰.comap i).inter s ≤ (𝒰.comap i).inter (sing 𝒰 (s.1 1)) :=
      le_iInf fun _ => (𝒰.comap i).inter_le s 1
    set εa := (X.presheaf.map (homOfLE ha).op).hom (ε (sing 𝒰 (s.1 0))) with hεa
    set εb := (X.presheaf.map (homOfLE hb).op).hom (ε (sing 𝒰 (s.1 1))) with hεb
    set t := τ₁.transition s with ht

    have hA : (X.presheaf.map (homOfLE (𝒰.inter_le s 0)).op).hom (c' (s.1 0)) = 1 + εa := by
      simp only [c', map_add, map_one, hεa]
      congr 1
      rw [← CommRingCat.comp_apply, ← Functor.map_comp]; rfl
    have hB : (X.presheaf.map (homOfLE (𝒰.inter_le s 1)).op).hom (c (s.1 1)) = 1 - εb := by
      simp only [c, map_sub, map_one, hεb]
      congr 1
      rw [← CommRingCat.comp_apply, ← Functor.map_comp]; rfl
    rw [hA, hB]

    have Rδ := hread₁ s
    have Ra : IsFibreReading V ι f fk i (𝒰.inter s) ((𝒰.comap i).inter s) (𝒰.comap_inter_le i s) εa
        (((OModulePresheaf.unit fk).res hak).comp ((LinearMap.proj (sing 𝒰 (s.1 0))).comp θ)) :=
      rc_res V ι f fk i _ _ ha _ _ _ hak _ _ _ (hε (sing 𝒰 (s.1 0)))
    have Rb : IsFibreReading V ι f fk i (𝒰.inter s) ((𝒰.comap i).inter s) (𝒰.comap_inter_le i s) εb
        (((OModulePresheaf.unit fk).res hbk).comp ((LinearMap.proj (sing 𝒰 (s.1 1))).comp θ)) :=
      rc_res V ι f fk i _ _ hb _ _ _ hbk _ _ _ (hε (sing 𝒰 (s.1 1)))

    have p1 : (t - 1) * εa = 0 := rc_mul_eq_zero V ι f fk i hJ2 _ _ _ _ _ _ _ Rδ Ra
    have p2 : (t - 1) * εb = 0 := rc_mul_eq_zero V ι f fk i hJ2 _ _ _ _ _ _ _ Rδ Rb
    have p3 : εa * εb = 0 := rc_mul_eq_zero V ι f fk i hJ2 _ _ _ _ _ _ _ Ra Rb
    have hD : t * (1 + εa) * (1 - εb) - 1 = (t - 1) + εa - εb := by
      linear_combination p1 - p2 - t * p3

    have Rsum := rc_add V ι f fk i _ _ _ _ _ _ _ (rc_add V ι f fk i _ _ _ _ _ _ _ Rδ Ra)
      (rc_neg V ι f fk i _ _ _ _ _ Rb)
    have hW0 : (LinearMap.proj s).comp w +
        ((OModulePresheaf.unit fk).res hak).comp ((LinearMap.proj (sing 𝒰 (s.1 0))).comp θ) +
        -(((OModulePresheaf.unit fk).res hbk).comp ((LinearMap.proj (sing 𝒰 (s.1 1))).comp θ)) = 0 := by
      ext ξ
      have hθs : (w ξ) s = ((OModulePresheaf.unit fk).d (𝒰.comap i) 0 (θ ξ)) s := (congrFun (hθ ξ) s).symm
      simp only [LinearMap.add_apply, LinearMap.neg_apply, LinearMap.comp_apply, LinearMap.proj_apply,
        LinearMap.zero_apply]
      erw [hθs]
      rw [OModulePresheaf.d_apply, Fin.sum_univ_two]
      simp only [Fin.val_zero, pow_zero, one_smul, Fin.val_one, pow_one, neg_smul]
      have hf0 : (𝒰.comap i).face s 0 = sing 𝒰 (s.1 1) := face_one_zero 𝒰 s
      have hf1 : (𝒰.comap i).face s 1 = sing 𝒰 (s.1 0) := face_one_one 𝒰 s
      rw [res_idx hf0 (θ ξ) _ hbk, res_idx hf1 (θ ξ) _ hak]
      first
        | module
        | (norm_num; abel)
        | (simp only [neg_one_smul, Int.cast_neg, Int.cast_one, neg_smul, one_smul]; abel)
        | (simp; abel)
    rw [hW0, ← sub_eq_add_neg] at Rsum
    have hD0 : t * (1 + εa) * (1 - εb) - 1 = 0 := by
      rw [hD]
      exact IsFibreReading.eq_zero_of_isFibreReading_zero_of_flat V ι hι f fk i hi _ (haff s) _
        (𝒰.comap_inter_le i s) (𝒰.le_comap_inter i s) _ Rsum
    exact sub_eq_zero.mp hD0
  exact τ₂.nonempty_iso_unit_of_forall_transition_eq_one htriv

end S_AlgebraicGeometry_SmallExtension_nonempty_iso_unit_of_isPicDeformationCocycle_of_forall_mem_range
end P2MW
export P2MW.S_AlgebraicGeometry_SmallExtension_nonempty_iso_unit_of_isPicDeformationCocycle_of_forall_mem_range (solution)
