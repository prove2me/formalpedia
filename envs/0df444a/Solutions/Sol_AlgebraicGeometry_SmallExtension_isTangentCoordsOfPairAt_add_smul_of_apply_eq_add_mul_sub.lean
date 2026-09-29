-- Prove2me | solution 1 for AlgebraicGeometry.SmallExtension.isTangentCoordsOfPairAt_add_smul_of_apply_eq_add_mul_sub
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/88d06065-016e-5543-a3eb-9329ebbd3c02

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_AlgebraicGeometry_SquareZeroDeformation
import Definitions.Def_AlgebraicGeometry_SquareZeroRelTangent
import Definitions.Def_AlgebraicGeometry_SmallExtensionPairTangent
import Definitions.Def_AlgebraicGeometry_TangentCoordsOfPair
import Definitions.Def_AlgebraicGeometry_SmallExtensionTangentCoords
import Definitions.Def_AlgebraicGeometry_TangentCoordsOfPairAt
import Theorems.Thm_AlgebraicGeometry_SmallExtension_existsUnique_isTangentOfPair_of_flat
import Theorems.Thm_AlgebraicGeometry_RelTangentPoints_existsUnique_comp_openInclusion_eq
import Theorems.Thm_AlgebraicGeometry_RelTangentPoints_comp_translate_eq_translate_comp
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_SmallExtension_isTangentCoordsOfPairAt_add_smul_of_apply_eq_add_mul_sub

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 4000000

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry P2MW.S_AlgebraicGeometry_SmallExtension_isTangentCoordsOfPairAt_add_smul_of_apply_eq_add_mul_sub.AlgebraicGeometry TensorProduct IsLocalRing AlgebraicGeometry.SmallExtension P2MW.S_AlgebraicGeometry_SmallExtension_isTangentCoordsOfPairAt_add_smul_of_apply_eq_add_mul_sub.AlgebraicGeometry.SmallExtension NeronModelInfra GoodReductionJacobian"

universe u

noncomputable section

namespace PTSumAux

variable {T' : Type u} [CommRing T'] [IsLocalRing T'] (I : Ideal T')
  (V : Type u) [AddCommGroup V] [Module (ResidueField T') V] [Module (ResidueField T')ᵐᵒᵖ V]
  [IsCentralScalar (ResidueField T') V] [Module T' V] [IsScalarTower T' (ResidueField T') V]
  (ι : V →ₗ[T'] T')
  (C : Type u) [CommRing C] [Algebra T' C]

theorem mem_pairRing_zero_iff (d : C) :
    ((0 : C), d) ∈ pairRing I C ↔ d ∈ I.map (algebraMap T' C) := by
  rw [mem_pairRing]
  simp only [map_zero]
  rw [eq_comm, Ideal.Quotient.eq_zero_iff_mem]

theorem ringHom_pairRing_ext (hιI : LinearMap.range ι = Submodule.restrictScalars T' I)
    {S : Type u} [Semiring S] (f g : pairRing I C →+* S)
    (hdiag : ∀ (a : C) (ha : (a, a) ∈ pairRing I C), f ⟨(a, a), ha⟩ = g ⟨(a, a), ha⟩)
    (hgen : ∀ (v : V) (c : C) (h : ((0 : C), algebraMap T' C (ι v) * c) ∈ pairRing I C),
      f ⟨((0 : C), algebraMap T' C (ι v) * c), h⟩ = g ⟨((0 : C), algebraMap T' C (ι v) * c), h⟩) : f = g := by
  classical
  have hz : ∀ (d : C) (hd : d ∈ I.map (algebraMap T' C)),
      f ⟨((0 : C), d), (mem_pairRing_zero_iff I C d).mpr hd⟩ = g ⟨((0 : C), d), (mem_pairRing_zero_iff I C d).mpr hd⟩ := by
    intro d hd
    induction hd using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨i, hi, rfl⟩ := hx
      have hi' : i ∈ LinearMap.range ι := by rw [hιI]; exact hi
      obtain ⟨w, rfl⟩ := hi'
      have hmem : ((0 : C), algebraMap T' C (ι w) * 1) ∈ pairRing I C := by
        rw [mul_one]; exact (mem_pairRing_zero_iff I C _).mpr (Ideal.mem_map_of_mem _ hi)
      have e : (⟨((0 : C), algebraMap T' C (ι w)), (mem_pairRing_zero_iff I C _).mpr
          (Ideal.subset_span ⟨ι w, hi, rfl⟩)⟩ : pairRing I C) = ⟨((0 : C), algebraMap T' C (ι w) * 1), hmem⟩ := by
        apply Subtype.ext; simp
      rw [e, hgen w 1 hmem]
    | zero =>
      have e : (⟨((0 : C), (0 : C)), (mem_pairRing_zero_iff I C _).mpr (Submodule.zero_mem _)⟩ : pairRing I C) = 0 :=
        Subtype.ext rfl
      rw [e, f.map_zero, g.map_zero]
    | add x y hx hy ihx ihy =>
      have e : (⟨((0 : C), x + y), (mem_pairRing_zero_iff I C _).mpr (Submodule.add_mem _ hx hy)⟩ : pairRing I C) =
          ⟨((0 : C), x), (mem_pairRing_zero_iff I C _).mpr hx⟩ + ⟨((0 : C), y), (mem_pairRing_zero_iff I C _).mpr hy⟩ :=
        Subtype.ext (by simp)
      rw [e, f.map_add, g.map_add, ihx, ihy]
    | smul c x hx ihx =>
      have hc : (c, c) ∈ pairRing I C := by rw [mem_pairRing]
      have e : (⟨((0 : C), c • x), (mem_pairRing_zero_iff I C _).mpr (Submodule.smul_mem _ c hx)⟩ : pairRing I C) =
          ⟨(c, c), hc⟩ * ⟨((0 : C), x), (mem_pairRing_zero_iff I C _).mpr hx⟩ :=
        Subtype.ext (by simp [smul_eq_mul])
      rw [e, f.map_mul, g.map_mul, hdiag c hc, ihx]
  apply RingHom.ext
  rintro ⟨⟨a, b⟩, hab⟩
  have hba : b - a ∈ I.map (algebraMap T' C) := by
    rw [mem_pairRing] at hab
    exact (Ideal.Quotient.eq.mp hab.symm)
  have haa : (a, a) ∈ pairRing I C := by rw [mem_pairRing]
  have e : (⟨(a, b), hab⟩ : pairRing I C) =
      ⟨(a, a), haa⟩ + ⟨((0 : C), b - a), (mem_pairRing_zero_iff I C _).mpr hba⟩ :=
    Subtype.ext (by simp)
  rw [e, f.map_add, g.map_add, hdiag a haa, hz (b - a) hba]

theorem schlessinger_unique (hιI : LinearMap.range ι = Submodule.restrictScalars T' I)
    (ϑ ϑ' : pairRing I C →+* thickening T' V C)
    (h : IsSchlessingerMap I V ι C ϑ) (h' : IsSchlessingerMap I V ι C ϑ') : ϑ = ϑ' :=
  ringHom_pairRing_ext I V ι C hιI (S := thickening T' V C) ϑ ϑ' (fun a ha => (h.1 a ha).trans (h'.1 a ha).symm)
    (fun v c hh => (h.2 v c hh).trans (h'.2 v c hh).symm)

theorem toReduction_eq_of_mem_pairRing (hI : I ≤ maximalIdeal T') {a b : C} (hab : (a, b) ∈ pairRing I C) :
    toReduction T' C a = toReduction T' C b := by
  have hle : I.map (algebraMap T' C) ≤ RingHom.ker (toReduction T' C) := by
    rw [Ideal.map_le_iff_le_comap]
    intro t ht
    rw [Ideal.mem_comap, RingHom.mem_ker]
    change (1 : ResidueField T') ⊗ₜ[T'] (algebraMap T' C t) = 0
    rw [Algebra.algebraMap_eq_smul_one, TensorProduct.tmul_smul, TensorProduct.smul_tmul', Algebra.smul_def,
      mul_one, IsLocalRing.ResidueField.algebraMap_eq, (IsLocalRing.residue_eq_zero_iff t).mpr (hI ht),
      TensorProduct.zero_tmul]
  rw [mem_pairRing] at hab
  have h2 : a - b ∈ I.map (algebraMap T' C) := Ideal.Quotient.eq.mp hab
  have := hle h2
  rwa [RingHom.mem_ker, map_sub, sub_eq_zero] at this

section Tensor

variable (W : Type u) [AddCommGroup W] [Module (ResidueField T') W] [Module (ResidueField T')ᵐᵒᵖ W]
  [IsCentralScalar (ResidueField T') W]
  (W' : Type u) [AddCommGroup W'] [Module (ResidueField T') W'] [Module (ResidueField T')ᵐᵒᵖ W']
  [IsCentralScalar (ResidueField T') W']

variable (T') in

def proj : thickening T' W C →ₐ[ResidueField T'] (ResidueField T' ⊗[T'] C) :=
  Algebra.TensorProduct.lift (AlgHom.id (ResidueField T') (ResidueField T' ⊗[T'] C))
    ((Algebra.ofId (ResidueField T') (ResidueField T' ⊗[T'] C)).comp
      (TrivSqZeroExt.fstHom (ResidueField T') (ResidueField T') W))
    (fun _ _ => Commute.all _ _)

theorem proj_tmul (c : ResidueField T' ⊗[T'] C) (t : TrivSqZeroExt (ResidueField T') W) :
    proj T' C W (c ⊗ₜ t) = c * algebraMap (ResidueField T') (ResidueField T' ⊗[T'] C) t.fst := by
  rw [proj, Algebra.TensorProduct.lift_tmul]
  rfl

variable (T') in

def sigma : (ResidueField T' ⊗[T'] C) ⊗[ResidueField T'] W →ₗ[ResidueField T'] thickening T' W C :=
  TensorProduct.map LinearMap.id (TrivSqZeroExt.inrHom (ResidueField T') W)

theorem sigma_tmul (c : ResidueField T' ⊗[T'] C) (w : W) :
    sigma T' C W (c ⊗ₜ w) = c ⊗ₜ (TrivSqZeroExt.inr w : TrivSqZeroExt (ResidueField T') W) := by
  rw [sigma, TensorProduct.map_tmul]
  rfl

theorem vPart_tmul (c : ResidueField T' ⊗[T'] C) (t : TrivSqZeroExt (ResidueField T') W) :
    vPart T' W C (c ⊗ₜ t) = c ⊗ₜ t.snd := by
  rw [vPart, TensorProduct.map_tmul]
  rfl

theorem smul_tmul_one_eq (c : ResidueField T' ⊗[T'] C) (r : ResidueField T') :
    (c * algebraMap (ResidueField T') (ResidueField T' ⊗[T'] C) r) ⊗ₜ[ResidueField T'] (1 : TrivSqZeroExt (ResidueField T') W) =
      c ⊗ₜ (TrivSqZeroExt.inl r : TrivSqZeroExt (ResidueField T') W) := by
  rw [mul_comm, ← Algebra.smul_def, TensorProduct.smul_tmul, Algebra.smul_def, mul_one, TrivSqZeroExt.algebraMap_eq_inl]

theorem decomp (e : thickening T' W C) :
    Algebra.TensorProduct.includeLeftRingHom (proj T' C W e) + sigma T' C W (vPart T' W C e) = e := by
  induction e using TensorProduct.induction_on with
  | zero => simp
  | tmul c t =>
    rw [proj_tmul, vPart_tmul, sigma_tmul, Algebra.TensorProduct.includeLeftRingHom_apply, smul_tmul_one_eq,
      ← TensorProduct.tmul_add, TrivSqZeroExt.inl_fst_add_inr_snd_eq]
  | add x y hx hy =>
    simp only [map_add]
    rw [add_add_add_comm, hx, hy]

variable (T') in

private abbrev _root_.PTSumAux.jmap (f : W' →ₗ[ResidueField T'] W) : thickening T' W' C →ₐ[ResidueField T'] thickening T' W C :=
  Algebra.TensorProduct.map (AlgHom.id (ResidueField T') (ResidueField T' ⊗[T'] C)) (TrivSqZeroExt.map f)

p2m_export "PTSumAux" "jmap"
theorem jmap_tmul (f : W' →ₗ[ResidueField T'] W) (c : ResidueField T' ⊗[T'] C) (t : TrivSqZeroExt (ResidueField T') W') :
    jmap T' C W W' f (c ⊗ₜ t) = c ⊗ₜ TrivSqZeroExt.map f t := by
  rw [jmap, Algebra.TensorProduct.map_tmul]
  rfl

theorem map_inr (f : W' →ₗ[ResidueField T'] W) (w : W') :
    TrivSqZeroExt.map f (TrivSqZeroExt.inr w : TrivSqZeroExt (ResidueField T') W') = TrivSqZeroExt.inr (f w) := by
  apply TrivSqZeroExt.ext
  · rw [TrivSqZeroExt.fst_map, TrivSqZeroExt.fst_inr, TrivSqZeroExt.fst_inr]
  · rw [TrivSqZeroExt.snd_map, TrivSqZeroExt.snd_inr, TrivSqZeroExt.snd_inr]

theorem vPart_jmap (f : W' →ₗ[ResidueField T'] W) (e : thickening T' W' C) :
    vPart T' W C (jmap T' C W W' f e) = LinearMap.lTensor (ResidueField T' ⊗[T'] C) f (vPart T' W' C e) := by
  induction e using TensorProduct.induction_on with
  | zero => simp
  | tmul c t => rw [jmap_tmul, vPart_tmul, vPart_tmul, LinearMap.lTensor_tmul, TrivSqZeroExt.snd_map]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem proj_jmap (f : W' →ₗ[ResidueField T'] W) (e : thickening T' W' C) :
    proj T' C W (jmap T' C W W' f e) = proj T' C W' e := by
  induction e using TensorProduct.induction_on with
  | zero => simp
  | tmul c t => rw [jmap_tmul, proj_tmul, proj_tmul, TrivSqZeroExt.fst_map]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem jmap_includeLeft (f : W' →ₗ[ResidueField T'] W) (c : ResidueField T' ⊗[T'] C) :
    jmap T' C W W' f (Algebra.TensorProduct.includeLeftRingHom c) = Algebra.TensorProduct.includeLeftRingHom c := by
  rw [Algebra.TensorProduct.includeLeftRingHom_apply, Algebra.TensorProduct.includeLeftRingHom_apply, jmap_tmul, map_one]

theorem jmap_sigma (f : W' →ₗ[ResidueField T'] W) (m : (ResidueField T' ⊗[T'] C) ⊗[ResidueField T'] W') :
    jmap T' C W W' f (sigma T' C W' m) = sigma T' C W (LinearMap.lTensor (ResidueField T' ⊗[T'] C) f m) := by
  induction m using TensorProduct.induction_on with
  | zero => simp
  | tmul c w => rw [sigma_tmul, jmap_tmul, map_inr, LinearMap.lTensor_tmul, sigma_tmul]
  | add x y hx hy => simp only [map_add, hx, hy]

end Tensor

section Double

theorem lTensor_fst_mix (m₁ m₂ : (ResidueField T' ⊗[T'] C) ⊗[ResidueField T'] V) :
    LinearMap.lTensor (ResidueField T' ⊗[T'] C) (LinearMap.fst (ResidueField T') V V)
      (LinearMap.lTensor (ResidueField T' ⊗[T'] C) (LinearMap.inl (ResidueField T') V V) m₁ + LinearMap.lTensor (ResidueField T' ⊗[T'] C) (LinearMap.inr (ResidueField T') V V) m₂) = m₁ := by
  rw [map_add, ← LinearMap.comp_apply, ← LinearMap.lTensor_comp, LinearMap.fst_comp_inl, LinearMap.lTensor_id,
    ← LinearMap.comp_apply, ← LinearMap.lTensor_comp, LinearMap.fst_comp_inr, LinearMap.lTensor_zero]
  simp

theorem lTensor_snd_mix (m₁ m₂ : (ResidueField T' ⊗[T'] C) ⊗[ResidueField T'] V) :
    LinearMap.lTensor (ResidueField T' ⊗[T'] C) (LinearMap.snd (ResidueField T') V V)
      (LinearMap.lTensor (ResidueField T' ⊗[T'] C) (LinearMap.inl (ResidueField T') V V) m₁ + LinearMap.lTensor (ResidueField T' ⊗[T'] C) (LinearMap.inr (ResidueField T') V V) m₂) = m₂ := by
  rw [map_add, ← LinearMap.comp_apply, ← LinearMap.lTensor_comp, LinearMap.snd_comp_inl, LinearMap.lTensor_zero,
    ← LinearMap.comp_apply, ← LinearMap.lTensor_comp, LinearMap.snd_comp_inr, LinearMap.lTensor_id]
  simp

theorem eq_zero_of_lTensor_fst_snd (m : (ResidueField T' ⊗[T'] C) ⊗[ResidueField T'] (V × V))
    (h₁ : LinearMap.lTensor (ResidueField T' ⊗[T'] C) (LinearMap.fst (ResidueField T') V V) m = 0)
    (h₂ : LinearMap.lTensor (ResidueField T' ⊗[T'] C) (LinearMap.snd (ResidueField T') V V) m = 0) : m = 0 := by
  have hid : (LinearMap.inl (ResidueField T') V V).comp (LinearMap.fst (ResidueField T') V V) +
      (LinearMap.inr (ResidueField T') V V).comp (LinearMap.snd (ResidueField T') V V) = LinearMap.id := by
    apply LinearMap.ext
    rintro ⟨v₁, v₂⟩
    simp
  have : m = LinearMap.lTensor (ResidueField T' ⊗[T'] C) (LinearMap.inl (ResidueField T') V V) (LinearMap.lTensor (ResidueField T' ⊗[T'] C) (LinearMap.fst (ResidueField T') V V) m) +
      LinearMap.lTensor (ResidueField T' ⊗[T'] C) (LinearMap.inr (ResidueField T') V V) (LinearMap.lTensor (ResidueField T' ⊗[T'] C) (LinearMap.snd (ResidueField T') V V) m) := by
    conv_lhs => rw [← LinearMap.id_apply (R := ResidueField T') m, ← LinearMap.lTensor_id, ← hid]
    rw [LinearMap.lTensor_add, LinearMap.add_apply, LinearMap.lTensor_comp, LinearMap.lTensor_comp, LinearMap.comp_apply,
      LinearMap.comp_apply]
  rw [this, h₁, h₂, map_zero, map_zero, add_zero]

variable (T') in

abbrev Psi : thickening T' (V × V) C →+* thickening T' V C × thickening T' V C :=
  RingHom.prod (jmap T' C V (V × V) (LinearMap.fst (ResidueField T') V V)).toRingHom
    (jmap T' C V (V × V) (LinearMap.snd (ResidueField T') V V)).toRingHom

theorem Psi_eq_zero (e : thickening T' (V × V) C) (he : Psi T' V C e = 0) : e = 0 := by
  have h₁ : jmap T' C V (V × V) (LinearMap.fst (ResidueField T') V V) e = 0 := congrArg Prod.fst he
  have h₂ : jmap T' C V (V × V) (LinearMap.snd (ResidueField T') V V) e = 0 := congrArg Prod.snd he
  have hp : proj T' C (V × V) e = 0 := by
    rw [← proj_jmap C V (V × V) (LinearMap.fst (ResidueField T') V V) e, h₁, map_zero]
  have hv : vPart T' (V × V) C e = 0 := by
    apply eq_zero_of_lTensor_fst_snd
    · rw [← vPart_jmap, h₁, map_zero]
    · rw [← vPart_jmap, h₂, map_zero]
  rw [← decomp C (V × V) e, hp, hv, map_zero, map_zero, add_zero]

theorem Psi_injective : Function.Injective (Psi T' V C) := fun a b h =>
  sub_eq_zero.1 (Psi_eq_zero V C (a - b) (by rw [map_sub, h, sub_self]))

theorem jmap_add_eq (e : thickening T' (V × V) C) :
    jmap T' C V (V × V) (LinearMap.fst (ResidueField T') V V + LinearMap.snd (ResidueField T') V V) e =
      jmap T' C V (V × V) (LinearMap.fst (ResidueField T') V V) e + jmap T' C V (V × V) (LinearMap.snd (ResidueField T') V V) e -
        Algebra.TensorProduct.includeLeftRingHom (proj T' C (V × V) e) := by
  induction e using TensorProduct.induction_on with
  | zero => simp
  | tmul c t =>
    rw [jmap_tmul, jmap_tmul, jmap_tmul, proj_tmul, Algebra.TensorProduct.includeLeftRingHom_apply, smul_tmul_one_eq,
      ← TensorProduct.tmul_add, ← TensorProduct.tmul_sub]
    congr 1
    apply TrivSqZeroExt.ext
    · simp [TrivSqZeroExt.fst_map]
    · simp [TrivSqZeroExt.snd_map]
  | add x y hx hy =>
    simp only [map_add, hx, hy]
    abel

end Double

end PTSumAux

namespace PTSumAux

variable {T' : Type u} [CommRing T'] [IsLocalRing T']
  (V : Type u) [AddCommGroup V] [Module (ResidueField T') V] [Module (ResidueField T')ᵐᵒᵖ V]
  [IsCentralScalar (ResidueField T') V] [Module T' V] [IsScalarTower T' (ResidueField T') V]
  (C : Type u) [CommRing C] [Algebra T' C]
  {R : Type u} [CommRing R] (g₁ g₂ : R →+* thickening T' V C)

theorem proj_schlessinger_apply (I : Ideal T') (ι : V →ₗ[T'] T') (hιI : LinearMap.range ι = Submodule.restrictScalars T' I)
    (ϑ : pairRing I C →+* thickening T' V C) (hϑ : IsSchlessingerMap I V ι C ϑ) (q : pairRing I C) :
    proj T' C V (ϑ q) = toReduction T' C ((q : C × C).1) := by
  have key : (proj T' C V).toRingHom.comp ϑ = (toReduction T' C).comp (pairFst I C) := by
    apply ringHom_pairRing_ext I V ι C hιI
    · intro a ha
      change proj T' C V (ϑ ⟨(a, a), ha⟩) = toReduction T' C a
      rw [hϑ.1 a ha, proj_tmul, TrivSqZeroExt.fst_one, map_one, mul_one]
    · intro v c h
      change proj T' C V (ϑ ⟨_, h⟩) = toReduction T' C 0
      rw [hϑ.2 v c h, proj_tmul, TrivSqZeroExt.fst_inr, map_zero, mul_zero, map_zero]
  exact congrArg (fun f : pairRing I C →+* ResidueField T' ⊗[T'] C => f q) key

def GlueFun (x : R) : thickening T' (V × V) C :=
  Algebra.TensorProduct.includeLeftRingHom (proj T' C V (g₁ x)) +
    sigma T' C (V × V)
      (LinearMap.lTensor (ResidueField T' ⊗[T'] C) (LinearMap.inl (ResidueField T') V V) (vPart T' V C (g₁ x)) +
        LinearMap.lTensor (ResidueField T' ⊗[T'] C) (LinearMap.inr (ResidueField T') V V) (vPart T' V C (g₂ x)))

theorem Psi_GlueFun (hg : ∀ x, proj T' C V (g₁ x) = proj T' C V (g₂ x)) (x : R) :
    Psi T' V C (GlueFun V C g₁ g₂ x) = (g₁ x, g₂ x) := by
  apply Prod.ext
  · change jmap T' C V (V × V) (LinearMap.fst (ResidueField T') V V) (GlueFun V C g₁ g₂ x) = g₁ x
    rw [GlueFun, map_add, jmap_includeLeft, jmap_sigma, lTensor_fst_mix, decomp]
  · change jmap T' C V (V × V) (LinearMap.snd (ResidueField T') V V) (GlueFun V C g₁ g₂ x) = g₂ x
    rw [GlueFun, map_add, jmap_includeLeft, jmap_sigma, lTensor_snd_mix, hg, decomp]

def Glue (hg : ∀ x, proj T' C V (g₁ x) = proj T' C V (g₂ x)) : R →+* thickening T' (V × V) C where
  toFun := GlueFun V C g₁ g₂
  map_one' := Psi_injective V C (by
    rw [Psi_GlueFun V C g₁ g₂ hg, g₁.map_one, g₂.map_one, (Psi T' V C).map_one]; rfl)
  map_mul' p q := Psi_injective V C (by
    rw [Psi_GlueFun V C g₁ g₂ hg, (Psi T' V C).map_mul, Psi_GlueFun V C g₁ g₂ hg, Psi_GlueFun V C g₁ g₂ hg,
      g₁.map_mul, g₂.map_mul]; rfl)
  map_zero' := Psi_injective V C (by
    rw [Psi_GlueFun V C g₁ g₂ hg, g₁.map_zero, g₂.map_zero, (Psi T' V C).map_zero]; rfl)
  map_add' p q := Psi_injective V C (by
    rw [Psi_GlueFun V C g₁ g₂ hg, (Psi T' V C).map_add, Psi_GlueFun V C g₁ g₂ hg, Psi_GlueFun V C g₁ g₂ hg,
      g₁.map_add, g₂.map_add]; rfl)

theorem Glue_fst (hg : ∀ x, proj T' C V (g₁ x) = proj T' C V (g₂ x)) (x : R) :
    jmap T' C V (V × V) (LinearMap.fst (ResidueField T') V V) (Glue V C g₁ g₂ hg x) = g₁ x :=
  congrArg Prod.fst (Psi_GlueFun V C g₁ g₂ hg x)

theorem Glue_snd (hg : ∀ x, proj T' C V (g₁ x) = proj T' C V (g₂ x)) (x : R) :
    jmap T' C V (V × V) (LinearMap.snd (ResidueField T') V V) (Glue V C g₁ g₂ hg x) = g₂ x :=
  congrArg Prod.snd (Psi_GlueFun V C g₁ g₂ hg x)

theorem proj_Glue (hg : ∀ x, proj T' C V (g₁ x) = proj T' C V (g₂ x)) (x : R) :
    proj T' C (V × V) (Glue V C g₁ g₂ hg x) = proj T' C V (g₁ x) := by
  rw [← proj_jmap C V (V × V) (LinearMap.fst (ResidueField T') V V), Glue_fst]

theorem jmap_add_smul_eq (r : ResidueField T') (e : thickening T' (V × V) C) :
    jmap T' C V (V × V) (LinearMap.fst (ResidueField T') V V + r • LinearMap.snd (ResidueField T') V V) e =
      jmap T' C V (V × V) (LinearMap.fst (ResidueField T') V V) e +
        r • (jmap T' C V (V × V) (LinearMap.snd (ResidueField T') V V) e -
          Algebra.TensorProduct.includeLeftRingHom (proj T' C (V × V) e)) := by
  induction e using TensorProduct.induction_on with
  | zero => simp
  | tmul c t =>
    rw [jmap_tmul, jmap_tmul, jmap_tmul, proj_tmul, Algebra.TensorProduct.includeLeftRingHom_apply, smul_tmul_one_eq,
      ← TensorProduct.tmul_sub, ← TensorProduct.tmul_smul, ← TensorProduct.tmul_add]
    congr 1
    apply TrivSqZeroExt.ext
    · simp [TrivSqZeroExt.fst_map]
    · simp [TrivSqZeroExt.snd_map]
  | add x y hx hy =>
    simp only [map_add, hx, hy, smul_add, smul_sub]
    abel

end PTSumAux

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Spec.map_comp Scheme.Hom Spec Spec.map Scheme Scheme.Hom.comp_appTop Flat Spec.map_id IsAffineOpen Scheme.ΓSpecIso_naturality SquareZero.toBase SquareZero.specMap SquareZero.specMap_toBase SquareZero.basePoint_specMap SquareZero.zeroSection SquareZero.zeroSection_fst SquareZero.zeroSection_snd RelTangentPoints SquareZero.zeroSection_snd_assoc RelTangentPoints.base RelTangentPoints.translate RelTangentPoints.existsUnique_comp_openInclusion_eq RelTangentPoints.comp_translate_eq_translate_comp"
namespace SmallExtension
p2m_export "AlgebraicGeometry.SmallExtension" "pairRing mem_pairRing pairFst pairSnd thickening toReduction IsSchlessingerMap IsTangentOfPair reductionBase thickeningFst thickeningSnd thickening_isPullback vPart tensorToDualHom tensorToDualHom_tmul tangentCoords tangentCoords_apply chartRingHom IsTangentCoordsOfPairAt existsUnique_isTangentOfPair_of_flat"
namespace CoordsAlphaAux
p2m_open "AlgebraicGeometry.SmallExtension AlgebraicGeometry"

variable {T' : Type u} [CommRing T'] [IsLocalRing T']
  (V : Type u) [AddCommGroup V] [Module (ResidueField T') V] [Module (ResidueField T')ᵐᵒᵖ V]
  [IsCentralScalar (ResidueField T') V] [Module T' V] [IsScalarTower T' (ResidueField T') V]
  (C : Type u) [CommRing C] [Algebra T' C]

variable (T') in

private abbrev _root_.AlgebraicGeometry.SmallExtension.CoordsAlphaAux.jmap (f : (V × V) →ₗ[ResidueField T'] V) :
    thickening T' (V × V) C →ₐ[ResidueField T'] thickening T' V C :=
  Algebra.TensorProduct.map (AlgHom.id (ResidueField T') (ResidueField T' ⊗[T'] C)) (TrivSqZeroExt.map f)

p2m_export "AlgebraicGeometry.SmallExtension.CoordsAlphaAux" "jmap"
variable (T') in

abbrev jSpec (f : (V × V) →ₗ[ResidueField T'] V) :
    Spec (CommRingCat.of (thickening T' V C)) ⟶ Spec (CommRingCat.of (thickening T' (V × V) C)) :=
  Spec.map (CommRingCat.ofHom (jmap T' V C f).toRingHom)

theorem jSpec_thickeningFst (f : (V × V) →ₗ[ResidueField T'] V) :
    jSpec T' V C f ≫ thickeningFst T' (V × V) C = thickeningFst T' V C := by
  rw [jSpec, thickeningFst, thickeningFst, ← Spec.map_comp]
  congr 1
  all_goals
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro c
    change jmap T' V C f (Algebra.TensorProduct.includeLeftRingHom c) = Algebra.TensorProduct.includeLeftRingHom c
    simp [Algebra.TensorProduct.includeLeftRingHom_apply, jmap, Algebra.TensorProduct.map_tmul]

theorem jSpec_thickeningSnd (f : (V × V) →ₗ[ResidueField T'] V) :
    jSpec T' V C f ≫ thickeningSnd T' (V × V) C = thickeningSnd T' V C ≫ SquareZero.specMap (ResidueField T') f := by
  rw [jSpec, thickeningSnd, thickeningSnd, SquareZero.specMap, ← Spec.map_comp, ← Spec.map_comp]
  congr 1

theorem jSpec_base (f : (V × V) →ₗ[ResidueField T'] V) :
    jSpec T' V C f ≫ RelTangentPoints.base (V × V) (thickeningSnd T' (V × V) C) =
      RelTangentPoints.base V (thickeningSnd T' V C) := by
  rw [RelTangentPoints.base, RelTangentPoints.base, ← Category.assoc, jSpec_thickeningSnd, Category.assoc,
    SquareZero.specMap_toBase]

theorem zeroSection_jSpec (f : (V × V) →ₗ[ResidueField T'] V) :
    SquareZero.zeroSection V (reductionBase T' C) (thickeningFst T' V C) (thickeningSnd T' V C) (thickening_isPullback V C) ≫
        jSpec T' V C f =
      SquareZero.zeroSection (V × V) (reductionBase T' C) (thickeningFst T' (V × V) C) (thickeningSnd T' (V × V) C)
        (thickening_isPullback (V × V) C) := by
  apply (thickening_isPullback (V × V) C).hom_ext
  · rw [Category.assoc, jSpec_thickeningFst, SquareZero.zeroSection_fst, SquareZero.zeroSection_fst]
  · rw [Category.assoc, jSpec_thickeningSnd, SquareZero.zeroSection_snd_assoc, SquareZero.zeroSection_snd,
      SquareZero.basePoint_specMap]

theorem chartRingHom_jSpec_comp {Ak : Scheme.{u}} (Ue : Ak.Opens) (f : (V × V) →ₗ[ResidueField T'] V)
    (w : Spec (CommRingCat.of (thickening T' (V × V) C)) ⟶ (Ue : Scheme.{u})) :
    chartRingHom V C Ue (jSpec T' V C f ≫ w) = (jmap T' V C f).toRingHom.comp (chartRingHom (V × V) C Ue w) := by
  simp only [chartRingHom, jSpec, Scheme.Hom.comp_appTop, Category.assoc]
  rw [Scheme.ΓSpecIso_naturality]
  simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom]
  rfl

end AlgebraicGeometry.SmallExtension.CoordsAlphaAux

end

open PTSumAux AlgebraicGeometry.SmallExtension.CoordsAlphaAux in
theorem solution
    {T' : Type u} [CommRing T'] [IsLocalRing T'] [IsArtinianRing T']
    (I : Ideal T') (hI : I ≤ maximalIdeal T') (hsmall : I * maximalIdeal T' = ⊥)
    (V : Type u) [AddCommGroup V] [Module (ResidueField T') V] [Module (ResidueField T')ᵐᵒᵖ V]
    [IsCentralScalar (ResidueField T') V] [Module.Finite (ResidueField T') V]
    [Module T' V] [IsScalarTower T' (ResidueField T') V]
    (ι : V →ₗ[T'] T') (hι : Function.Injective ι) (hιI : LinearMap.range ι = Submodule.restrictScalars T' I)
    (C : Type u) [CommRing C] [Algebra T' C] [Module.Flat T' C]
    {Y : Scheme.{u}} (qY : Y ⟶ Spec (CommRingCat.of T'))
    (u : Spec (CommRingCat.of C) ⟶ Y) (hu : u ≫ qY = Spec.map (CommRingCat.ofHom (algebraMap T' C)))
    {Ak : Scheme.{u}} (xk : Ak ⟶ Spec (CommRingCat.of (ResidueField T'))) (Lk : RelativeGroupLaw (ResidueField T') xk)
    (ak : Ak ⟶ Y) (hak : IsPullback ak xk qY (Spec.map (CommRingCat.ofHom (residue T'))))
    (Ue : Ak.Opens) (hUe : IsAffineOpen Ue)
    (e₁ : Spec (CommRingCat.of (ResidueField T')) ⟶ (Ue : Scheme.{u})) (he₁ : e₁ ≫ Ue.ι = (Lk.one (𝟙 _)).1)
    (r : ResidueField T') (ar : T') (har : residue T' ar = r)
    (ψ ψ' ψ'' : C →ₐ[T'] C)
    (hψ : ∀ x : C, Ideal.Quotient.mk (I.map (algebraMap T' C)) (ψ x) = Ideal.Quotient.mk (I.map (algebraMap T' C)) x)
    (hψ' : ∀ x : C, Ideal.Quotient.mk (I.map (algebraMap T' C)) (ψ' x) = Ideal.Quotient.mk (I.map (algebraMap T' C)) x)
    (hψ'' : ∀ x : C, ψ'' x = ψ x + algebraMap T' C ar * (ψ' x - x))
    (c c' : Γ(Ak, Ue) → (Module.Dual (ResidueField T') V →ₗ[ResidueField T'] (ResidueField T' ⊗[T'] C)))
    (hc : IsTangentCoordsOfPairAt I V ι C u (Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ u) xk Lk ak Ue c)
    (hc' : IsTangentCoordsOfPairAt I V ι C u (Spec.map (CommRingCat.ofHom ψ'.toRingHom) ≫ u) xk Lk ak Ue c') :
    IsTangentCoordsOfPairAt I V ι C u (Spec.map (CommRingCat.ofHom ψ''.toRingHom) ≫ u) xk Lk ak Ue (c + r • c')  := by
  classical
  obtain ⟨a0, ha0, a1, hat, hatr, hac⟩ := hc
  obtain ⟨b0, hb0, b1, hbt, hbtr, hbc⟩ := hc'

  obtain ⟨ϑ, hϑ, φa, hφa1, hφa2, hwa⟩ := hat
  obtain ⟨ϑ', hϑ', φb, hφb1, hφb2, hwb⟩ := hbt
  obtain rfl : ϑ = ϑ' := schlessinger_unique I V ι C hιI ϑ ϑ' hϑ hϑ'
  let k := ResidueField T'
  let fst : (V × V) →ₗ[k] V := LinearMap.fst k V V
  let snd : (V × V) →ₗ[k] V := LinearMap.snd k V V
  let f : (V × V) →ₗ[k] V := LinearMap.fst k V V + r • LinearMap.snd k V V

  have hψ''mod : ∀ x : C, Ideal.Quotient.mk (I.map (algebraMap T' C)) (ψ'' x) = Ideal.Quotient.mk (I.map (algebraMap T' C)) x := by
    intro x
    rw [hψ'' x, map_add, map_mul, map_sub, hψ x, hψ' x, sub_self, mul_zero, add_zero]
  have hsec : ∀ (χ : C →ₐ[T'] C),
      (∀ x : C, Ideal.Quotient.mk (I.map (algebraMap T' C)) (χ x) = Ideal.Quotient.mk (I.map (algebraMap T' C)) x) →
      ∃ m : C →+* pairRing I C, (pairFst I C).comp m = RingHom.id C ∧ (pairSnd I C).comp m = χ.toRingHom := by
    intro χ hχ
    refine ⟨((RingHom.id C).prod χ.toRingHom).codRestrict (pairRing I C) (fun x => ?_), RingHom.ext fun _ => rfl,
      RingHom.ext fun _ => rfl⟩
    rw [mem_pairRing]
    exact (hχ x).symm
  obtain ⟨m, hm1, hm2⟩ := hsec ψ hψ
  obtain ⟨m', hm'1, hm'2⟩ := hsec ψ' hψ'
  obtain ⟨m'', hm''1, hm''2⟩ := hsec ψ'' hψ''mod
  have hm_apply : ∀ x, (m x : C × C) = (x, ψ x) := fun x =>
    Prod.ext (congrArg (fun g : C →+* C => g x) hm1) (congrArg (fun g : C →+* C => g x) hm2)
  have hm'_apply : ∀ x, (m' x : C × C) = (x, ψ' x) := fun x =>
    Prod.ext (congrArg (fun g : C →+* C => g x) hm'1) (congrArg (fun g : C →+* C => g x) hm'2)
  have hm''_apply : ∀ x, (m'' x : C × C) = (x, ψ'' x) := fun x =>
    Prod.ext (congrArg (fun g : C →+* C => g x) hm''1) (congrArg (fun g : C →+* C => g x) hm''2)

  have hpair : ∀ (χ : C →ₐ[T'] C) (mχ : C →+* pairRing I C),
      (pairFst I C).comp mχ = RingHom.id C → (pairSnd I C).comp mχ = χ.toRingHom →
      IsTangentOfPair I V ι C u (Spec.map (CommRingCat.ofHom χ.toRingHom) ≫ u)
        (Spec.map (CommRingCat.ofHom (ϑ.comp mχ)) ≫ u) := by
    intro χ mχ h1 h2
    refine ⟨ϑ, hϑ, Spec.map (CommRingCat.ofHom mχ) ≫ u, ?_, ?_, ?_⟩
    · rw [← Category.assoc, ← Spec.map_comp]
      change Spec.map (CommRingCat.ofHom ((pairFst I C).comp mχ)) ≫ u = u
      rw [h1, CommRingCat.ofHom_id]
      rw [Spec.map_id, Category.id_comp]
    · rw [← Category.assoc, ← Spec.map_comp]
      change Spec.map (CommRingCat.ofHom ((pairSnd I C).comp mχ)) ≫ u = _
      rw [h2]
    · rw [← Category.assoc, ← Spec.map_comp]; rfl

  have hvq : ∀ (χ : C →ₐ[T'] C), (Spec.map (CommRingCat.ofHom χ.toRingHom) ≫ u) ≫ qY = Spec.map (CommRingCat.ofHom (algebraMap T' C)) := by
    intro χ
    rw [Category.assoc, hu, ← Spec.map_comp]
    congr 1
    apply CommRingCat.hom_ext
    exact χ.comp_algebraMap
  have hvmod : ∀ (χ : C →ₐ[T'] C),
      (∀ x : C, Ideal.Quotient.mk (I.map (algebraMap T' C)) (χ x) = Ideal.Quotient.mk (I.map (algebraMap T' C)) x) →
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I.map (algebraMap T' C)))) ≫ u
        = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I.map (algebraMap T' C)))) ≫
          Spec.map (CommRingCat.ofHom χ.toRingHom) ≫ u := by
    intro χ hχ
    rw [← Category.assoc, ← Spec.map_comp]
    congr 2
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro x
    exact (hχ x).symm

  have ha0' : a0 ≫ ak = Spec.map (CommRingCat.ofHom (ϑ.comp m)) ≫ u :=
    (existsUnique_isTangentOfPair_of_flat I hI hsmall V ι hι hιI C qY u hu _ (hvq ψ) (hvmod ψ hψ)).unique
      ⟨ϑ, hϑ, φa, hφa1, hφa2, hwa⟩ (hpair ψ m hm1 hm2)
  have hb0' : b0 ≫ ak = Spec.map (CommRingCat.ofHom (ϑ.comp m')) ≫ u :=
    (existsUnique_isTangentOfPair_of_flat I hI hsmall V ι hι hιI C qY u hu _ (hvq ψ') (hvmod ψ' hψ')).unique
      ⟨ϑ, hϑ', φb, hφb1, hφb2, hwb⟩ (hpair ψ' m' hm'1 hm'2)

  have hproj : ∀ x, proj T' C V ((ϑ.comp m) x) = proj T' C V ((ϑ.comp m') x) := by
    intro x
    rw [RingHom.comp_apply, RingHom.comp_apply, proj_schlessinger_apply V C I ι hιI ϑ hϑ, proj_schlessinger_apply V C I ι hιI ϑ hϑ,
      hm_apply, hm'_apply]
  let D : C →+* thickening T' (V × V) C := Glue V C (ϑ.comp m) (ϑ.comp m') hproj
  have hDf : (jmap T' V C fst).toRingHom.comp D = ϑ.comp m := RingHom.ext fun x => Glue_fst V C _ _ hproj x
  have hDs : (jmap T' V C snd).toRingHom.comp D = ϑ.comp m' := RingHom.ext fun x => Glue_snd V C _ _ hproj x

  have hred : toReduction T' C (algebraMap T' C ar) = algebraMap (ResidueField T') (ResidueField T' ⊗[T'] C) r := by
    change (1 : ResidueField T') ⊗ₜ[T'] algebraMap T' C ar = algebraMap (ResidueField T') (ResidueField T' ⊗[T'] C) r
    rw [Algebra.algebraMap_eq_smul_one (A := C) ar, TensorProduct.tmul_smul, TensorProduct.smul_tmul', Algebra.smul_def, mul_one,
      IsLocalRing.ResidueField.algebraMap_eq, har, Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
  have hDa : (jmap T' V C f).toRingHom.comp D = ϑ.comp m'' := by
    apply RingHom.ext
    intro x
    change jmap T' V C f (D x) = ϑ (m'' x)
    have e3 : jmap T' V C f (D x) = PTSumAux.jmap T' C V (V × V) (LinearMap.fst k V V + r • LinearMap.snd k V V) (D x) := rfl
    rw [e3, PTSumAux.jmap_add_smul_eq, Glue_fst, Glue_snd, proj_Glue, RingHom.comp_apply, RingHom.comp_apply,
      proj_schlessinger_apply V C I ι hιI ϑ hϑ, hm_apply]

    have hxx : (x, x) ∈ pairRing I C := by rw [mem_pairRing]
    have hdiff : ((0 : C), ψ' x - x) ∈ pairRing I C := by
      rw [PTSumAux.mem_pairRing_zero_iff, ← Ideal.Quotient.eq, hψ' x]
    have hadiff : ((0 : C), algebraMap T' C ar * (ψ' x - x)) ∈ pairRing I C := by
      rw [PTSumAux.mem_pairRing_zero_iff, ← Ideal.Quotient.eq_zero_iff_mem, map_mul,
        Ideal.Quotient.eq_zero_iff_mem.mpr ((PTSumAux.mem_pairRing_zero_iff I C _).mp hdiff), mul_zero]
    have haa : (algebraMap T' C ar, algebraMap T' C ar) ∈ pairRing I C := by rw [mem_pairRing]
    have em' : m' x = ⟨(x, x), hxx⟩ + ⟨((0 : C), ψ' x - x), hdiff⟩ := Subtype.ext (by rw [hm'_apply]; ext <;> simp)
    have em'' : m'' x = m x + ⟨(algebraMap T' C ar, algebraMap T' C ar), haa⟩ * ⟨((0 : C), ψ' x - x), hdiff⟩ :=
      Subtype.ext (by rw [hm''_apply]; change _ = (m x : C × C) + _; rw [hm_apply]; ext <;> simp [hψ'' x])
    rw [em', em'', ϑ.map_add, ϑ.map_add, ϑ.map_mul, hϑ.1 x hxx, hϑ.1 _ haa, hred,
      Algebra.TensorProduct.includeLeftRingHom_apply]
    dsimp only
    rw [add_sub_cancel_left]
    congr 1
    refine (Algebra.smul_def (A := thickening T' V C) r _).trans ?_
    rw [Algebra.TensorProduct.algebraMap_apply]

  have hDq : ∀ t : T', D (algebraMap T' C t) =
      (1 : ResidueField T' ⊗[T'] C) ⊗ₜ (TrivSqZeroExt.inl (residue T' t) : TrivSqZeroExt (ResidueField T') (V × V)) := by
    intro t
    have htt : (algebraMap T' C t, algebraMap T' C t) ∈ pairRing I C := by rw [mem_pairRing]
    have em : m (algebraMap T' C t) = ⟨(algebraMap T' C t, algebraMap T' C t), htt⟩ :=
      Subtype.ext (by rw [hm_apply]; ext <;> simp [ψ.commutes])
    have em' : m' (algebraMap T' C t) = ⟨(algebraMap T' C t, algebraMap T' C t), htt⟩ :=
      Subtype.ext (by rw [hm'_apply]; ext <;> simp [ψ'.commutes])
    have hredt : toReduction T' C (algebraMap T' C t) = algebraMap (ResidueField T') (ResidueField T' ⊗[T'] C) (residue T' t) := by
      change (1 : ResidueField T') ⊗ₜ[T'] algebraMap T' C t = algebraMap (ResidueField T') (ResidueField T' ⊗[T'] C) (residue T' t)
      rw [Algebra.algebraMap_eq_smul_one (A := C) t, TensorProduct.tmul_smul, TensorProduct.smul_tmul', Algebra.smul_def, mul_one,
        IsLocalRing.ResidueField.algebraMap_eq, Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
    change GlueFun V C (ϑ.comp m) (ϑ.comp m') (algebraMap T' C t) = _
    rw [GlueFun, RingHom.comp_apply, RingHom.comp_apply, em, em', hϑ.1, proj_tmul, vPart_tmul, TrivSqZeroExt.fst_one,
      TrivSqZeroExt.snd_one, map_one, mul_one, TensorProduct.tmul_zero, map_zero, map_zero, add_zero, map_zero, add_zero,
      Algebra.TensorProduct.includeLeftRingHom_apply, hredt,
      ← one_mul (algebraMap (ResidueField T') (ResidueField T' ⊗[T'] C) (residue T' t)), smul_tmul_one_eq]

  have hWq : (Spec.map (CommRingCat.ofHom D) ≫ u) ≫ qY = RelTangentPoints.base (V × V) (thickeningSnd T' (V × V) C) ≫ Spec.map (CommRingCat.ofHom (residue T')) := by
    have eQ : CommRingCat.ofHom (algebraMap T' C) ≫ CommRingCat.ofHom D =
        (CommRingCat.ofHom (residue T') ≫ CommRingCat.ofHom (algebraMap (ResidueField T') (TrivSqZeroExt (ResidueField T') (V × V)))) ≫
          CommRingCat.ofHom (R := TrivSqZeroExt (ResidueField T') (V × V)) (S := thickening T' (V × V) C)
            (Algebra.TensorProduct.includeRight (R := ResidueField T') (A := ResidueField T' ⊗[T'] C)
              (B := TrivSqZeroExt (ResidueField T') (V × V))).toRingHom := by
      apply CommRingCat.hom_ext; apply RingHom.ext; intro t
      change D (algebraMap T' C t) = Algebra.TensorProduct.includeRight (algebraMap (ResidueField T') (TrivSqZeroExt (ResidueField T') (V × V)) (residue T' t))
      rw [Algebra.TensorProduct.includeRight_apply, TrivSqZeroExt.algebraMap_eq_inl]
      exact hDq t
    rw [Category.assoc, hu, ← Spec.map_comp, eQ, RelTangentPoints.base, thickeningSnd, SquareZero.toBase, Spec.map_comp,
      Spec.map_comp, Category.assoc]
  have eSpec : ∀ (g : (V × V) →ₗ[k] V) (η : C →+* thickening T' V C),
      (∀ x, jmap T' V C g (D x) = η x) → jSpec T' V C g ≫ Spec.map (CommRingCat.ofHom D) = Spec.map (CommRingCat.ofHom η) := by
    intro g η hη
    rw [jSpec, ← Spec.map_comp]
    congr 1
    apply CommRingCat.hom_ext; apply RingHom.ext; intro x
    exact hη x
  have hW1 : jSpec T' V C fst ≫ Spec.map (CommRingCat.ofHom D) ≫ u = a0 ≫ ak := by
    rw [ha0', ← Category.assoc, eSpec fst (ϑ.comp m) (fun x => Glue_fst V C _ _ hproj x)]
  have hW2 : jSpec T' V C snd ≫ Spec.map (CommRingCat.ofHom D) ≫ u = b0 ≫ ak := by
    rw [hb0', ← Category.assoc, eSpec snd (ϑ.comp m') (fun x => Glue_snd V C _ _ hproj x)]
  have hW3 : jSpec T' V C f ≫ Spec.map (CommRingCat.ofHom D) ≫ u = Spec.map (CommRingCat.ofHom (ϑ.comp m'')) ≫ u := by
    rw [← Category.assoc, eSpec f (ϑ.comp m'') (fun x => DFunLike.congr_fun hDa x)]
  let W₀ : Spec (CommRingCat.of (thickening T' (V × V) C)) ⟶ Ak :=
    hak.lift (Spec.map (CommRingCat.ofHom D) ≫ u) (RelTangentPoints.base (V × V) (thickeningSnd T' (V × V) C)) hWq
  have hW₀a : W₀ ≫ ak = Spec.map (CommRingCat.ofHom D) ≫ u := hak.lift_fst _ _ _
  have hW₀x : W₀ ≫ xk = RelTangentPoints.base (V × V) (thickeningSnd T' (V × V) C) := hak.lift_snd _ _ _
  have r1 : jSpec T' V C fst ≫ W₀ = a0 :=
    hak.hom_ext (by rw [Category.assoc, hW₀a, hW1]) (by rw [Category.assoc, hW₀x, jSpec_base, ha0])
  have r2 : jSpec T' V C snd ≫ W₀ = b0 :=
    hak.hom_ext (by rw [Category.assoc, hW₀a, hW2]) (by rw [Category.assoc, hW₀x, jSpec_base, hb0])
  have hc0 : (jSpec T' V C f ≫ W₀) ≫ xk = RelTangentPoints.base V (thickeningSnd T' V C) := by
    rw [Category.assoc, hW₀x, jSpec_base]

  let T := RelTangentPoints.translate xk Lk (V × V) (reductionBase T' C) (thickeningFst T' (V × V) C)
    (thickeningSnd T' (V × V) C) (thickening_isPullback (V × V) C) W₀ hW₀x
  obtain ⟨T₁, hT₁⟩ := (RelTangentPoints.existsUnique_comp_openInclusion_eq xk (Lk.one (𝟙 _)).1 (V × V) (reductionBase T' C)
    (thickeningFst T' (V × V) C) (thickeningSnd T' (V × V) C) (thickening_isPullback (V × V) C) T Ue e₁ he₁).exists
  have htr : ∀ (g : (V × V) →ₗ[k] V) (w0 : Spec (CommRingCat.of (thickening T' V C)) ⟶ Ak)
      (hw0 : w0 ≫ xk = RelTangentPoints.base V (thickeningSnd T' V C)),
      jSpec T' V C g ≫ W₀ = w0 →
      jSpec T' V C g ≫ T.1 = (RelTangentPoints.translate xk Lk V (reductionBase T' C) (thickeningFst T' V C)
        (thickeningSnd T' V C) (thickening_isPullback V C) w0 hw0).1 := by
    intro g w0 hw0 hr
    exact RelTangentPoints.comp_translate_eq_translate_comp xk Lk V (V × V) (reductionBase T' C) (reductionBase T' C)
      (thickeningFst T' V C) (thickeningSnd T' V C) (thickening_isPullback V C)
      (thickeningFst T' (V × V) C) (thickeningSnd T' (V × V) C) (thickening_isPullback (V × V) C)
      (𝟙 _) (Category.id_comp _) (jSpec T' V C g) (by rw [jSpec_thickeningFst, Category.comp_id])
      (by rw [zeroSection_jSpec, Category.id_comp]) W₀ hW₀x w0 hw0 hr
  have key : ∀ (g : (V × V) →ₗ[k] V) (w0 : Spec (CommRingCat.of (thickening T' V C)) ⟶ Ak)
      (hw0 : w0 ≫ xk = RelTangentPoints.base V (thickeningSnd T' V C))
      (w1 : Spec (CommRingCat.of (thickening T' V C)) ⟶ (Ue : Scheme.{u})),
      jSpec T' V C g ≫ W₀ = w0 →
      w1 ≫ Ue.ι = (RelTangentPoints.translate xk Lk V (reductionBase T' C) (thickeningFst T' V C) (thickeningSnd T' V C)
                  (thickening_isPullback V C) w0 hw0).1 →
      jSpec T' V C g ≫ T₁ = w1 := by
    intro g w0 hw0 w1 hr hw1
    exact (RelTangentPoints.existsUnique_comp_openInclusion_eq xk (Lk.one (𝟙 _)).1 V (reductionBase T' C)
      (thickeningFst T' V C) (thickeningSnd T' V C) (thickening_isPullback V C) _ Ue e₁ he₁).unique
      (by rw [Category.assoc, hT₁, htr g w0 hw0 hr]) hw1
  have e1 : jSpec T' V C fst ≫ T₁ = a1 := key fst a0 ha0 a1 r1 hatr
  have e2 : jSpec T' V C snd ≫ T₁ = b1 := key snd b0 hb0 b1 r2 hbtr

  have hnat : ∀ (g : (V × V) →ₗ[k] V) {A : Type u} [CommRing A] (φ : A →+* thickening T' (V × V) C) (y : A)
      (ξ : Module.Dual (ResidueField T') V),
      tangentCoords T' V C ((jmap T' V C g).toRingHom.comp φ) y ξ = tangentCoords T' (V × V) C φ y (ξ ∘ₗ g) := by
    intro g A _ φ y ξ
    rw [tangentCoords_apply, tangentCoords_apply, RingHom.comp_apply]
    generalize φ y = e
    induction e using TensorProduct.induction_on with
    | zero => simp
    | tmul c t =>
      change tensorToDualHom _ _ V (TensorProduct.map LinearMap.id (TrivSqZeroExt.sndHom (ResidueField T') V)
          (jmap T' V C g (c ⊗ₜ t))) ξ
        = tensorToDualHom _ _ (V × V) (TensorProduct.map LinearMap.id (TrivSqZeroExt.sndHom (ResidueField T') (V × V)) (c ⊗ₜ t)) (ξ ∘ₗ g)
      rw [AlgebraicGeometry.SmallExtension.CoordsAlphaAux.jmap, Algebra.TensorProduct.map_tmul, AlgHom.id_apply, TensorProduct.map_tmul,
        TensorProduct.map_tmul]
      simp only [LinearMap.id_coe, id_eq, tensorToDualHom_tmul, LinearMap.comp_apply]
      change ξ (TrivSqZeroExt.map g t).snd • c = ξ (g t.snd) • c
      rw [TrivSqZeroExt.snd_map]
    | add x y hx hy => simp only [map_add, LinearMap.add_apply, hx, hy]

  refine ⟨jSpec T' V C f ≫ W₀, hc0, jSpec T' V C f ≫ T₁, ?_, ?_, ?_⟩
  · rw [Category.assoc, hW₀a, hW3]
    exact hpair ψ'' m'' hm''1 hm''2
  · rw [Category.assoc, hT₁]
    exact htr f _ hc0 rfl
  · rw [hac, hbc, ← e1, ← e2, chartRingHom_jSpec_comp, chartRingHom_jSpec_comp, chartRingHom_jSpec_comp]
    funext y
    apply LinearMap.ext
    intro ξ
    rw [Pi.add_apply, Pi.smul_apply, LinearMap.add_apply, LinearMap.smul_apply, hnat, hnat, hnat]
    change _ = tangentCoords T' (V × V) C _ y (ξ ∘ₗ (LinearMap.fst k V V + r • LinearMap.snd k V V))
    rw [LinearMap.comp_add, LinearMap.comp_smul, map_add, map_smul]

end S_AlgebraicGeometry_SmallExtension_isTangentCoordsOfPairAt_add_smul_of_apply_eq_add_mul_sub
end P2MW
export P2MW.S_AlgebraicGeometry_SmallExtension_isTangentCoordsOfPairAt_add_smul_of_apply_eq_add_mul_sub (solution)
