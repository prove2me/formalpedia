-- Prove2me | Definitions.Def_GroundTheory_AutomorphicForms_HeckeIrreducible
-- name    : GroundTheory_AutomorphicForms_HeckeIrreducible
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-25T01:37:42.711248+00:00
-- url     : https://prove2.me/theorems/8317e4ba-1a7c-4551-9386-0e0026665e20
-- title:
--   Hecke Irreducible
-- statement:
--   Definitions and structural lemmas for Hecke Irreducible, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HeckeIrreducible.lean

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HeckeAlgebraLevel
import Theorems.Thm_GroundTheory_Automorphic_HeckeAlgebra_HeckeAlgebraLevel_coe_smul_fixedVectors
import Theorems.Thm_GroundTheory_Automorphic_HeckeAlgebra_mul_apply
import Theorems.Thm_GroundTheory_Automorphic_map_heckeAct

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
universe u
namespace GroundTheory.Automorphic
open Set Filter Topology MeasureTheory
open scoped Pointwise
variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
  [MeasurableSpace G] [BorelSpace G] {μ : Measure G} [μ.IsHaarMeasure]
  {K : Subgroup G} (hKc : IsCompact (K : Set G)) (hKo : IsOpen (K : Set G))
namespace HeckeAlgebra
section General
variable {V : Type*} [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ G V}
theorem leftReg_mul (g : G) (a b : HeckeAlgebra μ) : leftReg μ g (a * b) = leftReg μ g a * b := by
  rw [← heckeAct_leftReg, heckeAct_ltrans g a.mem (isSmooth_leftReg b), ← heckeAct_leftReg]
  rfl
end General
section Simple
variable {V : Type*} [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ G V}
def fixedMapLevel {W : Type*} [AddCommGroup W] [Module ℂ W] {σ : Representation ℂ G W}
    (T : Representation.IntertwiningMap ρ σ) :
    fixedVectors ρ K →ₗ[HeckeAlgebraLevel μ K hKc hKo] fixedVectors σ K where
  toFun v := ⟨T v, map_mem_fixedVectors ρ T v.2⟩
  map_add' v w := Subtype.ext (map_add T _ _)
  map_smul' h v := Subtype.ext (by
    simp only [RingHom.id_apply, HeckeAlgebraLevel.coe_smul_fixedVectors]
    exact map_heckeAct T (h : HeckeAlgebra μ).mem (smooth_of_mem_fixedVectors hKo v.2))
def fixedVectorsEquiv {W : Type*} [AddCommGroup W] [Module ℂ W] {σ : Representation ℂ G W}
    (T : ρ.Equiv σ) :
    fixedVectors ρ K ≃ₗ[HeckeAlgebraLevel μ K hKc hKo] fixedVectors σ K :=
  LinearEquiv.ofBijective (fixedMapLevel hKc hKo T.toIntertwiningMap) (by
    refine ⟨fun v w h => Subtype.ext (T.toLinearEquiv.injective (congrArg Subtype.val h)), ?_⟩
    intro w
    set v := T.toLinearEquiv.symm (w : W)
    have hTv : T.toLinearEquiv v = w := T.toLinearEquiv.apply_symm_apply _
    have hv : v ∈ fixedVectors ρ K := fun k hk => T.toLinearEquiv.injective (by
      rw [Representation.Equiv.toLinearEquiv_apply, T.toIntertwiningMap.isIntertwining,
        ← Representation.Equiv.toLinearEquiv_apply, hTv, w.2 k hk])
    exact ⟨⟨v, hv⟩, Subtype.ext hTv⟩)
end Simple
section Construction
namespace HeckeAlgebraLevel
theorem smul_mem_ideal (I : Submodule (HeckeAlgebraLevel μ K hKc hKo) (HeckeAlgebraLevel μ K hKc hKo))
    (c : ℂ) {h : HeckeAlgebraLevel μ K hKc hKo} (hh : h ∈ I) : c • h ∈ I := by
  have : c • h = (c • (1 : HeckeAlgebraLevel μ K hKc hKo)) * h := by
    apply ext hKc hKo
    rw [val_smul, val_mul, val_smul, val_one, smul_mul_assoc,
      ((mem_biInvariant_iff_idem hKc hKo).1 (val_mem hKc hKo h)).1]
  rw [this]
  exact I.smul_mem _ hh
def cornerₗ : HeckeAlgebra μ →ₗ[ℂ] HeckeAlgebraLevel μ K hKc hKo where
  toFun := corner hKc hKo
  map_add' a b := ext hKc hKo (by simp only [val_corner, val_add, mul_add, add_mul])
  map_smul' c a := ext hKc hKo (by
    simp only [val_corner, val_smul, RingHom.id_apply, mul_smul_comm, smul_mul_assoc])
theorem val_cornerₗ (f : HeckeAlgebra μ) :
    ((cornerₗ hKc hKo f : HeckeAlgebraLevel μ K hKc hKo) : HeckeAlgebra μ) =
      idem μ hKc hKo * f * idem μ hKc hKo := rfl
theorem cornerₗ_val (h : HeckeAlgebraLevel μ K hKc hKo) : cornerₗ hKc hKo (h : HeckeAlgebra μ) = h := by
  apply ext hKc hKo
  obtain ⟨h1, h2⟩ := (mem_biInvariant_iff_idem hKc hKo).1 (val_mem hKc hKo h)
  rw [val_cornerₗ, h1, h2]
theorem cornerₗ_mul_idem (f : HeckeAlgebra μ) :
    cornerₗ hKc hKo (f * idem μ hKc hKo) = cornerₗ hKc hKo f := by
  apply ext hKc hKo
  simp only [val_cornerₗ, mul_assoc, (isIdempotentElem_idem hKc hKo).eq]
end HeckeAlgebraLevel
open HeckeAlgebraLevel
variable (I : Submodule (HeckeAlgebraLevel μ K hKc hKo) (HeckeAlgebraLevel μ K hKc hKo))
def heckeKernel : Submodule ℂ (HeckeAlgebra μ) where
  carrier := {φ | ∀ g, cornerₗ hKc hKo (leftReg μ g φ) ∈ I}
  add_mem' {a b} ha hb g := by
    rw [map_add, map_add]
    exact I.add_mem (ha g) (hb g)
  zero_mem' g := by
    rw [map_zero, map_zero]
    exact I.zero_mem
  smul_mem' c φ hφ g := by
    rw [map_smul, map_smul]
    exact smul_mem_ideal hKc hKo I c (hφ g)
theorem heckeKernel_le_comap (g : G) :
    heckeKernel hKc hKo I ≤ (heckeKernel hKc hKo I).comap (leftReg μ g) := by
  intro φ hφ g'
  rw [← Module.End.mul_apply, ← map_mul]
  exact hφ (g' * g)
def quotRep : Representation ℂ G (HeckeAlgebra μ ⧸ heckeKernel hKc hKo I) :=
  (leftReg μ).quotient _ (heckeKernel_le_comap hKc hKo I)
theorem quotRep_mkQ (g : G) (φ : HeckeAlgebra μ) :
    quotRep hKc hKo I g ((heckeKernel hKc hKo I).mkQ φ) =
      (heckeKernel hKc hKo I).mkQ (leftReg μ g φ) := rfl
def quotMap : Representation.IntertwiningMap (leftReg μ) (quotRep hKc hKo I) where
  toLinearMap := (heckeKernel hKc hKo I).mkQ
  isIntertwining' g := LinearMap.ext fun φ => (quotRep_mkQ hKc hKo I g φ).symm
theorem heckeAct_quotRep (f φ : HeckeAlgebra μ) :
    heckeAct μ (quotRep hKc hKo I) f ((heckeKernel hKc hKo I).mkQ φ) =
      (heckeKernel hKc hKo I).mkQ (f * φ) := by
  have := map_heckeAct (μ := μ) (quotMap hKc hKo I) f.mem (isSmooth_leftReg φ)
  rw [heckeAct_leftReg] at this
  exact this.symm
theorem mkQ_mul_idem (φ : HeckeAlgebra μ) :
    (heckeKernel hKc hKo I).mkQ (φ * idem μ hKc hKo) = (heckeKernel hKc hKo I).mkQ φ := by
  rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq]
  intro g
  rw [map_sub, leftReg_mul, map_sub, cornerₗ_mul_idem, sub_self]
  exact I.zero_mem
def toFixedQuot :
    HeckeAlgebraLevel μ K hKc hKo →ₗ[HeckeAlgebraLevel μ K hKc hKo] fixedVectors (quotRep hKc hKo I) K where
  toFun h := ⟨(heckeKernel hKc hKo I).mkQ (h : HeckeAlgebra μ), fun k hk => by
    rw [quotRep_mkQ, mem_fixedVectors_leftReg.2 (fun k' hk' x => apply_mul_left hKc hKo h hk' x) k hk]⟩
  map_add' a b := Subtype.ext (by simp only [val_add, map_add, Submodule.coe_add])
  map_smul' a h := Subtype.ext (by
    simp only [RingHom.id_apply, coe_smul_fixedVectors]
    rw [heckeAct_quotRep]
    rfl)
theorem toFixedQuot_apply (h : HeckeAlgebraLevel μ K hKc hKo) :
    ((toFixedQuot hKc hKo I h : fixedVectors (quotRep hKc hKo I) K) :
      HeckeAlgebra μ ⧸ heckeKernel hKc hKo I) = (heckeKernel hKc hKo I).mkQ (h : HeckeAlgebra μ) := rfl
theorem ker_toFixedQuot : LinearMap.ker (toFixedQuot hKc hKo I) = I := by
  ext h
  rw [LinearMap.mem_ker]
  constructor
  · intro h0
    have hmem : (h : HeckeAlgebra μ) ∈ heckeKernel hKc hKo I := by
      rw [← Submodule.Quotient.mk_eq_zero, ← Submodule.mkQ_apply, ← toFixedQuot_apply, h0]
      rfl
    have := hmem 1
    rwa [map_one, Module.End.one_apply, cornerₗ_val] at this
  · intro hI
    apply Subtype.ext
    rw [toFixedQuot_apply, Submodule.mkQ_apply, ZeroMemClass.coe_zero,
      Submodule.Quotient.mk_eq_zero]
    intro g
    obtain ⟨h1, h2⟩ := (mem_biInvariant_iff_idem hKc hKo).1 (val_mem hKc hKo h)
    have e1 : leftReg μ g (h : HeckeAlgebra μ) = leftReg μ g (idem μ hKc hKo) * h := by
      rw [← leftReg_mul, h1]
    have : cornerₗ hKc hKo (leftReg μ g (h : HeckeAlgebra μ)) =
        cornerₗ hKc hKo (leftReg μ g (idem μ hKc hKo)) * h := by
      apply HeckeAlgebraLevel.ext hKc hKo
      rw [val_mul, val_cornerₗ, val_cornerₗ, e1]
      simp only [mul_assoc, h1, h2]
    rw [this]
    exact I.smul_mem _ hI
theorem toFixedQuot_surjective : Function.Surjective (toFixedQuot hKc hKo I) := by
  intro y
  obtain ⟨φ, hφ⟩ := (heckeKernel hKc hKo I).mkQ_surjective (y : HeckeAlgebra μ ⧸ _)
  refine ⟨cornerₗ hKc hKo φ, Subtype.ext ?_⟩
  rw [toFixedQuot_apply, val_cornerₗ, mkQ_mul_idem, ← heckeAct_quotRep, hφ]
  exact heckeAct_idem_of_mem (μ := μ) hKc hKo y.2
def fixedQuotEquiv :
    (HeckeAlgebraLevel μ K hKc hKo ⧸ I) ≃ₗ[HeckeAlgebraLevel μ K hKc hKo]
      fixedVectors (quotRep hKc hKo I) K :=
  (Submodule.quotEquivOfEq I _ (ker_toFixedQuot hKc hKo I).symm).trans
    ((toFixedQuot hKc hKo I).quotKerEquivOfSurjective (toFixedQuot_surjective hKc hKo I))
end Construction
section Classification
open HeckeAlgebraLevel
variable {V : Type*} [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ G V}
def orbitMap (v : V) (hv : v ∈ smoothVectors ρ) : HeckeAlgebra μ →ₗ[ℂ] V where
  toFun f := heckeAct μ ρ f v
  map_add' a b := by
    rw [coe_add]
    exact heckeAct_add_left a.mem b.mem hv
  map_smul' c a := by
    rw [coe_smul]
    exact heckeAct_smul_left c a.mem hv
end Classification
end HeckeAlgebra
end GroundTheory.Automorphic


