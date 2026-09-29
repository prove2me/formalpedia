-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.TwoAffineOpenCover.finrank_ker_cechDiff_baseChange_eq_one_of_geometricallyReduced_of_connected
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/7e147044-8ad6-555a-8743-37448ce9b4ad

import Mathlib
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_toH0_bijective
import Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_baseChangeIsos_structureSheaf
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_finrank_ker_cechDiff_baseChange_eq_one_of_geometricallyReduced_of_connected

set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_finrank_ker_cechDiff_baseChange_eq_one_of_geometricallyReduced_of_connected.AlgebraicGeometry TensorProduct"

noncomputable section

namespace TwoChartCech
p2m_export "TwoChartCech" "kerBaseChangeHom kerBaseChangeHom_apply_coe"
p2m_open "TwoChartCech"

theorem kerBaseChangeHom_bijective_of_flat {R : Type u} [CommRing R] {C0 C1 : Type u} [AddCommGroup C0]
    [Module R C0] [AddCommGroup C1] [Module R C1] (d : C0 →ₗ[R] C1) (A : Type u) [CommRing A] [Algebra R A]
    [Module.Flat R A] : Function.Bijective (kerBaseChangeHom d A) := by
  constructor
  ·
    intro x y h
    have h' := congrArg Subtype.val h
    rw [kerBaseChangeHom_apply_coe, kerBaseChangeHom_apply_coe] at h'
    have hinj : Function.Injective ((LinearMap.ker d).subtype.baseChange A) := by
      rw [LinearMap.baseChange_eq_ltensor]
      exact Module.Flat.lTensor_preserves_injective_linearMap _ (LinearMap.ker d).subtype_injective
    exact hinj h'
  ·
    rintro ⟨y, hy⟩
    have hex := Module.Flat.lTensor_exact A (LinearMap.exact_subtype_ker_map d)
    have hy' : (d.lTensor A) y = 0 := by rw [← LinearMap.baseChange_eq_ltensor]; exact hy
    obtain ⟨x, hx⟩ := (hex y).mp hy'
    refine ⟨x, Subtype.ext ?_⟩
    rw [kerBaseChangeHom_apply_coe, LinearMap.baseChange_eq_ltensor]
    exact hx

section ChangeField

variable {R : Type u} [CommRing R] {C0 C1 : Type u} [AddCommGroup C0] [Module R C0] [AddCommGroup C1]
  [Module R C1] (d : C0 →ₗ[R] C1)
variable (K L : Type u) [Field K] [Field L] [Algebra R K] [Algebra R L] [Algebra K L] [IsScalarTower R K L]

theorem cancelBaseChange_tmul_baseChange (l : L) (x : K ⊗[R] C0) :
    TensorProduct.AlgebraTensorModule.cancelBaseChange R K L L C1 (l ⊗ₜ[K] (d.baseChange K x))
      = (d.baseChange L) (TensorProduct.AlgebraTensorModule.cancelBaseChange R K L L C0 (l ⊗ₜ[K] x)) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => rw [map_add, TensorProduct.tmul_add, map_add, hx, hy, TensorProduct.tmul_add, map_add, map_add]
  | tmul k m => simp [LinearMap.baseChange_tmul, TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul]

theorem cancelBaseChange_baseChange (z : L ⊗[K] (K ⊗[R] C0)) :
    TensorProduct.AlgebraTensorModule.cancelBaseChange R K L L C1 (((d.baseChange K).baseChange L) z)
      = (d.baseChange L) (TensorProduct.AlgebraTensorModule.cancelBaseChange R K L L C0 z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]
  | tmul l x => rw [LinearMap.baseChange_tmul]; exact cancelBaseChange_tmul_baseChange d K L l x

theorem map_cancelBaseChange_ker :
    Submodule.map (TensorProduct.AlgebraTensorModule.cancelBaseChange R K L L C0).toLinearMap
        (LinearMap.ker ((d.baseChange K).baseChange L))
      = LinearMap.ker (d.baseChange L) := by
  ext w
  rw [Submodule.mem_map_equiv, LinearMap.mem_ker, LinearMap.mem_ker]
  have hw : w = TensorProduct.AlgebraTensorModule.cancelBaseChange R K L L C0
      ((TensorProduct.AlgebraTensorModule.cancelBaseChange R K L L C0).symm w) :=
    ((TensorProduct.AlgebraTensorModule.cancelBaseChange R K L L C0).apply_symm_apply w).symm
  constructor
  · intro h
    rw [hw, ← cancelBaseChange_baseChange, h, map_zero]
  · intro h
    apply (TensorProduct.AlgebraTensorModule.cancelBaseChange R K L L C1).injective
    rw [cancelBaseChange_baseChange, ← hw, h, map_zero]

def kerCancelEquiv : LinearMap.ker ((d.baseChange K).baseChange L) ≃ₗ[L] LinearMap.ker (d.baseChange L) :=
  (TensorProduct.AlgebraTensorModule.cancelBaseChange R K L L C0).ofSubmodules _ _
    (map_cancelBaseChange_ker d K L)

theorem finrank_ker_baseChange_eq :
    Module.finrank K (LinearMap.ker (d.baseChange K)) = Module.finrank L (LinearMap.ker (d.baseChange L)) := by
  have e1 : (L ⊗[K] LinearMap.ker (d.baseChange K)) ≃ₗ[L] LinearMap.ker ((d.baseChange K).baseChange L) :=
    LinearEquiv.ofBijective _ (kerBaseChangeHom_bijective_of_flat (d.baseChange K) L)
  let b := Module.Basis.ofVectorSpace K (LinearMap.ker (d.baseChange K))
  have h1 : Module.finrank K (LinearMap.ker (d.baseChange K))
      = Nat.card (Module.Basis.ofVectorSpaceIndex K (LinearMap.ker (d.baseChange K))) :=
    Module.finrank_eq_nat_card_basis b
  have h2 : Module.finrank L (L ⊗[K] LinearMap.ker (d.baseChange K))
      = Nat.card (Module.Basis.ofVectorSpaceIndex K (LinearMap.ker (d.baseChange K))) :=
    Module.finrank_eq_nat_card_basis (Algebra.TensorProduct.basis L b)
  rw [h1, ← h2, e1.finrank_eq, (kerCancelEquiv d K L).finrank_eq]

end ChangeField

end TwoChartCech

namespace S17H0One

p2m_open "CategoryTheory CategoryTheory.Limits Opposite TensorProduct AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_finrank_ker_cechDiff_baseChange_eq_one_of_geometricallyReduced_of_connected.AlgebraicGeometry"

theorem idempotent_trivial {Y : Scheme.{u}} [AlgebraicGeometry.IsReduced Y] [ConnectedSpace ↥Y]
    (e : Γ(Y, ⊤)) (he : IsIdempotentElem e) : e = 0 ∨ e = 1 := by
  classical

  have hcov : ∀ y : ↥Y, y ∈ Y.basicOpen e ∨ y ∈ Y.basicOpen (1 - e) := by
    intro y
    rw [Scheme.mem_basicOpen_top, Scheme.mem_basicOpen_top]
    have h1 : (ConcreteCategory.hom (Y.presheaf.germ ⊤ y trivial)) e +
        (ConcreteCategory.hom (Y.presheaf.germ ⊤ y trivial)) (1 - e) = 1 := by
      rw [← map_add, add_sub_cancel, map_one]
    exact IsLocalRing.isUnit_or_isUnit_of_add_one h1
  have hdisj : Y.basicOpen e ⊓ Y.basicOpen (1 - e) = ⊥ := by
    rw [← Scheme.basicOpen_mul, mul_sub, mul_one, he.eq, sub_self, Scheme.basicOpen_zero]

  have hcompl : ((Y.basicOpen e : Set ↥Y))ᶜ = (Y.basicOpen (1 - e) : Set ↥Y) := by
    ext y
    simp only [Set.mem_compl_iff, SetLike.mem_coe]
    constructor
    · intro hy
      exact (hcov y).resolve_left hy
    · intro hy hy'
      have : y ∈ (Y.basicOpen e ⊓ Y.basicOpen (1 - e) : Y.Opens) := ⟨hy', hy⟩
      rw [hdisj] at this
      exact this
  have hclopen : IsClopen ((Y.basicOpen e : Set ↥Y)) := by
    refine ⟨?_, (Y.basicOpen e).isOpen⟩
    rw [← isOpen_compl_iff, hcompl]
    exact (Y.basicOpen (1 - e)).isOpen
  rcases isClopen_iff.mp hclopen with h | h
  · left
    have hb : Y.basicOpen e = ⊥ := by
      apply TopologicalSpace.Opens.ext
      simpa using h
    exact (basicOpen_eq_bot_iff e).mp hb
  · right
    have hb : Y.basicOpen (1 - e) = ⊥ := by
      apply TopologicalSpace.Opens.ext
      rw [TopologicalSpace.Opens.coe_bot, ← Set.compl_univ, ← h, hcompl]
    have := (basicOpen_eq_bot_iff (1 - e)).mp hb
    exact (sub_eq_zero.mp this).symm

theorem isField_of_idempotent_trivial (A : Type u) [CommRing A] [IsArtinianRing A] [_root_.IsReduced A]
    [Nontrivial A] (h : ∀ e : A, IsIdempotentElem e → e = 0 ∨ e = 1) : IsField A := by
  classical
  let φ := IsArtinianRing.equivPi A

  have hne : Nonempty (MaximalSpectrum A) := by
    obtain ⟨m, hm⟩ := Ideal.exists_maximal A
    exact ⟨⟨m, hm⟩⟩
  have hsub : Subsingleton (MaximalSpectrum A) := by
    refine ⟨fun I J => ?_⟩
    by_contra hIJ
    let f : (K : MaximalSpectrum A) → A ⧸ K.asIdeal := Pi.single I 1
    have hf : IsIdempotentElem f := by
      change f * f = f
      ext K'
      simp only [f, Pi.mul_apply]
      by_cases hK : K' = I
      · subst hK; simp
      · simp [Pi.single_eq_of_ne hK]
    have hf' : IsIdempotentElem (φ.symm f) := by
      change φ.symm f * φ.symm f = φ.symm f
      rw [← map_mul, hf.eq]
    rcases h _ hf' with h0 | h1
    · have : f = 0 := by simpa using congrArg φ h0
      have hI := congrFun this I
      haveI := I.isMaximal
      letI : Field (A ⧸ I.asIdeal) := Ideal.Quotient.field I.asIdeal
      simp [f] at hI
    · have : f = 1 := by simpa using congrArg φ h1
      have hJ := congrFun this J
      haveI := J.isMaximal
      letI : Field (A ⧸ J.asIdeal) := Ideal.Quotient.field J.asIdeal
      simp [f, Pi.single_eq_of_ne (Ne.symm hIJ)] at hJ
  haveI : Unique (MaximalSpectrum A) := @Unique.mk' _ ⟨hne.some⟩ hsub

  let ψ : A ≃+* A ⧸ (default : MaximalSpectrum A).asIdeal :=
    φ.toRingEquiv.trans (RingEquiv.piUnique fun K : MaximalSpectrum A => A ⧸ K.asIdeal)
  haveI := (default : MaximalSpectrum A).isMaximal
  exact MulEquiv.isField (Ideal.Quotient.field _).toIsField ψ.toMulEquiv

end S17H0One

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Scheme.basicOpen_of_isUnit basicOpen_eq_bot_iff Spec IsIntegral Scheme Scheme.basicOpen_zero Flat IsReduced IsReduced.component_reduced Scheme.basicOpen_mul Scheme.mem_basicOpen_top Scheme.TwoAffineOpenCover Scheme.TwoAffineOpenCover.specMap"
namespace Scheme
p2m_export "AlgebraicGeometry.Scheme" "basicOpen_of_isUnit Γ basicOpen_zero basicOpen basicOpen_mul mem_basicOpen_top Opens TwoAffineOpenCover TwoAffineOpenCover.specMap"
namespace TwoAffineOpenCover
p2m_export "AlgebraicGeometry.Scheme.TwoAffineOpenCover" "specMap algebraOfHom cover structureSheafSections pullback toH0_bijective exists_baseChangeIsos_structureSheaf"
p2m_open "AlgebraicGeometry.Scheme.TwoAffineOpenCover AlgebraicGeometry.Scheme AlgebraicGeometry"

open S17H0One

theorem finrank_ker_eq_one_of_isAlgClosed'
    {R : Type u} [CommRing R] {X : Scheme.{u}} (𝒱 : X.TwoAffineOpenCover) (c : X ⟶ Spec (.of R))
    (L : Type u) [Field L] [IsAlgClosed L] [Algebra R L]
    [AlgebraicGeometry.IsReduced (Limits.pullback c (specMap R L))]
    [ConnectedSpace ↥(Limits.pullback c (specMap R L))]
    [Module.Finite L (LinearMap.ker ((𝒱.structureSheafSections c).cechDiff.baseChange L))] :
    Module.finrank L (LinearMap.ker ((𝒱.structureSheafSections c).cechDiff.baseChange L)) = 1 := by
  obtain ⟨e0, e1, e01, eH0, eH1, -, -, -, -, -⟩ := exists_baseChangeIsos_structureSheaf 𝒱 c L
  letI := algebraOfHom (Limits.pullback.snd c (specMap R L)) ⊤
  have hT := toH0_bijective (𝒱.pullback c L) (Limits.pullback.snd c (specMap R L))

  let e : Γ((Limits.pullback c (specMap R L)), ⊤) ≃ₗ[L] LinearMap.ker ((𝒱.structureSheafSections c).cechDiff.baseChange L) :=
    (LinearEquiv.ofBijective _ hT).trans eH0.symm
  haveI : Module.Finite L Γ((Limits.pullback c (specMap R L)), ⊤) := Module.Finite.equiv e.symm
  haveI : IsArtinianRing Γ((Limits.pullback c (specMap R L)), ⊤) := IsArtinianRing.of_finite L _
  haveI : _root_.IsReduced Γ((Limits.pullback c (specMap R L)), ⊤) := AlgebraicGeometry.IsReduced.component_reduced ⊤
  haveI : Nontrivial Γ((Limits.pullback c (specMap R L)), ⊤) := by
    obtain ⟨y⟩ := (inferInstance : Nonempty ↥(Limits.pullback c (specMap R L)))
    refine ⟨⟨1, 0, fun h10 => ?_⟩⟩
    have hb : (Limits.pullback c (specMap R L)).basicOpen (1 : Γ((Limits.pullback c (specMap R L)), ⊤)) = ⊥ := by rw [h10, Scheme.basicOpen_zero]
    have : y ∈ (Limits.pullback c (specMap R L)).basicOpen (1 : Γ((Limits.pullback c (specMap R L)), ⊤)) := by
      rw [Scheme.basicOpen_of_isUnit _ isUnit_one]; trivial
    rw [hb] at this
    exact this
  have hfield : IsField Γ((Limits.pullback c (specMap R L)), ⊤) := isField_of_idempotent_trivial _ (idempotent_trivial (Y := (Limits.pullback c (specMap R L))))
  haveI : IsDomain Γ((Limits.pullback c (specMap R L)), ⊤) := hfield.isDomain
  haveI : Algebra.IsIntegral L Γ((Limits.pullback c (specMap R L)), ⊤) := Algebra.IsIntegral.of_finite L _
  have hbij : Function.Bijective (algebraMap L Γ((Limits.pullback c (specMap R L)), ⊤)) := IsAlgClosed.algebraMap_bijective_of_isIntegral
  let eL : L ≃ₗ[L] Γ((Limits.pullback c (specMap R L)), ⊤) := LinearEquiv.ofBijective (Algebra.linearMap L _) hbij
  rw [← e.finrank_eq, ← eL.finrank_eq, Module.finrank_self]

end AlgebraicGeometry.Scheme.TwoAffineOpenCover

open _root_.AlgebraicGeometry _root_.P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_finrank_ker_cechDiff_baseChange_eq_one_of_geometricallyReduced_of_connected.AlgebraicGeometry in
theorem solution
    {R : Type u} [CommRing R] {X : Scheme.{u}} (𝒱 : X.TwoAffineOpenCover) (c : X ⟶ Spec (.of R))
    (hred : ∀ (L : Type u) [Field L] [IsAlgClosed L] [Algebra R L],
      IsReduced (Limits.pullback c (Scheme.TwoAffineOpenCover.specMap R L)))
    (hconn : ∀ (L : Type u) [Field L] [IsAlgClosed L] [Algebra R L],
      ConnectedSpace ↥(Limits.pullback c (Scheme.TwoAffineOpenCover.specMap R L)))
    (hfin : ∀ (L : Type u) [Field L] [IsAlgClosed L] [Algebra R L],
      Module.Finite L (LinearMap.ker ((𝒱.structureSheafSections c).cechDiff.baseChange L)))
    (K : Type u) [Field K] [Algebra R K] :
    Module.finrank K (LinearMap.ker ((𝒱.structureSheafSections c).cechDiff.baseChange K)) = 1 := by
  let L := AlgebraicClosure K
  haveI := hred L
  haveI := hconn L
  haveI := hfin L
  rw [TwoChartCech.finrank_ker_baseChange_eq _ K L]
  exact AlgebraicGeometry.Scheme.TwoAffineOpenCover.finrank_ker_eq_one_of_isAlgClosed' 𝒱 c L

end

end S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_finrank_ker_cechDiff_baseChange_eq_one_of_geometricallyReduced_of_connected
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_finrank_ker_cechDiff_baseChange_eq_one_of_geometricallyReduced_of_connected (solution)
