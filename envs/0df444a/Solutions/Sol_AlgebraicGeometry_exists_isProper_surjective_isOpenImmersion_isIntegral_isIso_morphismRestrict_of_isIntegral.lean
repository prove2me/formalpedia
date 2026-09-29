-- Prove2me | solution 1 for AlgebraicGeometry.exists_isProper_surjective_isOpenImmersion_isIntegral_isIso_morphismRestrict_of_isIntegral
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/ec9d80bd-ea73-55df-a630-76543dd49104

import Mathlib
import Definitions.Def_AlgebraicGeometry_ProjSpace
import Theorems.Thm_AlgebraicGeometry_ProjSpace_exists_algHom_away_apply_ratio_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_exists_isProper_surjective_isOpenImmersion_isIntegral_isIso_morphismRestrict_of_isIntegral

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Topology HomogeneousLocalization

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

noncomputable section

namespace SolCHint

abbrev grading (A : Type u) [CommRing A] (n : ℕ) := MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A

abbrev PP (A : Type u) [CommRing A] (n : ℕ) : Scheme.{u} := Proj (grading A n)

abbrev W (A : Type u) [CommRing A] (n : ℕ) : (PP A n).Opens :=
  Proj.basicOpen (grading A n) (MvPolynomial.X 0)

abbrev awayι₀ (A : Type u) [CommRing A] (n : ℕ) :
    Spec (.of (Away (grading A n) (MvPolynomial.X (0 : Fin (n + 1))))) ⟶ PP A n :=
  Proj.awayι (grading A n) (MvPolynomial.X 0) (ProjSpace.X_mem_one A n 0) one_pos

section Chart

variable {A : Type u} [CommRing A] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of A))

lemma ι_comp_eq_isoSpec_hom (U : X.Opens) (hU : IsAffineOpen U) :
    U.ι ≫ f = hU.isoSpec.hom ≫ Spec.map (f.appLE ⊤ U le_top) ≫
      Spec.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv := by
  rw [← IsAffineOpen.toSpecΓ_fromSpec hU, Category.assoc,
    ← IsAffineOpen.SpecMap_appLE_fromSpec f (isAffineOpen_top _) hU le_top,
    IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv, IsAffineOpen.isoSpec_hom]

theorem exists_chart [LocallyOfFiniteType f] (U : X.Opens) (hU : IsAffineOpen U) :
    ∃ (n : ℕ) (c : (U : Scheme.{u}) ⟶
        Spec (.of (Away (grading A n) (MvPolynomial.X (0 : Fin (n + 1)))))),
      IsClosedImmersion c ∧ c ≫ awayι₀ A n ≫ ProjSpace.π A n = U.ι ≫ f := by

  let φ₀ : A →+* Γ(X, U) :=
    ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ f.appLE ⊤ U le_top).hom
  letI : Algebra A Γ(X, U) := φ₀.toAlgebra
  have hft : Algebra.FiniteType A Γ(X, U) := by
    have h1 : (f.appLE ⊤ U le_top).hom.FiniteType :=
      f.finiteType_appLE (isAffineOpen_top _) hU le_top
    have h2 : φ₀.FiniteType := by
      show ((f.appLE ⊤ U le_top).hom.comp (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom).FiniteType
      exact h1.comp (RingHom.FiniteType.of_surjective _
        (Scheme.ΓSpecIso (CommRingCat.of A)).symm.commRingCatIsoToRingEquiv.surjective)
    exact h2
  obtain ⟨n, φ, hφ⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp hft

  let b : Fin (n + 1) → Γ(X, U) := Fin.cases 1 fun i => φ (MvPolynomial.X i)
  obtain ⟨θ, hθ⟩ := ProjSpace.exists_algHom_away_apply_ratio_eq A n 0 b rfl
  have hθsurj : Function.Surjective θ := by
    have hrange : φ.range ≤ θ.range := by
      have : φ.range = (Algebra.adjoin A (Set.range
          (MvPolynomial.X : Fin n → MvPolynomial (Fin n) A))).map φ := by
        rw [MvPolynomial.adjoin_range_X, Algebra.map_top]
      rw [this, AlgHom.map_adjoin, Algebra.adjoin_le_iff]
      rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
      exact ⟨ProjSpace.ratio A n 0 i.succ, by simpa [b] using hθ i.succ⟩
    intro c
    obtain ⟨p, rfl⟩ := hφ c
    exact hrange ⟨p, rfl⟩
  refine ⟨n, hU.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom θ.toRingHom), ?_, ?_⟩
  · haveI : IsClosedImmersion (Spec.map (CommRingCat.ofHom θ.toRingHom)) :=
      IsClosedImmersion.spec_of_surjective _ hθsurj
    infer_instance
  · rw [ι_comp_eq_isoSpec_hom f U hU, Category.assoc, ProjSpace.awayι_comp_π,
      ← Spec.map_comp, ← Spec.map_comp]
    congr 2
    rw [← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_hom
      ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ f.appLE ⊤ U le_top)]
    congr 1
    exact θ.comp_algebraMap

end Chart

section Setup

variable {A : Type u} [CommRing A] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of A))

structure ChartData where

  m : ℕ

  U : Fin m → X.Opens
  hne : ∀ k, ((U k : X.Opens) : Set X).Nonempty
  hcov : ⨆ k, U k = ⊤

  e : Fin m → ℕ

  c : ∀ k, ((U k : X.Opens) : Scheme.{u}) ⟶
    Spec (.of (Away (grading A (e k)) (MvPolynomial.X (0 : Fin (e k + 1)))))
  hc : ∀ k, IsClosedImmersion (c k)
  hover : ∀ k, c k ≫ awayι₀ A (e k) ≫ ProjSpace.π A (e k) = (U k).ι ≫ f

attribute [scoped instance] ChartData.hc

theorem nonempty_chartData [LocallyOfFiniteType f] [CompactSpace X] : Nonempty (ChartData f) := by
  let 𝒰 := X.affineCover.finiteSubcover
  let ε := Fintype.equivFin 𝒰.I₀
  let U : Fin (Fintype.card 𝒰.I₀) → X.Opens := fun k => (𝒰.f (ε.symm k)).opensRange
  have hU : ∀ k, IsAffineOpen (U k) := fun k => isAffineOpen_opensRange _
  choose e c hc hover using fun k => exists_chart f (U k) (hU k)
  have hne : ∀ k, ((U k : X.Opens) : Set X).Nonempty := fun k =>
    ⟨(ε.symm k).1, X.affineCover.covers (ε.symm k).1⟩
  have hcov : ⨆ k, U k = ⊤ := by
    rw [← 𝒰.iSup_opensRange]
    exact (Equiv.iSup_comp (g := fun i => (𝒰.f i).opensRange) ε.symm)
  exact ⟨⟨_, U, hne, hcov, e, c, hc, hover⟩⟩

namespace ChartData

variable {f} (D : ChartData f)

def ι (k : Fin D.m) : ((D.U k : X.Opens) : Scheme.{u}) ⟶ PP A (D.e k) := D.c k ≫ awayι₀ A (D.e k)

scoped instance (k : Fin D.m) : IsImmersion (D.ι k) := by unfold ι; infer_instance

lemma ι_comp_π (k : Fin D.m) : D.ι k ≫ ProjSpace.π A (D.e k) = (D.U k).ι ≫ f := by
  rw [ι, Category.assoc, D.hover]

lemma range_ι_subset (k : Fin D.m) : Set.range (D.ι k) ⊆ (W A (D.e k) : Set (PP A (D.e k))) := by
  rw [ι, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp]
  refine (Set.image_subset_range _ _).trans ?_
  rw [← Scheme.Hom.coe_opensRange, Proj.opensRange_awayι]

abbrev PiS : Scheme.{u} := ProjSpace.prodOver A D.e

abbrev prπ : D.PiS ⟶ Spec (CommRingCat.of A) := ProjSpace.prodOverπ A D.e

abbrev pr (k : Fin D.m) : D.PiS ⟶ PP A (D.e k) := ProjSpace.prodPr A D.e k

def Ω (k : Fin D.m) : D.PiS.Opens := D.pr k ⁻¹ᵁ W A (D.e k)

def Uo : X.Opens := Finset.univ.inf D.U

lemma Uo_le (k : Fin D.m) : D.Uo ≤ D.U k := Finset.inf_le (Finset.mem_univ k)

lemma mem_Uo {x : X} : x ∈ D.Uo ↔ ∀ k, x ∈ D.U k := by
  rw [Uo, ← SetLike.mem_coe, Opens.coe_finset_inf, Finset.inf_set_eq_iInter]
  simp

def g : (D.Uo : Scheme.{u}) ⟶ D.PiS :=
  ProjSpace.prodLift A (D.Uo.ι ≫ f) D.e (fun k => X.homOfLE (D.Uo_le k) ≫ D.ι k)
    (fun k => by rw [Category.assoc, D.ι_comp_π, ← Category.assoc, Scheme.homOfLE_ι])

lemma g_comp_prπ : D.g ≫ D.prπ = D.Uo.ι ≫ f := ProjSpace.prodLift_comp_prodOverπ ..

lemma g_comp_pr (k : Fin D.m) : D.g ≫ D.pr k = X.homOfLE (D.Uo_le k) ≫ D.ι k :=
  ProjSpace.prodLift_comp_prodPr ..

abbrev XP : Scheme.{u} := pullback f D.prπ

def ψ : (D.Uo : Scheme.{u}) ⟶ D.XP := pullback.lift D.Uo.ι D.g D.g_comp_prπ.symm

@[scoped simp] lemma ψ_fst : D.ψ ≫ pullback.fst f D.prπ = D.Uo.ι := pullback.lift_fst ..
@[scoped simp] lemma ψ_snd : D.ψ ≫ pullback.snd f D.prπ = D.g := pullback.lift_snd ..

scoped instance : IsImmersion D.ψ := by
  have : IsImmersion (D.ψ ≫ pullback.fst f D.prπ) := by rw [ψ_fst]; infer_instance
  exact IsImmersion.of_comp _ (pullback.fst f D.prπ)

abbrev X' : Scheme.{u} := D.ψ.image

abbrev α : D.X' ⟶ D.XP := D.ψ.imageι

abbrev ψ' : (D.Uo : Scheme.{u}) ⟶ D.X' := D.ψ.toImage

lemma ψ'_α : D.ψ' ≫ D.α = D.ψ := D.ψ.toImage_imageι

def π : D.X' ⟶ X := D.α ≫ pullback.fst f D.prπ

def ιι : D.X' ⟶ D.PiS := D.α ≫ pullback.snd f D.prπ

scoped instance : IsProper D.π := by unfold π; infer_instance
scoped instance [IsSeparated f] : IsSeparated D.ιι := by unfold ιι; infer_instance

lemma π_comp_f : D.π ≫ f = D.ιι ≫ D.prπ := by
  simp only [π, ιι, Category.assoc, pullback.condition]

@[scoped simp] lemma ψ'_π : D.ψ' ≫ D.π = D.Uo.ι := by rw [π, ← Category.assoc, ψ'_α, ψ_fst]
@[scoped simp] lemma ψ'_ιι : D.ψ' ≫ D.ιι = D.g := by rw [ιι, ← Category.assoc, ψ'_α, ψ_snd]

def V (k : Fin D.m) : D.X'.Opens := D.π ⁻¹ᵁ D.U k

end ChartData
p2m_reactivate "P2MW.S_AlgebraicGeometry_exists_isProper_surjective_isOpenImmersion_isIntegral_isIso_morphismRestrict_of_isIntegral.SolCHint.ChartData"

end Setup
p2m_reactivate "P2MW.S_AlgebraicGeometry_exists_isProper_surjective_isOpenImmersion_isIntegral_isIso_morphismRestrict_of_isIntegral.SolCHint.ChartData"

section Instances

variable {A : Type u} [CommRing A] [IsNoetherianRing A] {X : Scheme.{u}} [IsIntegral X]
  {f : X ⟶ Spec (CommRingCat.of A)} [LocallyOfFiniteType f] [QuasiCompact f]
  (D : ChartData f)

namespace ChartData

lemma isNoetherian_X (D : ChartData f) : IsNoetherian X :=
  haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  {}

scoped instance noetherianSpace_Uo : NoetherianSpace (D.Uo : Scheme.{u}) := by
  haveI := D.isNoetherian_X
  show NoetherianSpace D.Uo
  exact (inferInstance : NoetherianSpace X).set _

scoped instance compactSpace_XP : CompactSpace D.XP := by
  haveI := D.isNoetherian_X
  infer_instance

lemma Uo_nonempty : ((D.Uo : X.Opens) : Set X).Nonempty := by
  classical
  have hirr : IsIrreducible (Set.univ : Set X) := IrreducibleSpace.isIrreducible_univ X
  have := (isIrreducible_iff_sInter.mp hirr) (Finset.univ.image fun k => ((D.U k : X.Opens) : Set X))
    (by simp only [Finset.mem_image, Finset.mem_univ, true_and, forall_exists_index,
          forall_apply_eq_imp_iff]
        exact fun k => (D.U k).isOpen)
    (by simp only [Finset.mem_image, Finset.mem_univ, true_and, forall_exists_index,
          forall_apply_eq_imp_iff, Set.univ_inter]
        exact fun k => D.hne k)
  simp only [Set.univ_inter, Finset.coe_image, Finset.coe_univ, Set.image_univ,
    Set.sInter_range] at this
  obtain ⟨x, hx⟩ := this
  exact ⟨x, D.mem_Uo.mpr (by simpa using hx)⟩

scoped instance nonempty_Uo : Nonempty (D.Uo : Scheme.{u}) := by
  obtain ⟨x, hx⟩ := D.Uo_nonempty
  exact ⟨⟨x, hx⟩⟩

scoped instance isIntegral_Uo : IsIntegral (D.Uo : Scheme.{u}) :=
  isIntegral_of_isOpenImmersion D.Uo.ι

scoped instance quasiCompact_ψ : QuasiCompact D.ψ := inferInstance
scoped instance : IsOpenImmersion D.ψ' := inferInstance
scoped instance : IsDominant D.ψ' := inferInstance

scoped instance isReduced_X' : IsReduced D.X' := by

  haveI : ∀ U' : D.XP.affineOpens,
      _root_.IsReduced ((Γ(D.XP, (U' : D.XP.Opens)) : Type u) ⧸ D.ψ.ker.ideal U') := fun U' => by
    rw [← Ideal.isRadical_iff_quotient_reduced, Scheme.Hom.ker_apply]
    intro x ⟨n, hn⟩
    rw [RingHom.mem_ker, map_pow] at hn
    exact RingHom.mem_ker.mpr (IsReduced.eq_zero _ ⟨n, hn⟩)
  haveI : ∀ U' : D.XP.affineOpens, IsReduced (D.ψ.ker.subschemeCover.openCover.X U') :=
    fun U' => by
    show IsReduced (Spec (.of ((Γ(D.XP, (U' : D.XP.Opens)) : Type u) ⧸ D.ψ.ker.ideal U')))
    infer_instance
  exact IsReduced.of_openCover _ D.ψ.ker.subschemeCover.openCover

scoped instance irreducibleSpace_X' : IrreducibleSpace D.X' := by
  have h : IsIrreducible (D.ψ.ker.support : Set D.XP) := by
    rw [Scheme.Hom.support_ker, ← Set.image_univ]
    exact ((IrreducibleSpace.isIrreducible_univ _).image _ D.ψ.continuous.continuousOn).closure
  exact Subtype.irreducibleSpace h

scoped instance isIntegral_X' : IsIntegral D.X' := isIntegral_of_irreducibleSpace_of_isReduced _

scoped instance compactSpace_X' : CompactSpace D.X' :=
  QuasiCompact.compactSpace_of_compactSpace D.ψ.imageι

end ChartData
p2m_reactivate "P2MW.S_AlgebraicGeometry_exists_isProper_surjective_isOpenImmersion_isIntegral_isIso_morphismRestrict_of_isIntegral.SolCHint.ChartData"

end Instances
p2m_reactivate "P2MW.S_AlgebraicGeometry_exists_isProper_surjective_isOpenImmersion_isIntegral_isIso_morphismRestrict_of_isIntegral.SolCHint.ChartData"

section Step1

variable {A : Type u} [CommRing A] [IsNoetherianRing A] {X : Scheme.{u}} [IsIntegral X]
  {f : X ⟶ Spec (CommRingCat.of A)} [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
  (D : ChartData f)

namespace ChartData

def πk (k : Fin D.m) : (D.V k : Scheme.{u}) ⟶ (D.U k : X.Opens) := D.π.resLE (D.U k) (D.V k) le_rfl

lemma πk_ι (k : Fin D.m) : D.πk k ≫ (D.U k).ι = (D.V k).ι ≫ D.π := Scheme.Hom.resLE_comp_ι ..

def ak (k : Fin D.m) : (D.V k : Scheme.{u}) ⟶ PP A (D.e k) := D.πk k ≫ D.ι k

def bk (k : Fin D.m) : (D.V k : Scheme.{u}) ⟶ PP A (D.e k) := (D.V k).ι ≫ D.ιι ≫ D.pr k

lemma range_ψ'_subset_V (k : Fin D.m) : Set.range D.ψ' ⊆ Set.range (D.V k).ι := by
  rintro _ ⟨u, rfl⟩
  rw [Scheme.Opens.range_ι]
  show D.π (D.ψ' u) ∈ D.U k
  rw [← Scheme.Hom.comp_apply, ψ'_π]
  exact D.Uo_le k u.2

def ψk (k : Fin D.m) : (D.Uo : Scheme.{u}) ⟶ (D.V k : Scheme.{u}) :=
  IsOpenImmersion.lift (D.V k).ι D.ψ' (D.range_ψ'_subset_V k)

@[scoped simp] lemma ψk_ι (k : Fin D.m) : D.ψk k ≫ (D.V k).ι = D.ψ' := IsOpenImmersion.lift_fac ..

scoped instance (k : Fin D.m) : IsDominant (D.ψk k) := by
  constructor
  have h : Set.range (D.ψk k) = (D.V k).ι ⁻¹' Set.range D.ψ' := by
    rw [← D.ψk_ι k, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
      Set.preimage_image_eq _ (D.V k).ι.isOpenEmbedding.injective]
  rw [DenseRange, h]
  exact D.ψ'.denseRange.preimage (D.V k).ι.isOpenEmbedding.isOpenMap

lemma ψk_πk (k : Fin D.m) : D.ψk k ≫ D.πk k = X.homOfLE (D.Uo_le k) := by
  rw [← cancel_mono (D.U k).ι, Category.assoc, πk_ι, ← Category.assoc, ψk_ι, ψ'_π,
    Scheme.homOfLE_ι]

theorem ak_eq_bk (k : Fin D.m) : D.ak k = D.bk k := by
  refine ext_of_isDominant_of_isSeparated (ProjSpace.π A (D.e k)) ?_ (D.ψk k) ?_
  · rw [ak, bk, Category.assoc, ι_comp_π, ← Category.assoc, πk_ι, Category.assoc, Category.assoc,
      Category.assoc, ProjSpace.prodPr_comp_π, π_comp_f]
  · rw [ak, bk, ← Category.assoc, ψk_πk, ← Category.assoc, ψk_ι, ← Category.assoc, ψ'_ιι, g_comp_pr]

lemma pr_ιι_apply (k : Fin D.m) (x : D.X') (hx : x ∈ D.V k) :
    D.pr k (D.ιι x) = D.ι k (D.πk k ⟨x, hx⟩) := by
  have := congrArg (fun h => h ⟨x, hx⟩) (D.ak_eq_bk k)
  simp only [ak, bk, Scheme.Hom.comp_base, TopCat.coe_comp, Function.comp_apply,
    Scheme.Opens.ι_apply] at this
  exact this.symm

lemma V_le_preimage_Ω (k : Fin D.m) : D.V k ≤ D.ιι ⁻¹ᵁ D.Ω k := by
  intro x hx
  show D.pr k (D.ιι x) ∈ W A (D.e k)
  rw [D.pr_ιι_apply k x hx]
  exact D.range_ι_subset k ⟨_, rfl⟩

end ChartData
p2m_reactivate "P2MW.S_AlgebraicGeometry_exists_isProper_surjective_isOpenImmersion_isIntegral_isIso_morphismRestrict_of_isIntegral.SolCHint.ChartData"

end Step1
p2m_reactivate "P2MW.S_AlgebraicGeometry_exists_isProper_surjective_isOpenImmersion_isIntegral_isIso_morphismRestrict_of_isIntegral.SolCHint.ChartData"

section Step3

variable {A : Type u} [CommRing A] [IsNoetherianRing A] {X : Scheme.{u}} [IsIntegral X]
  {f : X ⟶ Spec (CommRingCat.of A)} [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
  (D : ChartData f)

namespace ChartData

def ιΩ (k : Fin D.m) : (D.V k : Scheme.{u}) ⟶ (D.Ω k : Scheme.{u}) :=
  D.ιι.resLE (D.Ω k) (D.V k) (D.V_le_preimage_Ω k)

lemma ιΩ_ι (k : Fin D.m) : D.ιΩ k ≫ (D.Ω k).ι = (D.V k).ι ≫ D.ιι := Scheme.Hom.resLE_comp_ι ..

abbrev T (k : Fin D.m) : Scheme.{u} := pullback ((D.U k).ι ≫ f) ((D.Ω k).ι ≫ D.prπ)

def mT (k : Fin D.m) : D.T k ⟶ D.XP :=
  pullback.map _ _ _ _ (D.U k).ι (D.Ω k).ι (𝟙 _) (by simp) (by simp)

scoped instance (k : Fin D.m) : IsOpenImmersion (D.mT k) := by unfold mT; infer_instance

@[scoped simp] lemma mT_fst (k : Fin D.m) : D.mT k ≫ pullback.fst f D.prπ = pullback.fst _ _ ≫ (D.U k).ι :=
  pullback.lift_fst ..
@[scoped simp] lemma mT_snd (k : Fin D.m) : D.mT k ≫ pullback.snd f D.prπ = pullback.snd _ _ ≫ (D.Ω k).ι :=
  pullback.lift_snd ..

lemma range_mT (k : Fin D.m) : Set.range (D.mT k) =
    pullback.fst f D.prπ ⁻¹' (D.U k : Set X) ∩ pullback.snd f D.prπ ⁻¹' (D.Ω k : Set D.PiS) := by
  rw [mT, Scheme.Pullback.range_map, Scheme.Opens.range_ι, Scheme.Opens.range_ι]

def tk (k : Fin D.m) : (D.V k : Scheme.{u}) ⟶ D.T k :=
  pullback.lift (D.πk k) (D.ιΩ k) (by
    rw [← Category.assoc, πk_ι, ← Category.assoc, ιΩ_ι, Category.assoc, Category.assoc, π_comp_f])

lemma tk_mT (k : Fin D.m) : D.tk k ≫ D.mT k = (D.V k).ι ≫ D.α := by
  apply pullback.hom_ext
  · rw [Category.assoc, mT_fst, ← Category.assoc, tk, pullback.lift_fst, πk_ι, Category.assoc]; rfl
  · rw [Category.assoc, mT_snd, ← Category.assoc, tk, pullback.lift_snd, ιΩ_ι, Category.assoc]; rfl

scoped instance (k : Fin D.m) : IsClosedImmersion (D.tk k) := by
  haveI : IsImmersion (D.tk k ≫ D.mT k) := by rw [tk_mT]; infer_instance
  haveI : IsImmersion (D.tk k) := IsImmersion.of_comp _ (D.mT k)
  refine IsClosedImmersion.of_isPreimmersion _ ?_

  have hrange : Set.range (D.tk k) = D.mT k ⁻¹' Set.range D.α := by
    apply Set.eq_of_subset_of_subset
    · rintro _ ⟨v, rfl⟩
      refine ⟨(D.V k).ι v, ?_⟩
      rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, tk_mT]
    · rintro w ⟨x, hx⟩
      have hxV : x ∈ D.V k := by
        show D.π x ∈ D.U k
        have : (D.mT k ≫ pullback.fst f D.prπ) w ∈ (D.U k : Set X) := by
          rw [mT_fst]
          exact ((pullback.fst ((D.U k).ι ≫ f) ((D.Ω k).ι ≫ D.prπ)) w).2
        rw [Scheme.Hom.comp_apply, ← hx] at this
        exact this
      refine ⟨⟨x, hxV⟩, (D.mT k).isOpenEmbedding.injective ?_⟩
      rw [← Scheme.Hom.comp_apply, tk_mT, Scheme.Hom.comp_apply, ← hx]
      rfl
  rw [hrange]
  exact IsClosed.preimage (D.mT k).continuous D.α.isClosedEmbedding.isClosed_range

def rk (k : Fin D.m) : (D.Ω k : Scheme.{u}) ⟶
    Spec (.of (Away (grading A (D.e k)) (MvPolynomial.X (0 : Fin (D.e k + 1))))) :=
  IsOpenImmersion.lift (awayι₀ A (D.e k)) ((D.Ω k).ι ≫ D.pr k) (by
    rintro _ ⟨w, rfl⟩
    rw [← Scheme.Hom.coe_opensRange, Proj.opensRange_awayι]
    exact w.2)

@[scoped simp] lemma rk_awayι (k : Fin D.m) : D.rk k ≫ awayι₀ A (D.e k) = (D.Ω k).ι ≫ D.pr k :=
  IsOpenImmersion.lift_fac ..

abbrev G (k : Fin D.m) : Scheme.{u} := pullback (D.c k) (D.rk k)

def tk' (k : Fin D.m) : (D.V k : Scheme.{u}) ⟶ D.G k :=
  pullback.lift (D.πk k) (D.ιΩ k) (by
    rw [← cancel_mono (awayι₀ A (D.e k)), Category.assoc, Category.assoc, rk_awayι,
      ← Category.assoc (D.ιΩ k), ιΩ_ι, Category.assoc]
    exact D.ak_eq_bk k)

abbrev ik (k : Fin D.m) : Spec (.of (Away (grading A (D.e k)) (MvPolynomial.X (0 : Fin (D.e k + 1)))))
    ⟶ Spec (CommRingCat.of A) := awayι₀ A (D.e k) ≫ ProjSpace.π A (D.e k)

lemma c_ik (k : Fin D.m) : D.c k ≫ D.ik k = (D.U k).ι ≫ f := D.hover k

lemma rk_ik (k : Fin D.m) : D.rk k ≫ D.ik k = (D.Ω k).ι ≫ D.prπ := by
  rw [← Category.assoc, rk_awayι, Category.assoc, ProjSpace.prodPr_comp_π]

lemma tk'_comp (k : Fin D.m) :
    D.tk' k ≫ pullback.mapDesc (D.c k) (D.rk k) (D.ik k) ≫
      (pullback.congrHom (D.c_ik k) (D.rk_ik k)).hom = D.tk k := by
  apply pullback.hom_ext
  · simp only [tk', tk, pullback.mapDesc, Category.assoc, pullback.congrHom_hom,
      pullback.lift_fst, Category.comp_id]
  · simp only [tk', tk, pullback.mapDesc, Category.assoc, pullback.congrHom_hom,
      pullback.lift_snd, Category.comp_id]

scoped instance (k : Fin D.m) : IsClosedImmersion (D.tk' k) := by
  haveI : IsClosedImmersion (D.tk' k ≫ (pullback.mapDesc (D.c k) (D.rk k) (D.ik k) ≫
      (pullback.congrHom (D.c_ik k) (D.rk_ik k)).hom)) := by
    rw [tk'_comp]; infer_instance
  exact IsClosedImmersion.of_comp_isClosedImmersion _
    (pullback.mapDesc (D.c k) (D.rk k) (D.ik k) ≫ (pullback.congrHom (D.c_ik k) (D.rk_ik k)).hom)

theorem isClosedImmersion_ιΩ (k : Fin D.m) : IsClosedImmersion (D.ιΩ k) := by
  have : D.ιΩ k = D.tk' k ≫ pullback.snd (D.c k) (D.rk k) := (pullback.lift_snd _ _ _).symm
  rw [this]
  infer_instance

end ChartData
p2m_reactivate "P2MW.S_AlgebraicGeometry_exists_isProper_surjective_isOpenImmersion_isIntegral_isIso_morphismRestrict_of_isIntegral.SolCHint.ChartData"

end Step3
p2m_reactivate "P2MW.S_AlgebraicGeometry_exists_isProper_surjective_isOpenImmersion_isIntegral_isIso_morphismRestrict_of_isIntegral.SolCHint.ChartData"

section Step2

variable {A : Type u} [CommRing A] [IsNoetherianRing A] {X : Scheme.{u}} [IsIntegral X]
  {f : X ⟶ Spec (CommRingCat.of A)} [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
  (D : ChartData f)

namespace ChartData

abbrev O (k : Fin D.m) : D.X'.Opens := D.ιι ⁻¹ᵁ D.Ω k

abbrev ek (k : Fin D.m) : (D.V k : Scheme.{u}) ⟶ (D.O k : Scheme.{u}) := D.X'.homOfLE (D.V_le_preimage_Ω k)

lemma ek_comp (k : Fin D.m) : D.ek k ≫ (D.ιι ∣_ D.Ω k) = D.ιΩ k := rfl

lemma V_nonempty (k : Fin D.m) : ((D.V k : D.X'.Opens) : Set D.X').Nonempty := by
  obtain ⟨u⟩ := D.nonempty_Uo
  exact ⟨(D.ψk k u).1, (D.ψk k u).2⟩

scoped instance nonempty_O (k : Fin D.m) : Nonempty (D.O k : Scheme.{u}) := by
  obtain ⟨x, hx⟩ := D.V_nonempty k
  exact ⟨⟨x, D.V_le_preimage_Ω k hx⟩⟩

scoped instance isProper_ek (k : Fin D.m) : IsProper (D.ek k) := by
  haveI : IsClosedImmersion (D.ιΩ k) := D.isClosedImmersion_ιΩ k
  haveI : IsProper (D.ek k ≫ (D.ιι ∣_ D.Ω k)) := by rw [ek_comp]; infer_instance
  exact IsProper.of_comp _ (D.ιι ∣_ D.Ω k)

theorem V_eq_O (k : Fin D.m) : D.V k = D.O k := by
  refine le_antisymm (D.V_le_preimage_Ω k) ?_

  have hclopen : IsClopen (Set.range (D.ek k)) :=
    ⟨(D.ek k).isClosedMap.isClosed_range, (D.ek k).isOpenEmbedding.isOpen_range⟩
  have hne : (Set.range (D.ek k)).Nonempty := by
    obtain ⟨x, hx⟩ := D.V_nonempty k
    exact ⟨_, ⟨⟨x, hx⟩, rfl⟩⟩
  have huniv := hclopen.eq_univ hne
  intro x hx
  obtain ⟨v, hv⟩ : (⟨x, hx⟩ : (D.O k : Scheme.{u})) ∈ Set.range (D.ek k) := by
    rw [huniv]; trivial
  have h1 : ((D.ek k) v).1 = x := congrArg Subtype.val hv
  rw [Scheme.homOfLE_apply] at h1
  rw [← h1]
  exact v.2

end ChartData
p2m_reactivate "P2MW.S_AlgebraicGeometry_exists_isProper_surjective_isOpenImmersion_isIntegral_isIso_morphismRestrict_of_isIntegral.SolCHint.ChartData"

end Step2
p2m_reactivate "P2MW.S_AlgebraicGeometry_exists_isProper_surjective_isOpenImmersion_isIntegral_isIso_morphismRestrict_of_isIntegral.SolCHint.ChartData"

section Step4

variable {A : Type u} [CommRing A] [IsNoetherianRing A] {X : Scheme.{u}} [IsIntegral X]
  {f : X ⟶ Spec (CommRingCat.of A)} [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
  (D : ChartData f)

namespace ChartData

scoped instance isClosedImmersion_restrict (k : Fin D.m) : IsClosedImmersion (D.ιι ∣_ D.Ω k) := by
  haveI : IsClosedImmersion (D.ιΩ k) := D.isClosedImmersion_ιΩ k

  haveI : Epi (D.ek k).base := by
    rw [TopCat.epi_iff_surjective]
    rintro ⟨x, hx⟩
    have hx' : x ∈ D.V k := by rw [D.V_eq_O k]; exact hx
    exact ⟨⟨x, hx'⟩, Subtype.ext (Scheme.homOfLE_apply _ _)⟩
  haveI : IsIso (D.ek k) := (isIso_iff_isOpenImmersion_and_epi_base _).mpr ⟨inferInstance, ‹_›⟩
  rw [← MorphismProperty.cancel_left_of_respectsIso @IsClosedImmersion (D.ek k), ek_comp]
  infer_instance

def Ωall : D.PiS.Opens := ⨆ k, D.Ω k

lemma range_ιι_subset : Set.range D.ιι ⊆ Set.range D.Ωall.ι := by
  rintro _ ⟨x, rfl⟩
  rw [Scheme.Opens.range_ι, Ωall, SetLike.mem_coe, Opens.mem_iSup]

  have hx : D.π x ∈ (⊤ : X.Opens) := trivial
  rw [← D.hcov, Opens.mem_iSup] at hx
  obtain ⟨k, hk⟩ := hx
  exact ⟨k, D.V_le_preimage_Ω k hk⟩

def ιall : D.X' ⟶ (D.Ωall : Scheme.{u}) := IsOpenImmersion.lift D.Ωall.ι D.ιι D.range_ιι_subset

@[scoped simp] lemma ιall_ι : D.ιall ≫ D.Ωall.ι = D.ιι := IsOpenImmersion.lift_fac ..

scoped instance isClosedImmersion_ιall : IsClosedImmersion D.ιall := by
  refine IsZariskiLocalAtTarget.of_iSup_eq_top (fun k => D.Ωall.ι ⁻¹ᵁ D.Ω k) ?_ fun k => ?_
  · apply le_antisymm le_top
    rintro ⟨w, hw⟩ -
    rw [Opens.mem_iSup]
    obtain ⟨k, hk⟩ := Opens.mem_iSup.mp (show w ∈ D.Ωall from hw)
    exact ⟨k, hk⟩
  · have h1 : IsClosedImmersion ((D.ιall ≫ D.Ωall.ι) ∣_ D.Ω k) := by rw [ιall_ι]; infer_instance
    rw [morphismRestrict_comp] at h1
    haveI : IsIso (D.Ωall.ι ∣_ D.Ω k) := by
      haveI : Epi (D.Ωall.ι ∣_ D.Ω k).base := by
        rw [TopCat.epi_iff_surjective]
        rintro ⟨w, hw⟩
        have hw' : w ∈ D.Ωall := by rw [Ωall, Opens.mem_iSup]; exact ⟨k, hw⟩
        exact ⟨⟨⟨w, hw'⟩, hw⟩, Subtype.ext (morphismRestrict_base_coe _ _ _)⟩
      exact (isIso_iff_isOpenImmersion_and_epi_base _).mpr ⟨inferInstance, ‹_›⟩
    exact (MorphismProperty.cancel_right_of_respectsIso @IsClosedImmersion _ (D.Ωall.ι ∣_ D.Ω k)).mp h1

scoped instance isImmersion_ιι : IsImmersion D.ιι := by rw [← ιall_ι]; infer_instance

scoped instance isNoetherian_X' : IsNoetherian D.X' := by
  haveI := D.isNoetherian_X
  haveI : IsLocallyNoetherian D.PiS := LocallyOfFiniteType.isLocallyNoetherian D.prπ
  haveI : IsLocallyNoetherian D.XP := inferInstance
  haveI : IsLocallyNoetherian D.X' := LocallyOfFiniteType.isLocallyNoetherian D.α
  exact {}

scoped instance quasiCompact_ιι : QuasiCompact D.ιι := inferInstance

scoped instance surjective_π : Surjective D.π := by
  haveI := D.isNoetherian_X
  constructor
  rw [← Set.range_eq_univ]
  have hdense : Dense ((D.Uo : X.Opens) : Set X) := (D.Uo).isOpen.dense D.Uo_nonempty
  have hsub : ((D.Uo : X.Opens) : Set X) ⊆ Set.range D.π := by
    rw [← Scheme.Opens.range_ι, ← D.ψ'_π, Scheme.Hom.comp_base, TopCat.coe_comp]
    exact Set.range_comp_subset_range _ _
  have hclosed : IsClosed (Set.range D.π) := D.π.isClosedMap.isClosed_range
  exact Set.eq_univ_of_univ_subset ((hdense.mono hsub).closure_eq ▸ hclosed.closure_subset)

abbrev Vu : D.X'.Opens := D.π ⁻¹ᵁ D.Uo

lemma range_ψ'_subset_Vu : Set.range D.ψ' ⊆ Set.range D.Vu.ι := by
  rintro _ ⟨u, rfl⟩
  rw [Scheme.Opens.range_ι]
  show D.π.base (D.ψ'.base u) ∈ D.Uo
  rw [← Scheme.Hom.comp_apply, D.ψ'_π]
  exact u.2

def ψu : (D.Uo : Scheme.{u}) ⟶ (D.Vu : Scheme.{u}) := IsOpenImmersion.lift D.Vu.ι D.ψ' D.range_ψ'_subset_Vu

@[scoped simp] lemma ψu_ι : D.ψu ≫ D.Vu.ι = D.ψ' := IsOpenImmersion.lift_fac ..

scoped instance : IsOpenImmersion D.ψu := by
  haveI : IsOpenImmersion (D.ψu ≫ D.Vu.ι) := by rw [ψu_ι]; infer_instance
  exact IsOpenImmersion.of_comp D.ψu D.Vu.ι

lemma ψu_restrict : D.ψu ≫ (D.π ∣_ D.Uo) = 𝟙 _ := by
  rw [← cancel_mono D.Uo.ι, Category.assoc, morphismRestrict_ι, ← Category.assoc, ψu_ι, ψ'_π,
    Category.id_comp]

scoped instance : IsClosedImmersion D.ψu := by
  haveI : IsClosedImmersion (D.ψu ≫ (D.π ∣_ D.Uo)) := by rw [ψu_restrict]; infer_instance
  exact IsClosedImmersion.of_comp (f := D.ψu) (g := D.π ∣_ D.Uo)

scoped instance nonempty_Vu : Nonempty (D.Vu : Scheme.{u}) := ⟨D.ψu.base (Classical.arbitrary _)⟩

scoped instance isIso_ψu : IsIso D.ψu := by
  haveI : IsIntegral (D.Vu : Scheme.{u}) := isIntegral_of_isOpenImmersion D.Vu.ι
  have hclopen : IsClopen (Set.range D.ψu.base) :=
    ⟨D.ψu.isClosedEmbedding.isClosed_range, D.ψu.isOpenEmbedding.isOpen_range⟩
  have huniv : Set.range D.ψu.base = Set.univ := hclopen.eq_univ (Set.range_nonempty _)
  haveI : Epi D.ψu.base := (TopCat.epi_iff_surjective _).mpr (Set.range_eq_univ.mp huniv)
  exact (isIso_iff_isOpenImmersion_and_epi_base _).mpr ⟨inferInstance, ‹_›⟩

theorem isIso_restrict_Uo : IsIso (D.π ∣_ D.Uo) := by
  rw [IsIso.eq_inv_of_hom_inv_id D.ψu_restrict]
  infer_instance

lemma Uo_ne_bot : D.Uo ≠ ⊥ := by
  intro h
  obtain ⟨x, hx⟩ := D.Uo_nonempty
  rw [h] at hx
  exact hx

scoped instance isReduced_P : IsReduced D.ιι.image := by
  haveI : ∀ U' : D.PiS.affineOpens,
      _root_.IsReduced ((Γ(D.PiS, (U' : D.PiS.Opens)) : Type u) ⧸ D.ιι.ker.ideal U') := fun U' => by
    rw [← Ideal.isRadical_iff_quotient_reduced, Scheme.Hom.ker_apply]
    intro x ⟨n, hn⟩
    rw [RingHom.mem_ker, map_pow] at hn
    exact RingHom.mem_ker.mpr (IsReduced.eq_zero _ ⟨n, hn⟩)
  haveI : ∀ U' : D.PiS.affineOpens, IsReduced (D.ιι.ker.subschemeCover.openCover.X U') :=
    fun U' => by
    show IsReduced (Spec (.of ((Γ(D.PiS, (U' : D.PiS.Opens)) : Type u) ⧸ D.ιι.ker.ideal U')))
    infer_instance
  exact IsReduced.of_openCover _ D.ιι.ker.subschemeCover.openCover

scoped instance irreducibleSpace_P : IrreducibleSpace D.ιι.image := by
  have h : IsIrreducible (D.ιι.ker.support : Set D.PiS) := by
    rw [Scheme.Hom.support_ker, ← Set.image_univ]
    exact ((IrreducibleSpace.isIrreducible_univ _).image _ D.ιι.continuous.continuousOn).closure
  exact Subtype.irreducibleSpace h

scoped instance isIntegral_P : IsIntegral D.ιι.image := isIntegral_of_irreducibleSpace_of_isReduced _

include D in

theorem chow_bir : ∃ (X' P : Scheme.{u}) (π : X' ⟶ X) (j : X' ⟶ P) (q : P ⟶ Spec (CommRingCat.of A)),
    IsProper π ∧ Surjective π ∧ IsOpenImmersion j ∧ IsProper q ∧ j ≫ q = π ≫ f ∧
    IsIntegral X' ∧ IsIntegral P ∧ ∃ U : X.Opens, U ≠ ⊥ ∧ IsIso (π ∣_ U) :=
  ⟨D.X', D.ιι.image, D.π, D.ιι.toImage, D.ιι.imageι ≫ D.prπ, inferInstance, inferInstance,
    inferInstance, inferInstance, by rw [← Category.assoc, Scheme.Hom.toImage_imageι, π_comp_f],
    inferInstance, inferInstance, D.Uo, D.Uo_ne_bot, D.isIso_restrict_Uo⟩

include D in

theorem chow : ∃ (X' P : Scheme.{u}) (π : X' ⟶ X) (j : X' ⟶ P) (q : P ⟶ Spec (CommRingCat.of A)),
    IsProper π ∧ Surjective π ∧ IsOpenImmersion j ∧ IsProper q ∧ j ≫ q = π ≫ f :=
  ⟨D.X', D.ιι.image, D.π, D.ιι.toImage, D.ιι.imageι ≫ D.prπ, inferInstance, inferInstance,
    inferInstance, inferInstance, by rw [← Category.assoc, Scheme.Hom.toImage_imageι, π_comp_f]⟩

end ChartData
p2m_reactivate "P2MW.S_AlgebraicGeometry_exists_isProper_surjective_isOpenImmersion_isIntegral_isIso_morphismRestrict_of_isIntegral.SolCHint.ChartData"

end Step4
p2m_reactivate "P2MW.S_AlgebraicGeometry_exists_isProper_surjective_isOpenImmersion_isIntegral_isIso_morphismRestrict_of_isIntegral.SolCHint.ChartData"

theorem main_bir {A : Type u} [CommRing A] [IsNoetherianRing A]
    {X : Scheme.{u}} [IsIntegral X] (f : X ⟶ Spec (CommRingCat.of A))
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f] :
    ∃ (X' P : Scheme.{u}) (π : X' ⟶ X) (j : X' ⟶ P) (q : P ⟶ Spec (CommRingCat.of A)),
      IsProper π ∧ Surjective π ∧ IsOpenImmersion j ∧ IsProper q ∧ j ≫ q = π ≫ f ∧
      IsIntegral X' ∧ IsIntegral P ∧ ∃ U : X.Opens, U ≠ ⊥ ∧ IsIso (π ∣_ U) := by
  haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  obtain ⟨D⟩ := nonempty_chartData f
  exact D.chow_bir

end SolCHint
p2m_reactivate "P2MW.S_AlgebraicGeometry_exists_isProper_surjective_isOpenImmersion_isIntegral_isIso_morphismRestrict_of_isIntegral.SolCHint.ChartData P2MW.S_AlgebraicGeometry_exists_isProper_surjective_isOpenImmersion_isIntegral_isIso_morphismRestrict_of_isIntegral.SolCHint"

end
p2m_reactivate "P2MW.S_AlgebraicGeometry_exists_isProper_surjective_isOpenImmersion_isIntegral_isIso_morphismRestrict_of_isIntegral.SolCHint.ChartData P2MW.S_AlgebraicGeometry_exists_isProper_surjective_isOpenImmersion_isIntegral_isIso_morphismRestrict_of_isIntegral.SolCHint"

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry in
theorem solution
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    {X : Scheme.{u}} [IsIntegral X] (f : X ⟶ Spec (CommRingCat.of A))
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f] :
    ∃ (X' P : Scheme.{u}) (π : X' ⟶ X) (j : X' ⟶ P) (q : P ⟶ Spec (CommRingCat.of A)),
      IsProper π ∧ Surjective π ∧ IsOpenImmersion j ∧ IsProper q ∧ j ≫ q = π ≫ f ∧
      IsIntegral X' ∧ IsIntegral P ∧ ∃ U : X.Opens, U ≠ ⊥ ∧ IsIso (π ∣_ U) :=
  SolCHint.main_bir f

end S_AlgebraicGeometry_exists_isProper_surjective_isOpenImmersion_isIntegral_isIso_morphismRestrict_of_isIntegral
end P2MW
export P2MW.S_AlgebraicGeometry_exists_isProper_surjective_isOpenImmersion_isIntegral_isIso_morphismRestrict_of_isIntegral (solution)
