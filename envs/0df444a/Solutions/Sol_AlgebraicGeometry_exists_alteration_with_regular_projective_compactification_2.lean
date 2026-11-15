-- Prove2me | solution 2 for AlgebraicGeometry.exists_alteration_with_regular_projective_compactification
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-11-14T12:20:20.558199+00:00
-- url     : https://prove2.me/submissions/6987cbe2-5db2-49bb-bea1-411e94249162
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_AlgebraicGeometry_ProjSpace
import Definitions.Def_P2M_Util
import Mathlib
import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Theorems.Thm_AlgebraicGeometry_ProjSpace_exists_algHom_away_apply_ratio_eq
import Theorems.Thm_AlgebraicGeometry_exists_regular_projective_alteration_of_isProper

universe u

section

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_exists_isProper_surjective_isOpenImmersion_comp_eq_of_isIntegral

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Topology HomogeneousLocalization


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
p2m_reactivate "P2MW.S_AlgebraicGeometry_exists_isProper_surjective_isOpenImmersion_comp_eq_of_isIntegral.SolCHint.ChartData"

end Setup
p2m_reactivate "P2MW.S_AlgebraicGeometry_exists_isProper_surjective_isOpenImmersion_comp_eq_of_isIntegral.SolCHint.ChartData"

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
p2m_reactivate "P2MW.S_AlgebraicGeometry_exists_isProper_surjective_isOpenImmersion_comp_eq_of_isIntegral.SolCHint.ChartData"

end Instances
p2m_reactivate "P2MW.S_AlgebraicGeometry_exists_isProper_surjective_isOpenImmersion_comp_eq_of_isIntegral.SolCHint.ChartData"

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
p2m_reactivate "P2MW.S_AlgebraicGeometry_exists_isProper_surjective_isOpenImmersion_comp_eq_of_isIntegral.SolCHint.ChartData"

end Step1
p2m_reactivate "P2MW.S_AlgebraicGeometry_exists_isProper_surjective_isOpenImmersion_comp_eq_of_isIntegral.SolCHint.ChartData"

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
p2m_reactivate "P2MW.S_AlgebraicGeometry_exists_isProper_surjective_isOpenImmersion_comp_eq_of_isIntegral.SolCHint.ChartData"

end Step3
p2m_reactivate "P2MW.S_AlgebraicGeometry_exists_isProper_surjective_isOpenImmersion_comp_eq_of_isIntegral.SolCHint.ChartData"

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
p2m_reactivate "P2MW.S_AlgebraicGeometry_exists_isProper_surjective_isOpenImmersion_comp_eq_of_isIntegral.SolCHint.ChartData"

end Step2
p2m_reactivate "P2MW.S_AlgebraicGeometry_exists_isProper_surjective_isOpenImmersion_comp_eq_of_isIntegral.SolCHint.ChartData"

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

include D in

theorem chow : ∃ (X' P : Scheme.{u}) (π : X' ⟶ X) (j : X' ⟶ P) (q : P ⟶ Spec (CommRingCat.of A)),
    IsProper π ∧ Surjective π ∧ IsOpenImmersion j ∧ IsProper q ∧ j ≫ q = π ≫ f :=
  ⟨D.X', D.ιι.image, D.π, D.ιι.toImage, D.ιι.imageι ≫ D.prπ, inferInstance, inferInstance,
    inferInstance, inferInstance, by rw [← Category.assoc, Scheme.Hom.toImage_imageι, π_comp_f]⟩

end ChartData
p2m_reactivate "P2MW.S_AlgebraicGeometry_exists_isProper_surjective_isOpenImmersion_comp_eq_of_isIntegral.SolCHint.ChartData"

end Step4
p2m_reactivate "P2MW.S_AlgebraicGeometry_exists_isProper_surjective_isOpenImmersion_comp_eq_of_isIntegral.SolCHint.ChartData"

theorem main {A : Type u} [CommRing A] [IsNoetherianRing A]
    {X : Scheme.{u}} [IsIntegral X] (f : X ⟶ Spec (CommRingCat.of A))
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f] :
    ∃ (X' P : Scheme.{u}) (π : X' ⟶ X) (j : X' ⟶ P) (q : P ⟶ Spec (CommRingCat.of A)),
      IsProper π ∧ Surjective π ∧ IsOpenImmersion j ∧ IsProper q ∧ j ≫ q = π ≫ f := by
  haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  obtain ⟨D⟩ := nonempty_chartData f
  exact D.chow

end SolCHint
p2m_reactivate "P2MW.S_AlgebraicGeometry_exists_isProper_surjective_isOpenImmersion_comp_eq_of_isIntegral.SolCHint.ChartData P2MW.S_AlgebraicGeometry_exists_isProper_surjective_isOpenImmersion_comp_eq_of_isIntegral.SolCHint"

end
p2m_reactivate "P2MW.S_AlgebraicGeometry_exists_isProper_surjective_isOpenImmersion_comp_eq_of_isIntegral.SolCHint.ChartData P2MW.S_AlgebraicGeometry_exists_isProper_surjective_isOpenImmersion_comp_eq_of_isIntegral.SolCHint"

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry in
theorem solution
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    {X : Scheme.{u}} [IsIntegral X] (f : X ⟶ Spec (CommRingCat.of A))
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f] :
    ∃ (X' P : Scheme.{u}) (π : X' ⟶ X) (j : X' ⟶ P) (q : P ⟶ Spec (CommRingCat.of A)),
      IsProper π ∧ Surjective π ∧ IsOpenImmersion j ∧ IsProper q ∧ j ≫ q = π ≫ f :=
  SolCHint.main f

end S_AlgebraicGeometry_exists_isProper_surjective_isOpenImmersion_comp_eq_of_isIntegral
end P2MW
end

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace


namespace PhilipponReducedClosedSubscheme

theorem radical_eq_of_isReduced {X : Scheme.{u}} (I : X.IdealSheafData)
    [IsReduced I.subscheme] : I.radical = I := by
  apply Scheme.IdealSheafData.ext
  funext U
  change (I.ideal U).radical = I.ideal U
  apply Ideal.radical_eq_iff.mpr
  apply (Ideal.isRadical_iff_quotient_reduced (I.ideal U)).mpr
  exact isReduced_of_injective (I.subschemeObjIso U).inv.hom
    (I.subschemeObjIso U).symm.commRingCatIsoToRingEquiv.injective

theorem isReduced_of_radical_eq {X : Scheme.{u}} (I : X.IdealSheafData)
    (h : I.radical = I) : IsReduced I.subscheme := by
  have hU (U : X.affineOpens) : (I.ideal U).IsRadical := by
    apply Ideal.radical_eq_iff.mp
    exact congrArg (fun J : X.IdealSheafData => J.ideal U) h
  haveI (U : X.affineOpens) : _root_.IsReduced (Γ(X, U) ⧸ I.ideal U) :=
    (Ideal.isRadical_iff_quotient_reduced (I.ideal U)).mp (hU U)
  haveI (U : X.affineOpens) : IsReduced (I.subschemeCover.openCover.X U) := by
    change IsReduced (Spec (CommRingCat.of (Γ(X, U) ⧸ I.ideal U)))
    infer_instance
  exact IsReduced.of_openCover I.subscheme I.subschemeCover.openCover

theorem isReduced_iff_radical_eq {X : Scheme.{u}} (I : X.IdealSheafData) :
    IsReduced I.subscheme ↔ I.radical = I :=
  ⟨fun h => @radical_eq_of_isReduced X I h, isReduced_of_radical_eq I⟩

theorem integral_of_prime_top {X : Scheme.{u}} [IsAffine X] (I : X.IdealSheafData)
    [(I.ideal ⟨⊤, isAffineOpen_top X⟩).IsPrime] : IsIntegral I.subscheme := by
  let U : X.affineOpens := ⟨⊤, isAffineOpen_top X⟩
  haveI : (I.ideal U).IsPrime :=
    (inferInstance : (I.ideal ⟨⊤, isAffineOpen_top X⟩).IsPrime)
  haveI : IsDomain (Γ(X, U) ⧸ I.ideal U) := inferInstance
  let f := I.subschemeCover.f U
  haveI : Surjective f := by
    constructor
    intro x
    have hx : x ∈ f.opensRange := by
      change x ∈ (I.subschemeCover.f U).opensRange
      rw [Scheme.IdealSheafData.opensRange_subschemeCover_map]
      trivial
    exact hx
  haveI : IsIso f := (isIso_iff_isOpenImmersion_and_surjective f).mpr
    ⟨inferInstance, inferInstance⟩
  haveI : IsIntegral (Spec (I.subschemeCover.X U)) := by
    change IsIntegral (Spec (CommRingCat.of (Γ(X, U) ⧸ I.ideal U)))
    infer_instance
  exact IsIntegral.of_isIso f

theorem radical_comap_open {X Y : Scheme.{u}} (I : Y.IdealSheafData)
    (f : X ⟶ Y) [IsOpenImmersion f] : (I.comap f).radical = I.radical.comap f := by
  apply Scheme.IdealSheafData.ext
  funext U
  change ((I.comap f).ideal U).radical = (I.radical.comap f).ideal U
  rw [Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion,
    Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion]
  exact (Ideal.comap_radical _ _).symm

theorem eq_of_reduced_support {X : Scheme.{u}} (I J : X.IdealSheafData)
    (hI : I.radical = I) (hJ : J.radical = J) (hs : I.support = J.support) : I = J := by
  rw [← hI, ← Scheme.IdealSheafData.vanishingIdeal_support, hs,
    Scheme.IdealSheafData.vanishingIdeal_support, hJ]

end PhilipponReducedClosedSubscheme

end

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace PhilipponSchemeImageIntegral

/-- The scheme-theoretic image of a reduced source is reduced. -/
theorem ker_radical {X Y : Scheme.{u}} [IsReduced X]
    (f : X ⟶ Y) [QuasiCompact f] : f.ker.radical = f.ker := by
  apply Scheme.IdealSheafData.ext
  funext U
  change (f.ker.ideal U).radical = f.ker.ideal U
  rw [f.ker_apply U]
  change (Ideal.comap (f.app U).hom ⊥).radical = Ideal.comap (f.app U).hom ⊥
  rw [← Ideal.comap_radical,
    Ideal.radical_eq_iff.mpr (Ideal.isRadical_bot : (⊥ : Ideal Γ(X, f ⁻¹ᵁ U)).IsRadical)]

instance image_isReduced {X Y : Scheme.{u}} [IsReduced X]
    (f : X ⟶ Y) [QuasiCompact f] : IsReduced f.image :=
  PhilipponReducedClosedSubscheme.isReduced_of_radical_eq f.ker (ker_radical f)

/-- No immersion hypothesis is needed for integrality of the actual
scheme-theoretic image of a quasi-compact map from an integral scheme. -/
theorem image_isIntegral {X Y : Scheme.{u}} [IsIntegral X]
    (f : X ⟶ Y) [QuasiCompact f] : IsIntegral f.image := by
  have hi : IsIrreducible (Set.range f.toImage) := by
    simpa only [Set.image_univ] using
      (IrreducibleSpace.isIrreducible_univ (X := X)).image
        f.toImage f.toImage.continuous.continuousOn
  letI : IrreducibleSpace f.image := (irreducibleSpace_def _).mpr (by
    change IsIrreducible (Set.univ : Set f.image)
    rw [← f.toImage.denseRange.closure_range]
    exact hi.closure)
  exact isIntegral_of_irreducibleSpace_of_isReduced _

end PhilipponSchemeImageIntegral

end

noncomputable section

set_option autoImplicit false
open AlgebraicGeometry CategoryTheory

theorem PhilipponProperOpenCompactification.isIso
    {Z Y S : Scheme.{u}} (j : Z ⟶ Y) (π : Y ⟶ S)
    [IsOpenImmersion j] [IsDominant j] [IsSeparated π]
    [IsProper (j ≫ π)] : IsIso j := by
  have : IsProper j := IsProper.of_comp j π
  have : Surjective j := inferInstance
  have : Epi j.base := (TopCat.epi_iff_surjective j.base).mpr j.surjective
  exact IsOpenImmersion.isIso j

end

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
attribute [local instance] MvPolynomial.gradedAlgebra

namespace PhilipponAlterationOpenRestriction

lemma finite_restrict_pullback {Z Y X C : Scheme.{u}}
    (a : Z ⟶ X) (c : Z ⟶ Y) (j : X ⟶ C) (f : Y ⟶ C)
    (H : IsPullback a c j f) (W : C.Opens) [IsFinite (f ∣_ W)] :
    IsFinite (a ∣_ (j ⁻¹ᵁ W)) := by
  have H' := Scheme.Hom.isPullback_resLE H (US := W) (UT := f ⁻¹ᵁ W)
    (UX := j ⁻¹ᵁ W) le_rfl le_rfl (UY := a ⁻¹ᵁ (j ⁻¹ᵁ W)) (by
      rw [← Scheme.Hom.comp_preimage, H.w, Scheme.Hom.comp_preimage, inf_idem])
  have hf : IsFinite (f.resLE W (f ⁻¹ᵁ W) le_rfl) := by
    simpa [Scheme.Hom.resLE] using (inferInstance : IsFinite (f ∣_ W))
  have h := MorphismProperty.of_isPullback H'.flip (P := @IsFinite) hf
  simpa [Scheme.Hom.resLE] using h

/-- Restricting one regular projective alteration of an integral proper
compactification gives an alteration with the same regular projective compactification. -/
theorem exists_of_compactification
    (K : Type u) [Field K] {X C : Scheme.{u}} [IsIntegral X] [IsIntegral C]
    (π : X ⟶ Spec (.of K)) (πC : C ⟶ Spec (.of K))
    (j : X ⟶ C) [IsOpenImmersion j] [IsDominant j] (hj : j ≫ πC = π)
    {Y : Scheme.{u}} [IsIntegral Y] (f : Y ⟶ C) [IsProper f] [IsDominant f]
    (hfinite : ∃ W : C.Opens, Nonempty W ∧ IsFinite (f ∣_ W))
    (πY : Y ⟶ Spec (.of K)) [IsProper πY]
    (hf : f ≫ πC = πY) (hreg : ∀ y : Y, IsRegularLocalRing (Y.presheaf.stalk y))
    (m : ℕ) (i : Y ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (m+1)) K))
    [IsClosedImmersion i] (hi : i ≫ ProjSpace.π K m = πY) :
    ∃ (Z : Scheme.{u}) (a : Z ⟶ X),
      IsIntegral Z ∧ IsProper a ∧ IsDominant a ∧
      (∃ V : X.Opens, Nonempty V ∧ IsFinite (a ∣_ V)) ∧
      ∃ (Y : Scheme.{u}) (πY : Y ⟶ Spec (.of K)),
        IsIntegral Y ∧ IsProper πY ∧
        (∀ y : Y, IsRegularLocalRing (Y.presheaf.stalk y)) ∧
        ∃ c : Z ⟶ Y, IsOpenImmersion c ∧ IsDominant c ∧ c ≫ πY = a ≫ π ∧
        ∃ (m : ℕ) (j : Y ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (m+1)) K)),
          IsClosedImmersion j ∧ j ≫ ProjSpace.π K m = πY := by
  let Z := pullback j f
  let a : Z ⟶ X := pullback.fst j f
  let c : Z ⟶ Y := pullback.snd j f
  haveI : Surjective f := inferInstance
  haveI : Surjective a := inferInstanceAs (Surjective (pullback.fst j f))
  haveI : Nonempty Z := by
    obtain ⟨x⟩ := (inferInstance : Nonempty X)
    obtain ⟨z, -⟩ := a.surjective x
    exact ⟨z⟩
  haveI : IsOpenImmersion c := inferInstanceAs (IsOpenImmersion (pullback.snd j f))
  haveI : IsIntegral Z := isIntegral_of_isOpenImmersion c
  haveI : IsDominant c := ⟨c.isOpenEmbedding.isOpenMap.denseRange_of_isPreirreducibleSpace⟩
  have H : IsPullback a c j f := IsPullback.of_hasPullback j f
  obtain ⟨W, hW, hfin⟩ := hfinite
  letI := hfin
  have hV : Nonempty (j ⁻¹ᵁ W) := by
    obtain ⟨x, hx⟩ := j.denseRange.exists_mem_open W.isOpen (by
      obtain ⟨w⟩ := hW
      exact ⟨w.val, w.property⟩)
    exact ⟨⟨x, hx⟩⟩
  refine ⟨Z, a, inferInstance, inferInstance, inferInstance,
    ⟨j ⁻¹ᵁ W, hV, finite_restrict_pullback a c j f H W⟩,
    Y, πY, inferInstance, inferInstance, hreg, c, inferInstance, inferInstance, ?_,
    m, i, inferInstance, hi⟩
  rw [← hf, ← Category.assoc, ← H.w, Category.assoc, hj]

end PhilipponAlterationOpenRestriction

end

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace PhilipponBirationalAlterationComposition

/-- A proper map from an integral scheme with an open section is an
isomorphism over the section's original nonempty open. -/
theorem isIso_restrict_of_open_section {X Y : Scheme.{u}} [IsIntegral Y]
    (p : Y ⟶ X) [IsProper p] (U : X.Opens) [Nonempty U]
    (s : U.toScheme ⟶ Y) [IsOpenImmersion s] (hs : s ≫ p = U.ι) :
    IsIso (p ∣_ U) := by
  let L := p ⁻¹ᵁ U
  have hr : Set.range s ⊆ Set.range L.ι := by
    rintro _ ⟨x, rfl⟩
    refine ⟨⟨s x, ?_⟩, rfl⟩
    change (s ≫ p) x ∈ U
    rw [hs]
    exact x.property
  let t := IsOpenImmersion.lift L.ι s hr
  have ht : t ≫ L.ι = s := IsOpenImmersion.lift_fac ..
  have htp : t ≫ (p ∣_ U) = 𝟙 _ := by
    rw [← cancel_mono U.ι, Category.assoc, morphismRestrict_ι,
      ← Category.assoc, ht, hs, Category.id_comp]
  haveI : IsOpenImmersion (t ≫ L.ι) := ht.symm ▸ inferInstance
  haveI : IsOpenImmersion t := IsOpenImmersion.of_comp t L.ι
  haveI : Nonempty L.toScheme := by
    obtain ⟨x⟩ := (inferInstance : Nonempty U)
    exact ⟨t x⟩
  haveI : IsIntegral L.toScheme := isIntegral_of_isOpenImmersion L.ι
  haveI : IsDominant t :=
    ⟨t.isOpenEmbedding.isOpenMap.denseRange_of_isPreirreducibleSpace⟩
  haveI : IsProper (t ≫ (p ∣_ U)) := htp.symm ▸ inferInstance
  haveI : IsIso t := PhilipponProperOpenCompactification.isIso t (p ∣_ U)
  have h : p ∣_ U = inv t := by
    rw [← cancel_epi t, htp, IsIso.hom_inv_id]
  rw [h]
  infer_instance

/-- Finiteness on a local cartesian model descends to its open image. -/
theorem finite_restrict_image {L Z U X : Scheme.{u}}
    (p : L ⟶ U) (i : L ⟶ Z) (j : U ⟶ X) (q : Z ⟶ X)
    [IsOpenImmersion j] (H : IsPullback p i j q)
    (W : U.Opens) [IsFinite (p ∣_ W)] :
    IsFinite (q ∣_ (W.ι ≫ j).opensRange) := by
  have h := (isPullback_morphismRestrict p W).paste_vert H
  haveI : IsFinite (pullback.snd q (W.ι ≫ j)) :=
    h.flip.isoPullback_inv_snd ▸
      (inferInstance : IsFinite (h.flip.isoPullback.inv ≫ (p ∣_ W)))
  exact ((MorphismProperty.arrow_mk_iso_iff @IsFinite)
    (morphismRestrictOpensRange q (W.ι ≫ j))).mpr inferInstance

/-- A map finite over a nonempty open remains generically finite after
composition with a map that is an isomorphism over a nonempty open. -/
theorem finite_open_comp {Z Y X : Scheme.{u}} [IsIntegral Y]
    (q : Z ⟶ Y) (p : Y ⟶ X)
    (U : X.Opens) [Nonempty U] [IsIso (p ∣_ U)]
    (V : Y.Opens) [Nonempty V] [IsFinite (q ∣_ V)] :
    ∃ W : X.Opens, Nonempty W ∧ IsFinite ((q ≫ p) ∣_ W) := by
  let L := p ⁻¹ᵁ U
  let b : L.toScheme ⟶ X := L.ι ≫ p
  have hb : b = (p ∣_ U) ≫ U.ι := (morphismRestrict_ι p U).symm
  haveI : IsOpenImmersion b := hb.symm ▸ inferInstance
  have hbr : b.opensRange = U := by
    ext x
    change x ∈ Set.range b ↔ x ∈ U
    rw [hb, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
      (p ∣_ U).surjective.range_eq, Set.image_univ, Scheme.Opens.range_ι]
    rfl
  haveI : Nonempty L.toScheme := by
    obtain ⟨x⟩ := (inferInstance : Nonempty U)
    exact ⟨inv (p ∣_ U) x⟩
  let W : L.toScheme.Opens := L.ι ⁻¹ᵁ V
  haveI : Nonempty W := by
    have hL : (L : Set Y).Nonempty := by
      obtain ⟨x⟩ := (inferInstance : Nonempty L.toScheme)
      exact ⟨x.val, x.property⟩
    have hV : (V : Set Y).Nonempty := by
      obtain ⟨x⟩ := (inferInstance : Nonempty V)
      exact ⟨x.val, x.property⟩
    obtain ⟨y, hyL, hyV⟩ :=
      nonempty_preirreducible_inter L.isOpen V.isOpen hL hV
    exact ⟨⟨⟨y, hyL⟩, hyV⟩⟩
  have H : IsPullback (q ∣_ L) (q ⁻¹ᵁ L).ι b (q ≫ p) := by
    apply IsOpenImmersion.isPullback
    · dsimp only [b]
      simpa only [Category.assoc] using
        congrArg (fun f => f ≫ p) (morphismRestrict_ι q L).symm
    · rw [hbr, Scheme.Opens.opensRange_ι, Scheme.Hom.comp_preimage]
  haveI : IsFinite ((q ∣_ L) ∣_ W) :=
    PhilipponAlterationOpenRestriction.finite_restrict_pullback
      (q ∣_ L) (q ⁻¹ᵁ L).ι L.ι q (isPullback_morphismRestrict q L) V
  refine ⟨(W.ι ≫ b).opensRange, ?_,
    finite_restrict_image (q ∣_ L) (q ⁻¹ᵁ L).ι b (q ≫ p) H W⟩
  obtain ⟨w⟩ := (inferInstance : Nonempty W)
  exact ⟨⟨(W.ι ≫ b) w, ⟨w, rfl⟩⟩⟩

end PhilipponBirationalAlterationComposition

end

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open P2MW.S_AlgebraicGeometry_exists_isProper_surjective_isOpenImmersion_comp_eq_of_isIntegral.SolCHint
open scoped P2MW.S_AlgebraicGeometry_exists_isProper_surjective_isOpenImmersion_comp_eq_of_isIntegral.SolCHint.ChartData

/-- The stronger data retained by the accepted Chow-envelope construction:
an integral proper birational modification with an integral proper
compactification. All maps are over the original arbitrary field. -/
theorem PhilipponChowBirationalCompactification.exists_model
    (K : Type u) [Field K] {X : Scheme.{u}} [IsIntegral X]
    (π : X ⟶ Spec (.of K))
    [LocallyOfFiniteType π] [QuasiCompact π] [IsSeparated π] :
    ∃ (X' C : Scheme.{u}) (p : X' ⟶ X) (j : X' ⟶ C)
      (πC : C ⟶ Spec (.of K)),
      IsIntegral X' ∧ IsIntegral C ∧ IsProper p ∧ IsDominant p ∧
      IsOpenImmersion j ∧ IsDominant j ∧ IsProper πC ∧
      j ≫ πC = p ≫ π ∧
      ∃ U : X.Opens, Nonempty U ∧ IsIso (p ∣_ U) := by
  haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace π
  obtain ⟨D⟩ := nonempty_chartData π
  haveI : IsIntegral D.ιι.image := PhilipponSchemeImageIntegral.image_isIntegral D.ιι
  haveI : IsDominant D.π := inferInstance
  haveI : IsIso (D.π ∣_ D.Uo) :=
    PhilipponBirationalAlterationComposition.isIso_restrict_of_open_section
      D.π D.Uo D.ψ' D.ψ'_π
  refine ⟨D.X', D.ιι.image, D.π, D.ιι.toImage, D.ιι.imageι ≫ D.prπ,
    inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, ?_, D.Uo, inferInstance, inferInstance⟩
  rw [← Category.assoc, Scheme.Hom.toImage_imageι, D.π_comp_f]

end

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
attribute [local instance] MvPolynomial.gradedAlgebra

theorem solution
    (K : Type u) [Field K] {X : Scheme.{u}} [IsIntegral X]
    (π : X ⟶ Spec (.of K))
    [LocallyOfFiniteType π] [QuasiCompact π] [IsSeparated π] :
    ∃ (Z : Scheme.{u}) (a : Z ⟶ X),
      IsIntegral Z ∧ IsProper a ∧ IsDominant a ∧
      (∃ V : X.Opens, Nonempty V ∧ IsFinite (a ∣_ V)) ∧
      ∃ (Y : Scheme.{u}) (πY : Y ⟶ Spec (.of K)),
        IsIntegral Y ∧ IsProper πY ∧
        (∀ y : Y, IsRegularLocalRing (Y.presheaf.stalk y)) ∧
        ∃ c : Z ⟶ Y, IsOpenImmersion c ∧ IsDominant c ∧ c ≫ πY = a ≫ π ∧
        ∃ (m : ℕ) (j : Y ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (m + 1)) K)),
          IsClosedImmersion j ∧ j ≫ ProjSpace.π K m = πY := by
  obtain ⟨X', C, p, j, πC, hX', hC, hproperp, hdomp, hopenj, hdomj,
    hproperC, hjbase, U, hU, hUiso⟩ :=
    PhilipponChowBirationalCompactification.exists_model K π
  letI := hX'
  letI := hC
  letI := hproperp
  letI := hdomp
  letI := hopenj
  letI := hdomj
  letI := hproperC
  letI := hU
  letI := hUiso
  obtain ⟨Y, f, hY, hproperf, hsurjf, hregular, hfinite, m, i, hi, hibase⟩ :=
    AlgebraicGeometry.exists_regular_projective_alteration_of_isProper K πC
  letI := hY
  letI := hproperf
  letI := hsurjf
  letI := hi
  obtain ⟨Z, q, hZ, hproperq, hdomq, ⟨V, hV, hVfin⟩,
    Y', πY', hY', hproperY', hreg', c, hcopen, hcdom, hcbase, m', i', hi', hibase'⟩ :=
    PhilipponAlterationOpenRestriction.exists_of_compactification K (p ≫ π) πC j hjbase
      f hfinite (f ≫ πC) rfl hregular m i hibase
  letI := hZ
  letI := hproperq
  letI := hdomq
  letI := hV
  letI := hVfin
  refine ⟨Z, q ≫ p, hZ, inferInstance, inferInstance,
    PhilipponBirationalAlterationComposition.finite_open_comp q p U V,
    Y', πY', hY', hproperY', hreg', c, hcopen, hcdom, ?_, m', i', hi', hibase'⟩
  simpa only [Category.assoc] using hcbase

end

#print axioms PhilipponReducedClosedSubscheme.isReduced_iff_radical_eq
#print axioms PhilipponReducedClosedSubscheme.integral_of_prime_top
#print axioms PhilipponReducedClosedSubscheme.radical_comap_open
#print axioms PhilipponReducedClosedSubscheme.eq_of_reduced_support
#print axioms PhilipponSchemeImageIntegral.ker_radical
#print axioms PhilipponSchemeImageIntegral.image_isReduced
#print axioms PhilipponSchemeImageIntegral.image_isIntegral
#print axioms PhilipponProperOpenCompactification.isIso
#print axioms PhilipponAlterationOpenRestriction.finite_restrict_pullback
#print axioms PhilipponAlterationOpenRestriction.exists_of_compactification
#print axioms PhilipponBirationalAlterationComposition.isIso_restrict_of_open_section
#print axioms PhilipponBirationalAlterationComposition.finite_restrict_image
#print axioms PhilipponBirationalAlterationComposition.finite_open_comp
#print axioms PhilipponChowBirationalCompactification.exists_model
#print axioms solution
