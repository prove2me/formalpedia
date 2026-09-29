-- Prove2me | solution 1 for AlgebraicGeometry.OModulePresheaf.exists_coequifibered_addEquiv_of_affHom_pushforwardUnit_of_isAdicComplete_of_isProper
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/8a665ed0-cffd-5167-a0e2-0efe62aa84b5

import Mathlib
import Definitions.Def_AlgebraicGeometry_OModulePresheafConstructions
import Definitions.Def_AlgebraicGeometry_OModulePresheafTensor
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_existsUnique_affHom_comp_eq_of_isAdicComplete_of_isProper
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_isCoherent_pushforwardUnit_and_exists_affHom_of_forall_isFinite_isPullback
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_isQuasicoherent_isCoherent_supportedIn_tensor
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_coequifibered_addEquiv_of_affHom_pushforwardUnit_of_isAdicComplete_of_isProper
p2m_attr_erase "instance" "AlgebraicGeometry.OModulePresheaf.moduleSectionsHomSub AlgebraicGeometry.OModulePresheaf.smulSections AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul AlgebraicGeometry.OModulePresheaf.Leray.biC_module AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I AlgebraicGeometry.ChowDatum.hι_closed AlgebraicGeometry.ChowDatumProj.hιN_closed AlgebraicGeometry.ChowDatumProj.hp_proper AlgebraicGeometry.ChowDatum.hp_isoU AlgebraicGeometry.ChowDatum.hp_proper AlgebraicGeometry.ProjSpace.algebraAway AlgebraicGeometry.ProjSpace.instIsProperProdOverπ AlgebraicGeometry.ChowDatumProj.hp_isoU AlgebraicGeometry.ProjSpace.isProper_π AlgebraicGeometry.ProjSpace.finiteType_mvPolynomial ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup"
p2m_attr_erase "instance" "ProjSpaceCech.GradedModule.sec.instZero ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule"
p2m_attr_erase "simp" "AlgebraicGeometry.OModulePresheaf.internalHom.ofAffHom_apply AlgebraicGeometry.OModulePresheaf.internalHom.toAffHom_app AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq AlgebraicGeometry.ChowDatumProj.mk.sizeOf_spec AlgebraicGeometry.ChowDatum.mk.sizeOf_spec AlgebraicGeometry.ChowDatumProj.mk.injEq AlgebraicGeometry.ChowDatum.mk.injEq ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.mk.injEq"

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry TensorProduct

noncomputable section

namespace AlgStructAux

open AlgebraicGeometry.OModulePresheaf

variable {R : Type u} [CommRing R] {X : Scheme.{u}} {f : X ⟶ Spec (.of R)}

abbrev A (U : X.affineOpens) : Type u := X.presheaf.obj (op U.1)

section MkAffHom

variable {M N : OModulePresheaf f}

def linR (U : X.affineOpens) (g : M.obj U.1 →ₗ[A U] N.obj U.1) : M.obj U.1 →ₗ[R] N.obj U.1 where
  toFun := g
  map_add' := g.map_add
  map_smul' r x := by
    letI := Scheme.TwoAffineOpenCover.algebraOfHom f U.1
    haveI := M.isScalarTower U.1
    haveI := N.isScalarTower U.1
    change g (r • x) = r • g x
    rw [← algebraMap_smul (A := A U) r x, g.map_smul, algebraMap_smul]

@[scoped simp] theorem linR_apply (U : X.affineOpens) (g : M.obj U.1 →ₗ[A U] N.obj U.1) (x : M.obj U.1) :
    linR U g x = g x := rfl

def mkAffHom (app : ∀ U : X.affineOpens, M.obj U.1 →ₗ[A U] N.obj U.1)
    (nat : ∀ (U U' : X.affineOpens) (h : U.1 ≤ U'.1) (x : M.obj U'.1), app U (M.res h x) = N.res h (app U' x)) :
    AffHom M N where
  app U := linR U (app U)
  app_smul U a x := (app U).map_smul a x
  naturality h := LinearMap.ext fun x => nat _ _ h x

@[scoped simp] theorem mkAffHom_app (app : ∀ U : X.affineOpens, M.obj U.1 →ₗ[A U] N.obj U.1) (nat) (U : X.affineOpens)
    (x : M.obj U.1) : (mkAffHom app nat).app U x = app U x := rfl

theorem affHom_ext (a b : AffHom M N) (h : ∀ (W : X.affineOpens) (x : M.obj W.1), a.app W x = b.app W x) : a = b := by
  obtain ⟨a1, a2, a3⟩ := a
  obtain ⟨b1, b2, b3⟩ := b
  have : a1 = b1 := funext fun W => LinearMap.ext (h W)
  subst this
  rfl

end MkAffHom

theorem unit_isCoherent : (unit f).IsCoherent := fun U => Module.Finite.self (A U)

theorem unit_isQuasicoherent : (unit f).IsQuasicoherent := by
  intro U r
  haveI := U.2.isLocalization_basicOpen r
  refine ⟨fun x => ?_, fun y hy => ?_⟩
  · obtain ⟨⟨y, s⟩, hs⟩ := IsLocalization.surj (Submonoid.powers r) (show Γ(X, X.basicOpen r) from x)
    obtain ⟨n, hn⟩ := s.2
    refine ⟨n, y, ?_⟩
    change (X.presheaf.map (homOfLE (X.basicOpen_le r)).op).hom y =
      (X.presheaf.map (homOfLE (X.basicOpen_le r)).op).hom (r ^ n) * (show Γ(X, X.basicOpen r) from x)
    have e : algebraMap Γ(X, U.1) Γ(X, X.basicOpen r) = (X.presheaf.map (homOfLE (X.basicOpen_le r)).op).hom := rfl
    have hn' : r ^ n = s.1 := hn
    rw [← e, hn', mul_comm]
    exact hs.symm
  · have hy' : algebraMap Γ(X, U.1) Γ(X, X.basicOpen r) (show Γ(X, U.1) from y) = 0 := hy
    obtain ⟨⟨m, k, hk⟩, hm⟩ := (IsLocalization.map_eq_zero_iff (Submonoid.powers r) Γ(X, X.basicOpen r) _).mp hy'
    refine ⟨k, ?_⟩
    have hk' : r ^ k = m := hk
    change r ^ k * (show Γ(X, U.1) from y) = 0
    rw [hk']
    exact hm

structure ASys {R : Type u} [CommRing R] (I : Ideal R) {X : Scheme.{u}} (f : X ⟶ Spec (.of R)) where
  sR : ∀ n : ℕ, Spec (CommRingCat.of (R ⧸ I ^ (n + 1))) ⟶ Spec (CommRingCat.of R)
  hsR : ∀ n : ℕ, sR n = Spec.map (CommRingCat.ofHom (algebraMap R (R ⧸ I ^ (n + 1))))
  tR : ∀ n : ℕ, Spec (CommRingCat.of (R ⧸ I ^ (n + 1))) ⟶ Spec (CommRingCat.of (R ⧸ I ^ (n + 1 + 1)))
  htR : ∀ n : ℕ, tR n ≫ sR (n + 1) = sR n
  xn : ∀ n : ℕ, Limits.pullback f (sR n) ⟶ Limits.pullback f (sR (n + 1))
  hxn₁ : ∀ n : ℕ, xn n ≫ Limits.pullback.fst f (sR (n + 1)) = Limits.pullback.fst f (sR n)
  hxn₂ : ∀ n : ℕ, xn n ≫ Limits.pullback.snd f (sR (n + 1)) = Limits.pullback.snd f (sR n) ≫ tR n
  Y : ℕ → Scheme.{u}
  g : ∀ n : ℕ, Y n ⟶ Limits.pullback f (sR n)
  hg : ∀ n : ℕ, IsFinite (g n)
  yn : ∀ n : ℕ, Y n ⟶ Y (n + 1)
  hY : ∀ n : ℕ, IsPullback (yn n) (g n) (g (n + 1)) (xn n)
  F : OModulePresheaf f
  hFc : F.IsCoherent
  hFq : F.IsQuasicoherent
  ρ : ∀ n : ℕ, AffHom F (pushforwardUnit f (g n ≫ pullback.fst f (sR n)))
  hρs : ∀ (n : ℕ) (U : X.affineOpens), Function.Surjective ((ρ n).app U)
  hρk : ∀ (n : ℕ) (U : X.affineOpens), LinearMap.ker ((ρ n).app U) = I ^ (n + 1) • (⊤ : Submodule R (F.obj U.1))
  hρc : ∀ (n : ℕ) (U : X.affineOpens) (x : F.obj U.1),
    (ρ n).app U x =
      ((yn n).appLE ((g (n + 1) ≫ pullback.fst f (sR (n + 1))) ⁻¹ᵁ U.1) ((g n ≫ pullback.fst f (sR n)) ⁻¹ᵁ U.1)
        (by rw [← Scheme.Hom.comp_preimage, ← Category.assoc, (hY n).w, Category.assoc, hxn₁])).hom
        ((ρ (n + 1)).app U x)

variable [IsNoetherianRing R] {I : Ideal R} [IsAdicComplete I R] [IsProper f] (S : ASys I f)

namespace ASys

abbrev h (n : ℕ) : S.Y n ⟶ X := S.g n ≫ pullback.fst f (S.sR n)

abbrev B (n : ℕ) : OModulePresheaf f := pushforwardUnit f (S.h n)

abbrev BΓ (n : ℕ) (U : X.Opens) : Type u := (S.Y n).presheaf.obj (op ((S.h n) ⁻¹ᵁ U))

abbrev bapp (n : ℕ) (U : X.Opens) : Γ(X, U) →+* S.BΓ n U := ((S.h n).appLE U ((S.h n) ⁻¹ᵁ U) le_rfl).hom

theorem yn_comp_h (n : ℕ) : S.yn n ≫ S.h (n + 1) = S.h n := by
  change S.yn n ≫ S.g (n + 1) ≫ pullback.fst f (S.sR (n + 1)) = S.g n ≫ pullback.fst f (S.sR n)
  rw [← Category.assoc, (S.hY n).w, Category.assoc, S.hxn₁]

theorem pre_le (n : ℕ) (U : X.Opens) : (S.h n) ⁻¹ᵁ U ≤ (S.yn n) ⁻¹ᵁ ((S.h (n + 1)) ⁻¹ᵁ U) := by
  rw [← Scheme.Hom.comp_preimage, S.yn_comp_h]

abbrev ynapp (n : ℕ) (U : X.Opens) : S.BΓ (n + 1) U →+* S.BΓ n U :=
  ((S.yn n).appLE ((S.h (n + 1)) ⁻¹ᵁ U) ((S.h n) ⁻¹ᵁ U) (S.pre_le n U)).hom

abbrev ρB (n : ℕ) (U : X.affineOpens) (x : S.F.obj U.1) : S.BΓ n U.1 := (S.ρ n).app U x

theorem hρc' (n : ℕ) (U : X.affineOpens) (x : S.F.obj U.1) : S.ρB n U x = S.ynapp n U.1 (S.ρB (n + 1) U x) :=
  S.hρc n U x

scoped instance isFinite_g (n : ℕ) : IsFinite (S.g n) := S.hg n

theorem B_smul (n : ℕ) (U : X.Opens) (a : Γ(X, U)) (z : (S.B n).obj U) :
    (a • z : (S.B n).obj U) = (show (S.B n).obj U from S.bapp n U a * (show S.BΓ n U from z)) := rfl

theorem B_res (n : ℕ) {U U' : X.Opens} (hU : U ≤ U') (z : (S.B n).obj U') :
    ((S.B n).res hU z : S.BΓ n U) =
      ((S.Y n).presheaf.map (homOfLE ((Opens.map (S.h n).base).monotone hU)).op).hom (show S.BΓ n U' from z) := rfl

theorem ρ_add (n : ℕ) (U : X.affineOpens) (x y : S.F.obj U.1) : S.ρB n U (x + y) = S.ρB n U x + S.ρB n U y :=
  map_add ((S.ρ n).app U) x y

theorem ρ_zero (n : ℕ) (U : X.affineOpens) : S.ρB n U 0 = 0 := map_zero ((S.ρ n).app U)

theorem ρ_sub (n : ℕ) (U : X.affineOpens) (x y : S.F.obj U.1) : S.ρB n U (x - y) = S.ρB n U x - S.ρB n U y :=
  map_sub ((S.ρ n).app U) x y

theorem ρ_smul (n : ℕ) (U : X.affineOpens) (a : A U) (x : S.F.obj U.1) :
    S.ρB n U (a • x) = S.bapp n U.1 a * S.ρB n U x := by
  change (S.ρ n).app U (a • x) = _
  rw [(S.ρ n).app_smul]
  rfl

theorem ρ_res (n : ℕ) (U U' : X.affineOpens) (hU : U.1 ≤ U'.1) (x : S.F.obj U'.1) :
    S.ρB n U (S.F.res hU x) =
      ((S.Y n).presheaf.map (homOfLE ((Opens.map (S.h n).base).monotone hU)).op).hom (S.ρB n U' x) := by
  change (S.ρ n).app U (S.F.res hU x) = _
  rw [(S.ρ n).naturality_apply (U := U) (U' := U') hU x]
  rfl

theorem B_coh_qc (n : ℕ) : (S.B n).IsCoherent ∧ (S.B n).IsQuasicoherent :=
  (AlgebraicGeometry.OModulePresheaf.isCoherent_pushforwardUnit_and_exists_affHom_of_forall_isFinite_isPullback
    R I X f S.sR S.hsR S.tR S.htR S.xn S.hxn₁ S.hxn₂ S.Y S.g S.yn S.hY).1 n

theorem B_coh (n : ℕ) : (S.B n).IsCoherent := (S.B_coh_qc n).1
theorem B_qc (n : ℕ) : (S.B n).IsQuasicoherent := (S.B_coh_qc n).2

theorem exists_τ : ∃ τ : ∀ n : ℕ, AffHom (S.B (n + 1)) (S.B n),
    ∀ (n : ℕ) (U : X.affineOpens) (z : (S.B (n + 1)).obj U.1),
      (τ n).app U z = (show (S.B n).obj U.1 from S.ynapp n U.1 (show S.BΓ (n + 1) U.1 from z)) := by
  obtain ⟨τ, hτ, -, -⟩ :=
    (AlgebraicGeometry.OModulePresheaf.isCoherent_pushforwardUnit_and_exists_affHom_of_forall_isFinite_isPullback
      R I X f S.sR S.hsR S.tR S.htR S.xn S.hxn₁ S.hxn₂ S.Y S.g S.yn S.hY).2.2
  exact ⟨τ, hτ⟩

def τ : ∀ n : ℕ, AffHom (S.B (n + 1)) (S.B n) := S.exists_τ.choose

theorem τ_app (n : ℕ) (U : X.affineOpens) (z : (S.B (n + 1)).obj U.1) :
    ((S.τ n).app U z : S.BΓ n U.1) = S.ynapp n U.1 (show S.BΓ (n + 1) U.1 from z) :=
  S.exists_τ.choose_spec n U z

theorem hτρ (n : ℕ) : (S.τ n).comp (S.ρ (n + 1)) = S.ρ n :=
  affHom_ext _ _ fun U x => by
    rw [AffHom.comp_app]
    exact (S.τ_app n U _).trans (S.hρc' n U x).symm

theorem k42 (M : OModulePresheaf f) (hMc : M.IsCoherent) (hMq : M.IsQuasicoherent)
    (ψ : ∀ n : ℕ, AffHom M (S.B n)) (hψ : ∀ n : ℕ, (S.τ n).comp (ψ (n + 1)) = ψ n) :
    ∃ φ : AffHom M S.F, (∀ n : ℕ, (S.ρ n).comp φ = ψ n) ∧
      ∀ φ' : AffHom M S.F, (∀ n : ℕ, (S.ρ n).comp φ' = ψ n) → φ' = φ :=
  AlgebraicGeometry.OModulePresheaf.existsUnique_affHom_comp_eq_of_isAdicComplete_of_isProper I f M S.F hMc hMq
    S.hFc S.hFq S.B S.τ S.ρ S.hρs S.hρk S.hτρ ψ hψ

theorem k42_unique (M : OModulePresheaf f) (hMc : M.IsCoherent) (hMq : M.IsQuasicoherent) (φ₀ φ' : AffHom M S.F)
    (h : ∀ n : ℕ, (S.ρ n).comp φ' = (S.ρ n).comp φ₀) : φ' = φ₀ := by
  obtain ⟨φ, hφ, huniq⟩ := S.k42 M hMc hMq (fun n => (S.ρ n).comp φ₀) fun n => by
    show (S.τ n).comp ((S.ρ (n + 1)).comp φ₀) = (S.ρ n).comp φ₀
    rw [← S.hτρ n]; rfl
  rw [huniq φ' h, huniq φ₀ fun n => rfl]

def u (n : ℕ) : AffHom (unit f) (S.B n) :=
  mkAffHom
    (fun U =>
      { toFun := fun a => show (S.B n).obj U.1 from S.bapp n U.1 (show A U from a)
        map_add' := fun a b => map_add _ _ _
        map_smul' := fun a b => by
          change S.bapp n U.1 (a * (show A U from b)) = a • (show (S.B n).obj U.1 from S.bapp n U.1 (show A U from b))
          rw [B_smul, map_mul] })
    (fun U U' hU a => by
      change S.bapp n U.1 ((X.presheaf.map (homOfLE hU).op).hom a) =
        (S.B n).res hU (show (S.B n).obj U'.1 from S.bapp n U'.1 a)
      rw [B_res, ← CommRingCat.comp_apply, ← CommRingCat.comp_apply, Scheme.Hom.map_appLE, Scheme.Hom.appLE_map])

theorem u_app (n : ℕ) (U : X.affineOpens) (a : A U) :
    ((S.u n).app U (show (unit f).obj U.1 from a) : S.BΓ n U.1) = S.bapp n U.1 a := rfl

theorem ynapp_bapp (n : ℕ) (U : X.Opens) (a : Γ(X, U)) : S.ynapp n U (S.bapp (n + 1) U a) = S.bapp n U a := by
  change ((S.h (n + 1)).appLE U _ le_rfl ≫ (S.yn n).appLE _ _ (S.pre_le n U)).hom a = _
  rw [Scheme.Hom.appLE_comp_appLE]

  have key : ∀ (k : S.Y n ⟶ X) (hk : k = S.h n) (e : (S.h n) ⁻¹ᵁ U ≤ k ⁻¹ᵁ U),
      (k.appLE U ((S.h n) ⁻¹ᵁ U) e).hom a = S.bapp n U a := by
    rintro k rfl e; rfl
  exact key _ (S.yn_comp_h n) _

theorem hτu (n : ℕ) : (S.τ n).comp (S.u (n + 1)) = S.u n :=
  affHom_ext _ _ fun U a => by
    rw [AffHom.comp_app]
    exact (S.τ_app n U _).trans (S.ynapp_bapp n U.1 a)

theorem exists_eta : ∃ η : AffHom (unit f) S.F, (∀ n : ℕ, (S.ρ n).comp η = S.u n) ∧
    ∀ η' : AffHom (unit f) S.F, (∀ n : ℕ, (S.ρ n).comp η' = S.u n) → η' = η :=
  S.k42 (unit f) unit_isCoherent unit_isQuasicoherent S.u S.hτu

def η : AffHom (unit f) S.F := S.exists_eta.choose

theorem ρ_η (n : ℕ) (U : X.affineOpens) (a : A U) :
    S.ρB n U (S.η.app U (show (unit f).obj U.1 from a)) = S.bapp n U.1 a := by
  have := congrArg (fun θ : AffHom (unit f) (S.B n) => (θ.app U (show (unit f).obj U.1 from a) : S.BΓ n U.1))
    (S.exists_eta.choose_spec.1 n)
  exact this

def one (U : X.affineOpens) : S.F.obj U.1 := S.η.app U (show (unit f).obj U.1 from (1 : A U))

theorem η_eq_smul_one (U : X.affineOpens) (a : A U) : S.η.app U (show (unit f).obj U.1 from a) = a • S.one U := by
  rw [one, ← (S.η).app_smul]
  exact congrArg _ (mul_one a).symm

theorem ρ_one (n : ℕ) (U : X.affineOpens) : S.ρB n U (S.one U) = 1 := by
  rw [one, ρ_η, map_one]

theorem res_one (U U' : X.affineOpens) (hU : U.1 ≤ U'.1) : S.F.res hU (S.one U') = S.one U := by
  rw [one, one, ← (S.η).naturality_apply (U := U) (U' := U') hU]
  exact congrArg _ (map_one (X.presheaf.map (homOfLE hU).op).hom)

abbrev T2 (U : X.affineOpens) : Type u := S.F.obj U.1 ⊗[A U] S.F.obj U.1

abbrev T3 (U : X.affineOpens) : Type u := S.T2 U ⊗[A U] S.F.obj U.1

abbrev F2 : OModulePresheaf f := S.F.tensor S.F

abbrev F3 : OModulePresheaf f := S.F2.tensor S.F

section Wrappers

variable {N : OModulePresheaf f}

def appT2 (θ : AffHom S.F2 N) (U : X.affineOpens) : S.T2 U →ₗ[A U] N.obj U.1 where
  toFun t := θ.app U t
  map_add' s t := (θ.app U).map_add s t
  map_smul' a t := θ.app_smul U a t

def appT3 (θ : AffHom S.F3 N) (U : X.affineOpens) : S.T3 U →ₗ[A U] N.obj U.1 where
  toFun t := θ.app U t
  map_add' s t := (θ.app U).map_add s t
  map_smul' a t := θ.app_smul U a t

theorem appT2_apply (θ : AffHom S.F2 N) (U : X.affineOpens) (t : S.T2 U) : S.appT2 θ U t = θ.app U t := rfl
theorem appT3_apply (θ : AffHom S.F3 N) (U : X.affineOpens) (t : S.T3 U) : S.appT3 θ U t = θ.app U t := rfl

def resT2 {U U' : X.affineOpens} (hU : U.1 ≤ U'.1) : S.T2 U' →+ S.T2 U where
  toFun t := S.F2.res hU t
  map_zero' := (S.F2.res hU).map_zero
  map_add' s t := (S.F2.res hU).map_add s t

def resT3 {U U' : X.affineOpens} (hU : U.1 ≤ U'.1) : S.T3 U' →+ S.T3 U where
  toFun t := S.F3.res hU t
  map_zero' := (S.F3.res hU).map_zero
  map_add' s t := (S.F3.res hU).map_add s t

theorem resT2_tmul {U U' : X.affineOpens} (hU : U.1 ≤ U'.1) (x y : S.F.obj U'.1) :
    S.resT2 hU (x ⊗ₜ y) = S.F.res hU x ⊗ₜ S.F.res hU y := rfl

theorem resT3_tmul {U U' : X.affineOpens} (hU : U.1 ≤ U'.1) (s : S.T2 U') (z : S.F.obj U'.1) :
    S.resT3 hU (s ⊗ₜ z) = S.resT2 hU s ⊗ₜ S.F.res hU z := rfl

def mkAffHom2 (g : ∀ U : X.affineOpens, S.T2 U →ₗ[A U] N.obj U.1)
    (nat : ∀ (U U' : X.affineOpens) (hU : U.1 ≤ U'.1) (x y : S.F.obj U'.1),
      g U (S.F.res hU x ⊗ₜ S.F.res hU y) = N.res hU (g U' (x ⊗ₜ y))) : AffHom S.F2 N :=
  mkAffHom (M := S.F2) (fun U => g U) fun U U' hU => fun (t : S.T2 U') =>
    show g U (S.resT2 hU t) = N.res hU (g U' t) by
      induction t using TensorProduct.induction_on with
      | zero => simp only [map_zero]
      | tmul x y => rw [resT2_tmul]; exact nat U U' hU x y
      | add s t hs ht => rw [map_add, map_add, hs, ht, map_add, map_add]

theorem mkAffHom2_app (g : ∀ U : X.affineOpens, S.T2 U →ₗ[A U] N.obj U.1) (nat) (U : X.affineOpens) (t : S.T2 U) :
    (S.mkAffHom2 g nat).app U t = g U t := rfl

def mkAffHom3 (g : ∀ U : X.affineOpens, S.T3 U →ₗ[A U] N.obj U.1)
    (nat : ∀ (U U' : X.affineOpens) (hU : U.1 ≤ U'.1) (x y z : S.F.obj U'.1),
      g U ((S.F.res hU x ⊗ₜ S.F.res hU y) ⊗ₜ S.F.res hU z) = N.res hU (g U' ((x ⊗ₜ y) ⊗ₜ z))) : AffHom S.F3 N :=
  mkAffHom (M := S.F3) (fun U => g U) fun U U' hU => fun (t : S.T3 U') =>
    show g U (S.resT3 hU t) = N.res hU (g U' t) by
      induction t using TensorProduct.induction_on with
      | zero => simp only [map_zero]
      | tmul s z =>
        rw [resT3_tmul]
        induction s using TensorProduct.induction_on with
        | zero => simp only [map_zero, zero_tmul]
        | tmul x y => rw [resT2_tmul]; exact nat U U' hU x y z
        | add s s' hs hs' => rw [map_add, add_tmul, map_add, hs, hs', add_tmul, map_add, map_add]
      | add s t hs ht => rw [map_add, map_add, hs, ht, map_add, map_add]

theorem mkAffHom3_app (g : ∀ U : X.affineOpens, S.T3 U →ₗ[A U] N.obj U.1) (nat) (U : X.affineOpens) (t : S.T3 U) :
    (S.mkAffHom3 g nat).app U t = g U t := rfl

theorem affHom2_ext (a b : AffHom S.F2 N) (h : ∀ (U : X.affineOpens) (x y : S.F.obj U.1), a.app U (x ⊗ₜ y) = b.app U (x ⊗ₜ y)) :
    a = b :=
  affHom_ext _ _ fun U => fun (t : S.T2 U) => show S.appT2 a U t = S.appT2 b U t by
    induction t using TensorProduct.induction_on with
    | zero => rw [map_zero, map_zero]
    | tmul x y => exact h U x y
    | add s t hs ht => rw [map_add, map_add, hs, ht]

theorem affHom3_ext (a b : AffHom S.F3 N)
    (h : ∀ (U : X.affineOpens) (x y z : S.F.obj U.1), a.app U ((x ⊗ₜ y) ⊗ₜ z) = b.app U ((x ⊗ₜ y) ⊗ₜ z)) : a = b :=
  affHom_ext _ _ fun U => fun (t : S.T3 U) => show S.appT3 a U t = S.appT3 b U t by
    induction t using TensorProduct.induction_on with
    | zero => rw [map_zero, map_zero]
    | tmul s z =>
      induction s using TensorProduct.induction_on with
      | zero => rw [zero_tmul, map_zero, map_zero]
      | tmul x y => exact h U x y z
      | add s s' hs hs' => rw [add_tmul, map_add, map_add, hs, hs']
    | add s t hs ht => rw [map_add, map_add, hs, ht]

end Wrappers

def μlin (n : ℕ) (U : X.affineOpens) : S.T2 U →ₗ[A U] (S.B n).obj U.1 :=
  TensorProduct.lift
    (LinearMap.mk₂ (A U) (fun x y => show (S.B n).obj U.1 from S.ρB n U x * S.ρB n U y)
      (fun x x' y => by
        change S.ρB n U (x + x') * S.ρB n U y = S.ρB n U x * S.ρB n U y + S.ρB n U x' * S.ρB n U y
        rw [ρ_add, add_mul])
      (fun a x y => by
        change S.ρB n U (a • x) * S.ρB n U y = a • (show (S.B n).obj U.1 from S.ρB n U x * S.ρB n U y)
        rw [B_smul, ρ_smul, mul_assoc])
      (fun x y y' => by
        change S.ρB n U x * S.ρB n U (y + y') = S.ρB n U x * S.ρB n U y + S.ρB n U x * S.ρB n U y'
        rw [ρ_add, mul_add])
      (fun a x y => by
        change S.ρB n U x * S.ρB n U (a • y) = a • (show (S.B n).obj U.1 from S.ρB n U x * S.ρB n U y)
        rw [B_smul, ρ_smul, mul_left_comm]))

theorem μlin_tmul (n : ℕ) (U : X.affineOpens) (x y : S.F.obj U.1) :
    (S.μlin n U (x ⊗ₜ y) : S.BΓ n U.1) = S.ρB n U x * S.ρB n U y := rfl

theorem B_inj (n : ℕ) (U : X.affineOpens) : Function.Injective (fun z : (S.B n).obj U.1 => (z : S.BΓ n U.1)) :=
  fun _ _ h => h

def μ (n : ℕ) : AffHom S.F2 (S.B n) :=
  S.mkAffHom2 (S.μlin n) fun U U' hU x y => by
    apply S.B_inj n U
    change S.ρB n U (S.F.res hU x) * S.ρB n U (S.F.res hU y) = ((S.B n).res hU (S.μlin n U' (x ⊗ₜ y)) : S.BΓ n U.1)
    rw [B_res, μlin_tmul, map_mul, ρ_res, ρ_res]

theorem μ_tmul (n : ℕ) (U : X.affineOpens) (x y : S.F.obj U.1) :
    ((S.μ n).app U (x ⊗ₜ y) : S.BΓ n U.1) = S.ρB n U x * S.ρB n U y := rfl

theorem hτμ (n : ℕ) : (S.τ n).comp (S.μ (n + 1)) = S.μ n :=
  S.affHom2_ext _ _ fun U x y => by
    rw [AffHom.comp_app]
    apply S.B_inj n U
    change ((S.τ n).app U ((S.μ (n + 1)).app U (x ⊗ₜ y)) : S.BΓ n U.1) = S.ρB n U x * S.ρB n U y
    rw [τ_app]
    change S.ynapp n U.1 (S.ρB (n + 1) U x * S.ρB (n + 1) U y) = S.ρB n U x * S.ρB n U y
    rw [map_mul, ← hρc', ← hρc']

theorem exists_m : ∃ m : AffHom S.F2 S.F, (∀ n : ℕ, (S.ρ n).comp m = S.μ n) ∧
    ∀ m' : AffHom S.F2 S.F, (∀ n : ℕ, (S.ρ n).comp m' = S.μ n) → m' = m :=
  S.k42 S.F2
    ((AlgebraicGeometry.OModulePresheaf.isQuasicoherent_isCoherent_supportedIn_tensor S.F S.F).2.1 S.hFc S.hFc)
    ((AlgebraicGeometry.OModulePresheaf.isQuasicoherent_isCoherent_supportedIn_tensor S.F S.F).1 S.hFq S.hFq)
    S.μ S.hτμ

def m : AffHom S.F2 S.F := S.exists_m.choose

theorem ρ_comp_m (n : ℕ) : (S.ρ n).comp S.m = S.μ n := S.exists_m.choose_spec.1 n

theorem m_unique (m' : AffHom S.F2 S.F) (h : ∀ n : ℕ, (S.ρ n).comp m' = S.μ n) : m' = S.m :=
  S.exists_m.choose_spec.2 m' h

def mul (U : X.affineOpens) (x y : S.F.obj U.1) : S.F.obj U.1 := S.appT2 S.m U (x ⊗ₜ y)

theorem mul_def (U : X.affineOpens) (x y : S.F.obj U.1) : S.mul U x y = S.m.app U (x ⊗ₜ y) := rfl

theorem ρ_mul (n : ℕ) (U : X.affineOpens) (x y : S.F.obj U.1) :
    S.ρB n U (S.mul U x y) = S.ρB n U x * S.ρB n U y := by
  have := congrArg (fun θ : AffHom S.F2 (S.B n) => (θ.app U (x ⊗ₜ y) : S.BΓ n U.1)) (S.ρ_comp_m n)
  exact this

theorem res_mul (U U' : X.affineOpens) (hU : U.1 ≤ U'.1) (x y : S.F.obj U'.1) :
    S.F.res hU (S.mul U' x y) = S.mul U (S.F.res hU x) (S.F.res hU y) :=
  ((S.m).naturality_apply (U := U) (U' := U') hU (x ⊗ₜ y)).symm

theorem mul_add' (U : X.affineOpens) (x y z : S.F.obj U.1) : S.mul U x (y + z) = S.mul U x y + S.mul U x z := by
  rw [mul, tmul_add, map_add]; rfl

theorem add_mul' (U : X.affineOpens) (x y z : S.F.obj U.1) : S.mul U (x + y) z = S.mul U x z + S.mul U y z := by
  rw [mul, add_tmul, map_add]; rfl

theorem zero_mul' (U : X.affineOpens) (x : S.F.obj U.1) : S.mul U 0 x = 0 := by
  rw [mul, zero_tmul, map_zero]

theorem mul_zero' (U : X.affineOpens) (x : S.F.obj U.1) : S.mul U x 0 = 0 := by
  rw [mul, tmul_zero, map_zero]

theorem smul_mul' (U : X.affineOpens) (a : A U) (x y : S.F.obj U.1) : S.mul U (a • x) y = a • S.mul U x y := by
  rw [mul, mul, ← map_smul, smul_tmul']

theorem mul_smul' (U : X.affineOpens) (a : A U) (x y : S.F.obj U.1) : S.mul U x (a • y) = a • S.mul U x y := by
  rw [mul, mul, ← map_smul, tmul_smul]

def mswap : AffHom S.F2 S.F :=
  S.mkAffHom2 (fun U => S.appT2 S.m U ∘ₗ (TensorProduct.comm (A U) (S.F.obj U.1) (S.F.obj U.1)).toLinearMap)
    fun U U' hU x y => by
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, TensorProduct.comm_tmul]
      exact (S.res_mul U U' hU y x).symm

theorem mswap_tmul (U : X.affineOpens) (x y : S.F.obj U.1) : S.mswap.app U (x ⊗ₜ y) = S.mul U y x := by
  rw [mswap, mkAffHom2_app, LinearMap.comp_apply, LinearEquiv.coe_coe, TensorProduct.comm_tmul]
  rfl

theorem mswap_eq_m : S.mswap = S.m :=
  S.m_unique _ fun n => S.affHom2_ext _ _ fun U x y => by
    rw [AffHom.comp_app, mswap_tmul]
    apply S.B_inj n U
    change S.ρB n U (S.mul U y x) = ((S.μ n).app U (x ⊗ₜ y) : S.BΓ n U.1)
    rw [ρ_mul, μ_tmul, mul_comm]

theorem mul_comm' (U : X.affineOpens) (x y : S.F.obj U.1) : S.mul U x y = S.mul U y x := by
  have := congrArg (fun θ : AffHom S.F2 S.F => θ.app U (y ⊗ₜ x)) S.mswap_eq_m
  rw [mswap_tmul] at this
  exact this

def mone : AffHom S.F S.F :=
  mkAffHom
    (fun U =>
      { toFun := fun x => S.mul U (S.one U) x
        map_add' := fun x y => S.mul_add' U _ x y
        map_smul' := fun a x => S.mul_smul' U a _ x })
    fun U U' hU x => by
      change S.mul U (S.one U) (S.F.res hU x) = S.F.res hU (S.mul U' (S.one U') x)
      rw [res_mul, res_one]

theorem mone_app (U : X.affineOpens) (x : S.F.obj U.1) : S.mone.app U x = S.mul U (S.one U) x := rfl

theorem mone_eq_id : S.mone = AffHom.id S.F :=
  S.k42_unique S.F S.hFc S.hFq (AffHom.id S.F) S.mone fun n => affHom_ext _ _ fun U x => by
    rw [AffHom.comp_app, AffHom.comp_app, AffHom.id_app, mone_app]
    apply S.B_inj n U
    change S.ρB n U (S.mul U (S.one U) x) = S.ρB n U x
    rw [ρ_mul, ρ_one, one_mul]

theorem one_mul' (U : X.affineOpens) (x : S.F.obj U.1) : S.mul U (S.one U) x = x := by
  have := congrArg (fun θ : AffHom S.F S.F => θ.app U x) S.mone_eq_id
  exact this

theorem mul_one' (U : X.affineOpens) (x : S.F.obj U.1) : S.mul U x (S.one U) = x := by
  rw [mul_comm', one_mul']

theorem eta_mul (U : X.affineOpens) (a : A U) (x : S.F.obj U.1) :
    S.mul U (S.η.app U (show (unit f).obj U.1 from a)) x = a • x := by
  rw [η_eq_smul_one, smul_mul', one_mul']

def massocL : AffHom S.F3 S.F :=
  S.mkAffHom3 (fun U => S.appT2 S.m U ∘ₗ TensorProduct.map (S.appT2 S.m U) LinearMap.id)
    fun U U' hU x y z => by
      simp only [LinearMap.comp_apply, TensorProduct.map_tmul, LinearMap.id_apply]
      change S.mul U (S.mul U (S.F.res hU x) (S.F.res hU y)) (S.F.res hU z) = S.F.res hU (S.mul U' (S.mul U' x y) z)
      rw [res_mul, res_mul]

def massocR : AffHom S.F3 S.F :=
  S.mkAffHom3 (fun U => S.appT2 S.m U ∘ₗ TensorProduct.map LinearMap.id (S.appT2 S.m U) ∘ₗ
      (TensorProduct.assoc (A U) (S.F.obj U.1) (S.F.obj U.1) (S.F.obj U.1)).toLinearMap)
    fun U U' hU x y z => by
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, TensorProduct.assoc_tmul, TensorProduct.map_tmul,
        LinearMap.id_apply]
      change S.mul U (S.F.res hU x) (S.mul U (S.F.res hU y) (S.F.res hU z)) = S.F.res hU (S.mul U' x (S.mul U' y z))
      rw [res_mul, res_mul]

theorem massocL_tmul (U : X.affineOpens) (x y z : S.F.obj U.1) :
    S.appT3 S.massocL U ((x ⊗ₜ y) ⊗ₜ z) = S.mul U (S.mul U x y) z := by
  change (S.appT2 S.m U ∘ₗ TensorProduct.map (S.appT2 S.m U) LinearMap.id) ((x ⊗ₜ y) ⊗ₜ z) = _
  rw [LinearMap.comp_apply, TensorProduct.map_tmul, LinearMap.id_apply]
  rfl

theorem massocR_tmul (U : X.affineOpens) (x y z : S.F.obj U.1) :
    S.appT3 S.massocR U ((x ⊗ₜ y) ⊗ₜ z) = S.mul U x (S.mul U y z) := by
  change (S.appT2 S.m U ∘ₗ TensorProduct.map LinearMap.id (S.appT2 S.m U) ∘ₗ
      (TensorProduct.assoc (A U) (S.F.obj U.1) (S.F.obj U.1) (S.F.obj U.1)).toLinearMap) ((x ⊗ₜ y) ⊗ₜ z) = _
  rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearEquiv.coe_coe, TensorProduct.assoc_tmul,
    TensorProduct.map_tmul, LinearMap.id_apply]
  rfl

theorem F3_coh_qc : S.F3.IsCoherent ∧ S.F3.IsQuasicoherent := by
  have h2 := AlgebraicGeometry.OModulePresheaf.isQuasicoherent_isCoherent_supportedIn_tensor S.F S.F
  have h3 := AlgebraicGeometry.OModulePresheaf.isQuasicoherent_isCoherent_supportedIn_tensor S.F2 S.F
  exact ⟨h3.2.1 (h2.2.1 S.hFc S.hFc) S.hFc, h3.1 (h2.1 S.hFq S.hFq) S.hFq⟩

theorem massocR_eq_massocL : S.massocR = S.massocL :=
  S.k42_unique S.F3 S.F3_coh_qc.1 S.F3_coh_qc.2 S.massocL S.massocR fun n => S.affHom3_ext _ _ fun U x y z => by
    apply S.B_inj n U
    change S.ρB n U (S.appT3 S.massocR U ((x ⊗ₜ y) ⊗ₜ z)) = S.ρB n U (S.appT3 S.massocL U ((x ⊗ₜ y) ⊗ₜ z))
    rw [massocR_tmul, massocL_tmul, ρ_mul, ρ_mul, ρ_mul, ρ_mul, mul_assoc]

theorem mul_assoc' (U : X.affineOpens) (x y z : S.F.obj U.1) :
    S.mul U (S.mul U x y) z = S.mul U x (S.mul U y z) := by
  have := congrArg (fun θ : AffHom S.F3 S.F => S.appT3 θ U ((x ⊗ₜ y) ⊗ₜ z)) S.massocR_eq_massocL
  rw [massocR_tmul, massocL_tmul] at this
  exact this.symm

def Carrier (U : X.affineOpens) : Type u := S.F.obj U.1

def toF (U : X.affineOpens) (x : S.Carrier U) : S.F.obj U.1 := x

def ofF (U : X.affineOpens) (x : S.F.obj U.1) : S.Carrier U := x

scoped instance instCommRing (U : X.affineOpens) : CommRing (S.Carrier U) :=
  { (inferInstance : AddCommGroup (S.F.obj U.1)) with
    mul := S.mul U
    one := S.one U
    mul_assoc := S.mul_assoc' U
    one_mul := S.one_mul' U
    mul_one := S.mul_one' U
    mul_comm := S.mul_comm' U
    left_distrib := S.mul_add' U
    right_distrib := S.add_mul' U
    zero_mul := S.zero_mul' U
    mul_zero := S.mul_zero' U }

theorem carrier_mul (U : X.affineOpens) (x y : S.Carrier U) : x * y = S.mul U x y := rfl
theorem carrier_one (U : X.affineOpens) : (1 : S.Carrier U) = S.one U := rfl

def resRing {U V : X.affineOpens} (h : V.1 ≤ U.1) : S.Carrier U →+* S.Carrier V where
  toFun x := S.F.res h x
  map_one' := S.res_one V U h
  map_mul' x y := S.res_mul V U h x y
  map_zero' := map_zero (S.F.res h)
  map_add' x y := map_add (S.F.res h) x y

theorem resRing_apply {U V : X.affineOpens} (h : V.1 ≤ U.1) (x : S.Carrier U) : S.resRing h x = S.F.res h x := rfl

def etaRing (U : X.affineOpens) : A U →+* S.Carrier U where
  toFun a := S.η.app U (show (unit f).obj U.1 from a)
  map_one' := rfl
  map_mul' a b := by
    change S.η.app U (show (unit f).obj U.1 from a * b) =
      S.mul U (S.η.app U (show (unit f).obj U.1 from a)) (S.η.app U (show (unit f).obj U.1 from b))
    rw [eta_mul, η_eq_smul_one, η_eq_smul_one, smul_smul]
  map_zero' := map_zero (S.η.app U)
  map_add' a b := map_add (S.η.app U) a b

theorem etaRing_apply (U : X.affineOpens) (a : A U) : S.etaRing U a = S.η.app U (show (unit f).obj U.1 from a) := rfl

theorem etaRing_mul (U : X.affineOpens) (a : A U) (x : S.Carrier U) : S.etaRing U a * x = a • S.toF U x :=
  S.eta_mul U a x

theorem res_etaRing {U V : X.affineOpens} (h : V.1 ≤ U.1) (a : A U) :
    S.resRing h (S.etaRing U a) = S.etaRing V ((X.presheaf.map (homOfLE h).op).hom a) :=
  ((S.η).naturality_apply (U := V) (U' := U) h (show (unit f).obj U.1 from a)).symm

def rhoRing (n : ℕ) (U : X.affineOpens) : S.Carrier U →+* S.BΓ n U.1 where
  toFun x := S.ρB n U x
  map_one' := S.ρ_one n U
  map_mul' x y := S.ρ_mul n U x y
  map_zero' := S.ρ_zero n U
  map_add' x y := S.ρ_add n U x y

theorem finite_etaRing (U : X.affineOpens) : (S.etaRing U).Finite := by
  letI : Algebra (A U) (S.Carrier U) := (S.etaRing U).toAlgebra
  haveI : Module.Finite (A U) (S.F.obj U.1) := S.hFc U
  let l : S.F.obj U.1 →ₗ[A U] S.Carrier U :=
    { toFun := S.ofF U
      map_add' := fun _ _ => rfl
      map_smul' := fun a x => by
        change S.ofF U (a • x) = S.etaRing U a * S.ofF U x
        rw [etaRing_mul]; rfl }
  exact Module.Finite.of_surjective l fun x => ⟨x, rfl⟩

abbrev toAff (U : X.AffineZariskiSite) : X.affineOpens := ⟨U.1, U.2⟩

def Afun : X.AffineZariskiSiteᵒᵖ ⥤ CommRingCat.{u} where
  obj U := CommRingCat.of (S.Carrier (toAff U.unop))
  map {U V} i := CommRingCat.ofHom (S.resRing (U := toAff U.unop) (V := toAff V.unop)
    (Scheme.AffineZariskiSite.toOpens_mono i.unop.le))
  map_id U := CommRingCat.hom_ext (RingHom.ext fun x => S.F.res_refl_apply _ x)
  map_comp {U V W} i j := CommRingCat.hom_ext (RingHom.ext fun x => (S.F.res_res _ _ x).symm)

theorem Afun_map_apply {U V : X.AffineZariskiSiteᵒᵖ} (i : U ⟶ V) (x : S.Carrier (toAff U.unop)) :
    (S.Afun.map i).hom x = S.F.res (Scheme.AffineZariskiSite.toOpens_mono i.unop.le) x := rfl

def αNat : (Scheme.AffineZariskiSite.toOpensFunctor X).op ⋙ X.presheaf ⟶ S.Afun where
  app U := CommRingCat.ofHom (S.etaRing (toAff U.unop))
  naturality {U V} i := CommRingCat.hom_ext (RingHom.ext fun a => by
    change S.etaRing (toAff V.unop) ((X.presheaf.map ((Scheme.AffineZariskiSite.toOpensFunctor X).map i.unop).op).hom a) =
      S.resRing (U := toAff U.unop) (V := toAff V.unop) (Scheme.AffineZariskiSite.toOpens_mono i.unop.le)
        (S.etaRing (toAff U.unop) a)
    rw [res_etaRing]
    rfl)

theorem αNat_app_apply (U : X.AffineZariskiSite) (a : Γ(X, U.1)) :
    (S.αNat.app (op U)).hom a = S.etaRing (toAff U) a := rfl

theorem isLocalization_carrier (U : X.affineOpens) (r : A U) :
    letI := (S.resRing (U := U) (V := ⟨X.basicOpen r, U.2.basicOpen r⟩) (X.basicOpen_le r)).toAlgebra
    IsLocalization.Away (S.etaRing U r) (S.Carrier ⟨X.basicOpen r, U.2.basicOpen r⟩) := by
  set D : X.affineOpens := ⟨X.basicOpen r, U.2.basicOpen r⟩ with hD
  have hle : D.1 ≤ U.1 := X.basicOpen_le r
  letI := (S.resRing (U := U) (V := D) hle).toAlgebra
  have alg : ∀ x, algebraMap (S.Carrier U) (S.Carrier D) x = S.resRing hle x := fun _ => rfl
  have hq := S.hFq U r
  refine (isLocalization_iff _ _).mpr ⟨?_, ?_, ?_⟩
  · rintro ⟨_, k, rfl⟩
    rw [map_pow, alg, res_etaRing]
    exact ((X.toRingedSpace.isUnit_res_basicOpen r).map (S.etaRing D)).pow k
  · intro z
    obtain ⟨k, y, hy⟩ := hq.1 (S.toF D z)
    refine ⟨(S.ofF U y, ⟨S.etaRing U r ^ k, k, rfl⟩), ?_⟩
    change z * algebraMap _ _ (S.etaRing U r ^ k) = algebraMap _ _ (S.ofF U y)
    rw [alg, alg, map_pow, res_etaRing, ← map_pow, ← map_pow, _root_.mul_comm, etaRing_mul]
    exact hy.symm
  · intro x y hxy
    rw [alg, alg] at hxy
    have h0 : S.F.res hle (S.toF U x - S.toF U y) = 0 := by
      rw [map_sub, sub_eq_zero]; exact hxy
    obtain ⟨k, hk⟩ := hq.2 _ h0
    refine ⟨⟨S.etaRing U r ^ k, k, rfl⟩, ?_⟩
    change S.etaRing U r ^ k * x = S.etaRing U r ^ k * y
    rw [← map_pow, ← sub_eq_zero, ← _root_.mul_sub, etaRing_mul]
    exact hk

theorem isLocalizationAway (U : X.AffineZariskiSite) (r : Γ(X, U.1)) :
    letI := (S.Afun.map (homOfLE (U.basicOpen_le r)).op).hom.toAlgebra
    IsLocalization.Away ((S.αNat.app (op U)).hom r) (S.Afun.obj (op (U.basicOpen r))) :=
  S.isLocalization_carrier (toAff U) r

theorem coequifibered : S.αNat.Coequifibered :=
  Scheme.AffineZariskiSite.coequifibered_iff_forall_isLocalizationAway.mpr fun U r => S.isLocalizationAway U r

def eU (U : X.AffineZariskiSite) : S.Afun.obj (op U) ≃+ S.F.obj U.1 where
  toFun x := S.toF (toAff U) x
  invFun x := S.ofF (toAff U) x
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

theorem main :
    ∃ (A : X.AffineZariskiSiteᵒᵖ ⥤ CommRingCat.{u})
      (α : (Scheme.AffineZariskiSite.toOpensFunctor X).op ⋙ X.presheaf ⟶ A) (_ : α.Coequifibered)
      (e : ∀ U : X.AffineZariskiSite, A.obj (op U) ≃+ S.F.obj U.1),
      (∀ U : X.AffineZariskiSite, (α.app (op U)).hom.Finite) ∧
      (∀ (U : X.AffineZariskiSite) (a : Γ(X, U.1)) (x : A.obj (op U)),
        e U ((α.app (op U)).hom a * x) = a • e U x) ∧
      (∀ (U V : X.AffineZariskiSite) (i : V ⟶ U) (x : A.obj (op U)),
        e V ((A.map i.op).hom x) = S.F.res (Scheme.AffineZariskiSite.toOpens_mono i.le) (e U x)) ∧
      (∀ (n : ℕ) (U : X.AffineZariskiSite),
        ∃ r : A.obj (op U) →+* Γ(S.Y n, (S.g n ≫ pullback.fst f (S.sR n)) ⁻¹ᵁ U.1),
          ∀ x : A.obj (op U), r x = (S.ρ n).app ⟨U.1, U.2⟩ (e U x)) :=
  ⟨S.Afun, S.αNat, S.coequifibered, S.eU, fun U => S.finite_etaRing (toAff U),
    fun U a x => S.etaRing_mul (toAff U) a x, fun _ _ _ _ => rfl,
    fun n U => ⟨S.rhoRing n (toAff U), fun _ => rfl⟩⟩

end ASys
p2m_reactivate "P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_coequifibered_addEquiv_of_affHom_pushforwardUnit_of_isAdicComplete_of_isProper.AlgStructAux.ASys"

end AlgStructAux
p2m_reactivate "P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_coequifibered_addEquiv_of_affHom_pushforwardUnit_of_isAdicComplete_of_isProper.AlgStructAux.ASys P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_coequifibered_addEquiv_of_affHom_pushforwardUnit_of_isAdicComplete_of_isProper.AlgStructAux"

theorem solution
    (R : Type u) [CommRing R] [IsNoetherianRing R] (I : Ideal R) [IsAdicComplete I R]
    (X : Scheme.{u}) (f : X ⟶ Spec (CommRingCat.of R)) [IsProper f]

    (sR : ∀ n : ℕ, Spec (CommRingCat.of (R ⧸ I ^ (n + 1))) ⟶ Spec (CommRingCat.of R))
    (hsR : ∀ n : ℕ, sR n = Spec.map (CommRingCat.ofHom (algebraMap R (R ⧸ I ^ (n + 1)))))
    (tR : ∀ n : ℕ, Spec (CommRingCat.of (R ⧸ I ^ (n + 1))) ⟶ Spec (CommRingCat.of (R ⧸ I ^ (n + 1 + 1))))
    (htR : ∀ n : ℕ, tR n ≫ sR (n + 1) = sR n)

    (xn : ∀ n : ℕ, Limits.pullback f (sR n) ⟶ Limits.pullback f (sR (n + 1)))
    (hxn₁ : ∀ n : ℕ, xn n ≫ Limits.pullback.fst f (sR (n + 1)) = Limits.pullback.fst f (sR n))
    (hxn₂ : ∀ n : ℕ, xn n ≫ Limits.pullback.snd f (sR (n + 1)) = Limits.pullback.snd f (sR n) ≫ tR n)

    (Y : ℕ → Scheme.{u}) (g : ∀ n : ℕ, Y n ⟶ Limits.pullback f (sR n)) [∀ n : ℕ, IsFinite (g n)]
    (yn : ∀ n : ℕ, Y n ⟶ Y (n + 1))
    (hY : ∀ n : ℕ, IsPullback (yn n) (g n) (g (n + 1)) (xn n))
    (F : OModulePresheaf f) (hFc : F.IsCoherent) (hFq : F.IsQuasicoherent)
    (ρ : ∀ n : ℕ, OModulePresheaf.AffHom F (OModulePresheaf.pushforwardUnit f (g n ≫ pullback.fst f (sR n))))
    (hρs : ∀ (n : ℕ) (U : X.affineOpens), Function.Surjective ((ρ n).app U))
    (hρk : ∀ (n : ℕ) (U : X.affineOpens),
      LinearMap.ker ((ρ n).app U) = I ^ (n + 1) • (⊤ : Submodule R (F.obj U.1)))
    (hρc : ∀ (n : ℕ) (U : X.affineOpens) (x : F.obj U.1),
      (ρ n).app U x =
        ((yn n).appLE ((g (n + 1) ≫ pullback.fst f (sR (n + 1))) ⁻¹ᵁ U.1) ((g n ≫ pullback.fst f (sR n)) ⁻¹ᵁ U.1)
          (by rw [← Scheme.Hom.comp_preimage, ← Category.assoc, (hY n).w, Category.assoc, hxn₁])).hom
          ((ρ (n + 1)).app U x)) :
    ∃ (A : X.AffineZariskiSiteᵒᵖ ⥤ CommRingCat.{u})
      (α : (Scheme.AffineZariskiSite.toOpensFunctor X).op ⋙ X.presheaf ⟶ A) (_ : α.Coequifibered)
      (e : ∀ U : X.AffineZariskiSite, A.obj (op U) ≃+ F.obj U.1),
      (∀ U : X.AffineZariskiSite, (α.app (op U)).hom.Finite) ∧
      (∀ (U : X.AffineZariskiSite) (a : Γ(X, U.1)) (x : A.obj (op U)),
        e U ((α.app (op U)).hom a * x) = a • e U x) ∧
      (∀ (U V : X.AffineZariskiSite) (i : V ⟶ U) (x : A.obj (op U)),
        e V ((A.map i.op).hom x) = F.res (Scheme.AffineZariskiSite.toOpens_mono i.le) (e U x)) ∧
      (∀ (n : ℕ) (U : X.AffineZariskiSite),
        ∃ r : A.obj (op U) →+* Γ(Y n, (g n ≫ pullback.fst f (sR n)) ⁻¹ᵁ U.1),
          ∀ x : A.obj (op U), r x = (ρ n).app ⟨U.1, U.2⟩ (e U x)) :=
  AlgStructAux.ASys.main (I := I) (f := f)
    { sR := sR, hsR := hsR, tR := tR, htR := htR, xn := xn, hxn₁ := hxn₁, hxn₂ := hxn₂, Y := Y, g := g,
      hg := inferInstance, yn := yn, hY := hY, F := F, hFc := hFc, hFq := hFq, ρ := ρ, hρs := hρs, hρk := hρk,
      hρc := hρc }

end
p2m_reactivate "P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_coequifibered_addEquiv_of_affHom_pushforwardUnit_of_isAdicComplete_of_isProper.AlgStructAux.ASys P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_coequifibered_addEquiv_of_affHom_pushforwardUnit_of_isAdicComplete_of_isProper.AlgStructAux"

end S_AlgebraicGeometry_OModulePresheaf_exists_coequifibered_addEquiv_of_affHom_pushforwardUnit_of_isAdicComplete_of_isProper
end P2MW
export P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_coequifibered_addEquiv_of_affHom_pushforwardUnit_of_isAdicComplete_of_isProper (solution)
