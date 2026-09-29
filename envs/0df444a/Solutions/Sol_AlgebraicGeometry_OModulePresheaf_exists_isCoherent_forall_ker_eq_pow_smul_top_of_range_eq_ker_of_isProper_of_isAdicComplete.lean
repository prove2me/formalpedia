-- Prove2me | solution 1 for AlgebraicGeometry.OModulePresheaf.exists_isCoherent_forall_ker_eq_pow_smul_top_of_range_eq_ker_of_isProper_of_isAdicComplete
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/c4c3fc29-34a6-5588-a5d9-f66317293121

import Mathlib
import Definitions.Def_AlgebraicGeometry_OModulePresheafHom
import Theorems.Thm_Module_exists_forall_surjective_ker_eq_pow_smul_top_of_adic_of_range_eq_ker
import Theorems.Thm_Module_existsUnique_compatible_lift_of_range_eq_ker_of_ker_le_pow_smul
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_existsUnique_affHom_comp_eq_of_isAdicComplete_of_isProper
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_AffHom_exists_isQuasicoherent_injective_range_eq_ker
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_forall_ker_eq_pow_smul_top_of_range_eq_ker_of_isProper_of_isAdicComplete
p2m_attr_erase "instance" "AlgebraicGeometry.OModulePresheaf.moduleSectionsHomSub AlgebraicGeometry.OModulePresheaf.smulSections AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul AlgebraicGeometry.OModulePresheaf.Leray.biC_module AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I AlgebraicGeometry.ChowDatum.hι_closed AlgebraicGeometry.ChowDatumProj.hιN_closed AlgebraicGeometry.ChowDatumProj.hp_proper AlgebraicGeometry.ChowDatum.hp_isoU AlgebraicGeometry.ChowDatum.hp_proper AlgebraicGeometry.ProjSpace.algebraAway AlgebraicGeometry.ProjSpace.instIsProperProdOverπ AlgebraicGeometry.ChowDatumProj.hp_isoU AlgebraicGeometry.ProjSpace.isProper_π AlgebraicGeometry.ProjSpace.finiteType_mvPolynomial ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule"
p2m_attr_erase "instance" "ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule"
p2m_attr_erase "simp" "AlgebraicGeometry.OModulePresheaf.internalHom.ofAffHom_apply AlgebraicGeometry.OModulePresheaf.internalHom.toAffHom_app AlgebraicGeometry.OModulePresheaf.prod_obj AlgebraicGeometry.OModulePresheaf.restrOpen_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq AlgebraicGeometry.OModulePresheaf.pushforward_obj AlgebraicGeometry.OModulePresheaf.im_obj AlgebraicGeometry.OModulePresheaf.pow_obj AlgebraicGeometry.OModulePresheaf.fstHom_app AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U AlgebraicGeometry.OModulePresheaf.sndHom_app AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq AlgebraicGeometry.ChowDatumProj.mk.sizeOf_spec AlgebraicGeometry.ChowDatum.mk.sizeOf_spec AlgebraicGeometry.ChowDatumProj.mk.injEq AlgebraicGeometry.ChowDatum.mk.injEq ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.mk.injEq"

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry

universe u

namespace C5vAux

theorem affHom_ext {R : Type u} [CommRing R] {V : Scheme.{u}} {π : V ⟶ Spec (CommRingCat.of R)}
    {F G : OModulePresheaf π} (a b : OModulePresheaf.AffHom F G) (h : ∀ U : V.affineOpens, a.app U = b.app U) :
    a = b := by
  obtain ⟨appa, sa, na⟩ := a
  obtain ⟨appb, sb, nb⟩ := b
  have : appa = appb := funext h
  subst this
  rfl

theorem affHom_comp_app {R : Type u} [CommRing R] {V : Scheme.{u}} {π : V ⟶ Spec (CommRingCat.of R)}
    {F G H : OModulePresheaf π} (a : OModulePresheaf.AffHom F G) (b : OModulePresheaf.AffHom G H)
    (U : V.affineOpens) : (b.comp a).app U = b.app U ∘ₗ a.app U := rfl

theorem restrictScalars_map_pow_smul_top {A B : Type u} [CommRing A] [CommRing B] [Algebra A B] (I : Ideal A)
    {X : Type u} [AddCommGroup X] [Module A X] [Module B X] [IsScalarTower A B X] (n : ℕ) :
    ((I.map (algebraMap A B)) ^ n • (⊤ : Submodule B X)).restrictScalars A = I ^ n • (⊤ : Submodule A X) := by
  rw [← Ideal.map_pow]
  generalize I ^ n = J
  have hB : ∀ (c : B) (y : X), y ∈ (J • (⊤ : Submodule A X) : Submodule A X) →
      c • y ∈ (J • (⊤ : Submodule A X) : Submodule A X) := by
    intro c y hy
    refine Submodule.smul_induction_on (p := fun y => c • y ∈ (J • (⊤ : Submodule A X) : Submodule A X)) hy ?_ ?_
    · intro a ha x _
      rw [smul_comm]
      exact Submodule.smul_mem_smul ha Submodule.mem_top
    · intro x y hx hy
      rw [smul_add]; exact Submodule.add_mem _ hx hy
  apply le_antisymm
  · intro x hx
    rw [Submodule.restrictScalars_mem] at hx
    refine Submodule.smul_induction_on (p := fun x => x ∈ (J • (⊤ : Submodule A X) : Submodule A X)) hx ?_ ?_
    · intro b hb x _
      rw [Ideal.map, Submodule.mem_span_iff_exists_finset_subset] at hb
      obtain ⟨f, t, ht, hf, rfl⟩ := hb
      rw [Finset.sum_smul]
      refine Submodule.sum_mem _ fun b' hb' => ?_
      obtain ⟨a, ha, rfl⟩ := ht hb'
      rw [smul_eq_mul, mul_smul, algebraMap_smul]
      exact hB _ _ (Submodule.smul_mem_smul ha Submodule.mem_top)
    · intro x y hx hy; exact Submodule.add_mem _ hx hy
  · refine Submodule.smul_le.2 fun a ha x _ => ?_
    rw [Submodule.restrictScalars_mem, ← algebraMap_smul B a x]
    exact Submodule.smul_mem_smul (Ideal.mem_map_of_mem _ ha) Submodule.mem_top

theorem restrictScalars_ker {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    {X Y : Type u} [AddCommGroup X] [Module A X] [Module B X] [IsScalarTower A B X]
    [AddCommGroup Y] [Module A Y] [Module B Y] [IsScalarTower A B Y] (f : X →ₗ[B] Y) :
    (LinearMap.ker f).restrictScalars A = LinearMap.ker (f.restrictScalars A) := rfl

theorem restrictScalars_range {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    {X Y : Type u} [AddCommGroup X] [Module A X] [Module B X] [IsScalarTower A B X]
    [AddCommGroup Y] [Module A Y] [Module B Y] [IsScalarTower A B Y] (f : X →ₗ[B] Y) :
    (LinearMap.range f).restrictScalars A = LinearMap.range (f.restrictScalars A) := by
  ext y
  simp [Submodule.restrictScalars_mem, LinearMap.mem_range]

end C5vAux

namespace C5v

theorem eq_of_compatible_of_apply_eq
    {R : Type u} [CommRing R] (I : Ideal R)
    (E : ℕ → Type u) [∀ k, AddCommGroup (E k)] [∀ k, Module R (E k)]
    (τ : ∀ k, E (k + 1) →ₗ[R] E k) (hτs : ∀ k, Function.Surjective (τ k))
    (hτk : ∀ k, LinearMap.ker (τ k) = I ^ (k + 1) • (⊤ : Submodule R (E (k + 1))))
    (P : ℕ → Type u) [∀ k, AddCommGroup (P k)] [∀ k, Module R (P k)] (π : ∀ k, P (k + 1) →ₗ[R] P k)
    (C : ℕ → Type u) [∀ k, AddCommGroup (C k)] [∀ k, Module R (C k)] (θ : ∀ k, P k →ₗ[R] C k)
    (u : ∀ k, E k →ₗ[R] P k) (huc : ∀ k, π k ∘ₗ u (k + 1) = u k ∘ₗ τ k)
    (hur : ∀ k, LinearMap.range (u k) = LinearMap.ker (θ k))
    (hui : ∃ c : ℕ, ∀ k : ℕ, LinearMap.ker (u (k + c)) ≤ I ^ (k + 1) • (⊤ : Submodule R (E (k + c))))
    (a b : ∀ k, E k) (ha : ∀ k, τ k (a (k + 1)) = a k) (hb : ∀ k, τ k (b (k + 1)) = b k)
    (hab : ∀ k, u k (a k) = u k (b k)) : a = b := by
  have hp : ∀ k, π k (u (k + 1) (a (k + 1))) = u k (a k) := fun k => by
    have h := LinearMap.congr_fun (huc k) (a (k + 1))
    simp only [LinearMap.coe_comp, Function.comp_apply] at h
    rw [h, ha]
  have hpθ : ∀ k, θ k (u k (a k)) = 0 := fun k => by
    have : u k (a k) ∈ LinearMap.ker (θ k) := by rw [← hur k]; exact LinearMap.mem_range_self _ _
    exact this
  obtain ⟨e, -, huniq⟩ :=
    Module.existsUnique_compatible_lift_of_range_eq_ker_of_ker_le_pow_smul I E τ hτs hτk P π C θ u huc hur hui
      (fun k => u k (a k)) hp hpθ
  exact (huniq a ⟨ha, fun _ => rfl⟩).trans (huniq b ⟨hb, fun k => (hab k).symm⟩).symm

theorem eq_of_compatible_of_comp_eq
    {R : Type u} [CommRing R] (I : Ideal R)
    (E : ℕ → Type u) [∀ k, AddCommGroup (E k)] [∀ k, Module R (E k)]
    (τ : ∀ k, E (k + 1) →ₗ[R] E k) (hτs : ∀ k, Function.Surjective (τ k))
    (hτk : ∀ k, LinearMap.ker (τ k) = I ^ (k + 1) • (⊤ : Submodule R (E (k + 1))))
    (P : ℕ → Type u) [∀ k, AddCommGroup (P k)] [∀ k, Module R (P k)] (π : ∀ k, P (k + 1) →ₗ[R] P k)
    (C : ℕ → Type u) [∀ k, AddCommGroup (C k)] [∀ k, Module R (C k)] (θ : ∀ k, P k →ₗ[R] C k)
    (u : ∀ k, E k →ₗ[R] P k) (huc : ∀ k, π k ∘ₗ u (k + 1) = u k ∘ₗ τ k)
    (hur : ∀ k, LinearMap.range (u k) = LinearMap.ker (θ k))
    (hui : ∃ c : ℕ, ∀ k : ℕ, LinearMap.ker (u (k + c)) ≤ I ^ (k + 1) • (⊤ : Submodule R (E (k + c))))
    {X : Type u} [AddCommGroup X] [Module R X]
    (a b : ∀ k, X →ₗ[R] E k) (ha : ∀ k, τ k ∘ₗ a (k + 1) = a k) (hb : ∀ k, τ k ∘ₗ b (k + 1) = b k)
    (hab : ∀ k, u k ∘ₗ a k = u k ∘ₗ b k) : a = b := by
  funext k
  ext x
  have h := eq_of_compatible_of_apply_eq I E τ hτs hτk P π C θ u huc hur hui
    (fun j => a j x) (fun j => b j x)
    (fun j => LinearMap.congr_fun (ha j) x) (fun j => LinearMap.congr_fun (hb j) x)
    (fun j => LinearMap.congr_fun (hab j) x)
  exact congrFun h k

end C5v

namespace C5vAux2
open AlgebraicGeometry
theorem appSections_restrictScalars {R : Type u} [CommRing R] {V : Scheme.{u}} {π : V ⟶ Spec (CommRingCat.of R)}
    {F G : OModulePresheaf π} (φ : OModulePresheaf.AffHom F G) (U : V.affineOpens) :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom π U.1
    (φ.appSections U).restrictScalars R = φ.app U :=
  LinearMap.ext fun _ => rfl
end C5vAux2

theorem solution
    {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A) [IsAdicComplete I A]
    {P : Scheme.{u}} (q : P ⟶ Spec (CommRingCat.of A)) [IsProper q]
    (E : ℕ → OModulePresheaf q) (hEc : ∀ k, (E k).IsCoherent) (hEq : ∀ k, (E k).IsQuasicoherent)
    (τ : ∀ k, OModulePresheaf.AffHom (E (k + 1)) (E k))
    (hτs : ∀ (k : ℕ) (U : P.affineOpens), Function.Surjective ((τ k).app U))
    (hτk : ∀ (k : ℕ) (U : P.affineOpens),
      LinearMap.ker ((τ k).app U) = I ^ (k + 1) • (⊤ : Submodule A ((E (k + 1)).obj U.1)))
    (Ps : ℕ → OModulePresheaf q) (hPsc : ∀ k, (Ps k).IsCoherent) (hPsq : ∀ k, (Ps k).IsQuasicoherent)
    (π : ∀ k, OModulePresheaf.AffHom (Ps (k + 1)) (Ps k))
    (hπs : ∀ (k : ℕ) (U : P.affineOpens), Function.Surjective ((π k).app U))
    (hπk : ∀ (k : ℕ) (U : P.affineOpens),
      LinearMap.ker ((π k).app U) = I ^ (k + 1) • (⊤ : Submodule A ((Ps (k + 1)).obj U.1)))
    (Cs : ℕ → OModulePresheaf q) (hCsc : ∀ k, (Cs k).IsCoherent) (hCsq : ∀ k, (Cs k).IsQuasicoherent)
    (γ : ∀ k, OModulePresheaf.AffHom (Cs (k + 1)) (Cs k))
    (hγs : ∀ (k : ℕ) (U : P.affineOpens), Function.Surjective ((γ k).app U))
    (hγk : ∀ (k : ℕ) (U : P.affineOpens),
      LinearMap.ker ((γ k).app U) = I ^ (k + 1) • (⊤ : Submodule A ((Cs (k + 1)).obj U.1)))
    (θ : ∀ k, OModulePresheaf.AffHom (Ps k) (Cs k))
    (hθc : ∀ (k : ℕ) (U : P.affineOpens), (γ k).app U ∘ₗ (θ (k + 1)).app U = (θ k).app U ∘ₗ (π k).app U)
    (u : ∀ k, OModulePresheaf.AffHom (E k) (Ps k))
    (huc : ∀ (k : ℕ) (U : P.affineOpens), (π k).app U ∘ₗ (u (k + 1)).app U = (u k).app U ∘ₗ (τ k).app U)
    (hur : ∀ (k : ℕ) (U : P.affineOpens), LinearMap.range ((u k).app U) = LinearMap.ker ((θ k).app U))
    (hui : ∀ U : P.affineOpens, ∃ c : ℕ, ∀ k : ℕ,
      LinearMap.ker ((u (k + c)).app U) ≤ I ^ (k + 1) • (⊤ : Submodule A ((E (k + c)).obj U.1)))
    (GP : OModulePresheaf q) (hGPc : GP.IsCoherent) (hGPq : GP.IsQuasicoherent)
    (ψP : ∀ k, OModulePresheaf.AffHom GP (Ps k))
    (hψPs : ∀ (k : ℕ) (U : P.affineOpens), Function.Surjective ((ψP k).app U))
    (hψPk : ∀ (k : ℕ) (U : P.affineOpens),
      LinearMap.ker ((ψP k).app U) = I ^ (k + 1) • (⊤ : Submodule A (GP.obj U.1)))
    (hψPc : ∀ (k : ℕ) (U : P.affineOpens), (π k).app U ∘ₗ (ψP (k + 1)).app U = (ψP k).app U)
    (GC : OModulePresheaf q) (hGCc : GC.IsCoherent) (hGCq : GC.IsQuasicoherent)
    (ψC : ∀ k, OModulePresheaf.AffHom GC (Cs k))
    (hψCs : ∀ (k : ℕ) (U : P.affineOpens), Function.Surjective ((ψC k).app U))
    (hψCk : ∀ (k : ℕ) (U : P.affineOpens),
      LinearMap.ker ((ψC k).app U) = I ^ (k + 1) • (⊤ : Submodule A (GC.obj U.1)))
    (hψCc : ∀ (k : ℕ) (U : P.affineOpens), (γ k).app U ∘ₗ (ψC (k + 1)).app U = (ψC k).app U) :
    ∃ (G : OModulePresheaf q) (ψ : ∀ k, OModulePresheaf.AffHom G (E k)),
      G.IsCoherent ∧ G.IsQuasicoherent ∧
      (∀ (k : ℕ) (U : P.affineOpens), Function.Surjective ((ψ k).app U)) ∧
      (∀ (k : ℕ) (U : P.affineOpens),
        LinearMap.ker ((ψ k).app U) = I ^ (k + 1) • (⊤ : Submodule A (G.obj U.1))) ∧
      (∀ (k : ℕ) (U : P.affineOpens), (τ k).app U ∘ₗ (ψ (k + 1)).app U = (ψ k).app U) := by
  classical

  haveI : IsLocallyNoetherian P := LocallyOfFiniteType.isLocallyNoetherian q

  have e1 : ∀ n, (γ n).comp (ψC (n + 1)) = ψC n := fun n => C5vAux.affHom_ext _ _ (fun U => hψCc n U)
  have e2 : ∀ n, (γ n).comp ((θ (n + 1)).comp (ψP (n + 1))) = (θ n).comp (ψP n) := fun n =>
    C5vAux.affHom_ext _ _ (fun U => by
      show (γ n).app U ∘ₗ ((θ (n + 1)).app U ∘ₗ (ψP (n + 1)).app U) = (θ n).app U ∘ₗ (ψP n).app U
      rw [← LinearMap.comp_assoc, hθc n U, LinearMap.comp_assoc, hψPc n U])
  obtain ⟨ρ, hρ, -⟩ :=
    AlgebraicGeometry.OModulePresheaf.existsUnique_affHom_comp_eq_of_isAdicComplete_of_isProper I q GP GC hGPc hGPq hGCc hGCq
      Cs γ ψC hψCs hψCk e1 (fun n => (θ n).comp (ψP n)) e2
  have hρU : ∀ (n : ℕ) (U : P.affineOpens), (ψC n).app U ∘ₗ ρ.app U = (θ n).app U ∘ₗ (ψP n).app U :=
    fun n U => congrArg (fun a => OModulePresheaf.AffHom.app a U) (hρ n)

  obtain ⟨G, ιG, hGcoh, hGq, hιi, hιr⟩ :=
    AlgebraicGeometry.OModulePresheaf.AffHom.exists_isQuasicoherent_injective_range_eq_ker hGPq hGCq ρ
  have hGc : G.IsCoherent := hGcoh inferInstance hGPc

  have main : ∀ U : P.affineOpens, ∃ ψU : ∀ k, G.obj U.1 →ₗ[A] (E k).obj U.1,
      (∀ (k : ℕ) (a : Γ(P, U.1)) (x : G.obj U.1), ψU k (a • x) = a • ψU k x) ∧
      (∀ k, Function.Surjective (ψU k)) ∧
      (∀ k, LinearMap.ker (ψU k) = I ^ (k + 1) • (⊤ : Submodule A (G.obj U.1))) ∧
      (∀ k, (τ k).app U ∘ₗ ψU (k + 1) = ψU k) ∧
      (∀ k, (u k).app U ∘ₗ ψU k = (ψP k).app U ∘ₗ ιG.app U) := by
    intro U
    letI alg : Algebra A Γ(P, U.1) := Scheme.TwoAffineOpenCover.algebraOfHom q U.1
    haveI : IsNoetherianRing Γ(P, U.1) := IsLocallyNoetherian.component_noetherian U
    haveI : Module.Finite Γ(P, U.1) (GP.obj U.1) := hGPc U
    haveI : Module.Finite Γ(P, U.1) (GC.obj U.1) := hGCc U
    set J : Ideal Γ(P, U.1) := I.map (algebraMap A Γ(P, U.1)) with hJ

    have brK : ∀ {X Y : OModulePresheaf q} (φ : OModulePresheaf.AffHom X Y) (n : ℕ),
        LinearMap.ker (φ.app U) = I ^ n • (⊤ : Submodule A (X.obj U.1)) →
        LinearMap.ker (φ.appSections U) = J ^ n • (⊤ : Submodule Γ(P, U.1) (X.obj U.1)) := by
      intro X Y φ n h
      apply Submodule.restrictScalars_injective A
      rw [C5vAux.restrictScalars_ker, C5vAux2.appSections_restrictScalars, hJ, C5vAux.restrictScalars_map_pow_smul_top]
      exact h
    have brR : ∀ {X Y Z : OModulePresheaf q} (φ : OModulePresheaf.AffHom X Y) (φ' : OModulePresheaf.AffHom Y Z),
        LinearMap.range (φ.app U) = LinearMap.ker (φ'.app U) →
        LinearMap.range (φ.appSections U) = LinearMap.ker (φ'.appSections U) := by
      intro X Y Z φ φ' h
      apply Submodule.restrictScalars_injective A
      rw [C5vAux.restrictScalars_ker, C5vAux.restrictScalars_range, C5vAux2.appSections_restrictScalars,
        C5vAux2.appSections_restrictScalars]
      exact h
    have brC : ∀ {X Y Z : OModulePresheaf q} (a : OModulePresheaf.AffHom X Y) (b : OModulePresheaf.AffHom Y Z)
        (c : OModulePresheaf.AffHom X Z), b.app U ∘ₗ a.app U = c.app U →
        b.appSections U ∘ₗ a.appSections U = c.appSections U := by
      intro X Y Z a b c h
      exact LinearMap.ext fun x => LinearMap.congr_fun h x
    have brC2 : ∀ {X Y Y' Z : OModulePresheaf q} (a : OModulePresheaf.AffHom X Y) (b : OModulePresheaf.AffHom Y Z)
        (a' : OModulePresheaf.AffHom X Y') (b' : OModulePresheaf.AffHom Y' Z), b.app U ∘ₗ a.app U = b'.app U ∘ₗ a'.app U →
        b.appSections U ∘ₗ a.appSections U = b'.appSections U ∘ₗ a'.appSections U := by
      intro X Y Y' Z a b a' b' h
      exact LinearMap.ext fun x => LinearMap.congr_fun h x
    obtain ⟨c, hcU⟩ := hui U
    have hui' : ∃ c : ℕ, ∀ k : ℕ, LinearMap.ker ((u (k + c)).appSections U) ≤
        J ^ (k + 1) • (⊤ : Submodule Γ(P, U.1) ((E (k + c)).obj U.1)) := by
      refine ⟨c, fun k x hx => ?_⟩
      have hx' : x ∈ I ^ (k + 1) • (⊤ : Submodule A ((E (k + c)).obj U.1)) := hcU k hx
      rw [← C5vAux.restrictScalars_map_pow_smul_top (B := Γ(P, U.1)) I (k + 1)] at hx'
      rwa [hJ]
    obtain ⟨ψB, hBs, hBk, hBc, hBl⟩ :=
      Module.exists_forall_surjective_ker_eq_pow_smul_top_of_adic_of_range_eq_ker (R := Γ(P, U.1)) J
        (ρ.appSections U) (ιG.appSections U) (hιi U) (brR ιG ρ (hιr U))
        (fun k => (E k).obj U.1) (fun k => (τ k).appSections U) (fun k => hτs k U) (fun k => brK (τ k) (k + 1) (hτk k U))
        (fun k => (Ps k).obj U.1) (fun k => (π k).appSections U)
        (fun k => (ψP k).appSections U) (fun k => hψPs k U) (fun k => brK (ψP k) (k + 1) (hψPk k U))
        (fun k => brC (ψP (k + 1)) (π k) (ψP k) (hψPc k U))
        (fun k => (Cs k).obj U.1) (fun k => (γ k).appSections U)
        (fun k => (ψC k).appSections U) (fun k => hψCs k U) (fun k => brK (ψC k) (k + 1) (hψCk k U))
        (fun k => brC (ψC (k + 1)) (γ k) (ψC k) (hψCc k U))
        (fun k => (θ k).appSections U) (fun k => brC2 (ψP k) (θ k) ρ (ψC k) (hρU k U).symm)
        (fun k => (u k).appSections U) (fun k => brC2 (u (k + 1)) (π k) (τ k) (u k) (huc k U))
        (fun k => brR (u k) (θ k) (hur k U)) hui'
    refine ⟨fun k => (ψB k).restrictScalars A, fun k a x => (ψB k).map_smul a x, fun k => hBs k, fun k => ?_, fun k => ?_, fun k => ?_⟩
    · rw [← C5vAux.restrictScalars_ker, hBk, hJ, C5vAux.restrictScalars_map_pow_smul_top]
    · exact LinearMap.ext fun x => LinearMap.congr_fun (hBc k) x
    · exact LinearMap.ext fun x => LinearMap.congr_fun (hBl k) x
  choose ψU hsm hs hk hc hl using main

  have hnat : ∀ (k : ℕ) {U U' : P.affineOpens} (h : U.1 ≤ U'.1), ψU U k ∘ₗ G.res h = (E k).res h ∘ₗ ψU U' k := by
    intro k U U' h
    have key := C5v.eq_of_compatible_of_comp_eq (R := A) I
      (fun k => (E k).obj U.1) (fun k => (τ k).app U) (fun k => hτs k U) (fun k => hτk k U)
      (fun k => (Ps k).obj U.1) (fun k => (π k).app U) (fun k => (Cs k).obj U.1) (fun k => (θ k).app U)
      (fun k => (u k).app U) (fun k => huc k U) (fun k => hur k U) (hui U)
      (fun k => ψU U k ∘ₗ G.res h) (fun k => (E k).res h ∘ₗ ψU U' k)
      (fun k => by
        show (τ k).app U ∘ₗ (ψU U (k + 1) ∘ₗ G.res h) = ψU U k ∘ₗ G.res h
        rw [← LinearMap.comp_assoc, hc U k])
      (fun k => by
        show (τ k).app U ∘ₗ ((E (k + 1)).res h ∘ₗ ψU U' (k + 1)) = (E k).res h ∘ₗ ψU U' k
        rw [← LinearMap.comp_assoc, (τ k).naturality h, LinearMap.comp_assoc, hc U' k])
      (fun k => by
        show (u k).app U ∘ₗ (ψU U k ∘ₗ G.res h) = (u k).app U ∘ₗ ((E k).res h ∘ₗ ψU U' k)
        rw [← LinearMap.comp_assoc, hl U k, LinearMap.comp_assoc, ιG.naturality h, ← LinearMap.comp_assoc,
          (ψP k).naturality h]
        conv_rhs => rw [← LinearMap.comp_assoc, (u k).naturality h, LinearMap.comp_assoc, hl U' k]
        rw [LinearMap.comp_assoc])
    exact congrFun key k
  exact ⟨G, fun k => ⟨fun U => ψU U k, fun U a x => hsm U k a x, fun h => hnat k h⟩, hGc, hGq,
    fun k U => hs U k, fun k U => hk U k, fun k U => hc U k⟩

end S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_forall_ker_eq_pow_smul_top_of_range_eq_ker_of_isProper_of_isAdicComplete
end P2MW
export P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_forall_ker_eq_pow_smul_top_of_range_eq_ker_of_isProper_of_isAdicComplete (solution)
