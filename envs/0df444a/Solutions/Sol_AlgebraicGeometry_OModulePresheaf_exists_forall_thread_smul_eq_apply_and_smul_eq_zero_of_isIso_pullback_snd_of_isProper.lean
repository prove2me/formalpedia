-- Prove2me | solution 1 for AlgebraicGeometry.OModulePresheaf.exists_forall_thread_smul_eq_apply_and_smul_eq_zero_of_isIso_pullback_snd_of_isProper
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/721b03f5-097c-5187-bda3-d14e4b8eb9f9

import Mathlib
import Definitions.Def_AlgebraicGeometry_OModulePresheafIdealFiltration
import Definitions.Def_AlgebraicGeometry_OModulePresheafCechPushforward
import Theorems.Thm_AdicCompletion_exists_module_finite_forall_comp_eq_and_ker_eq_pow_smul_top_of_forall_surjective
import Theorems.Thm_AdicCompletion_isAdicComplete_map_algebraMap_of_fg
import Theorems.Thm_Module_exists_pow_smul_ker_eq_zero_and_pow_smul_le_range_of_forall_exists_pow_smul
import Theorems.Thm_AdicCompletion_isNoetherianRing_of_isNoetherianRing
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_isPullback_isProper_and_exists_forall_surjective_ker_eq_pow_smul_top_of_forall_ker_eq_pow_smul_top
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_forall_eq_thread_and_eq_zero_of_forall_eq_zero_of_isAdicComplete_of_isProper
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_pow_smul_eq_zero_and_exists_eq_pow_smul_of_mem_vanishingIdeal_of_isIso_pullback_snd
import Theorems.Thm_AdicCompletion_exists_ringHom_comp_algebraMap_eq_and_flat_of_flat_of_finiteType
import Theorems.Thm_AdicCompletion_exists_bijective_forall_apply_tmul_eq_of_isBaseChange_of_forall_ker_eq_pow_smul_top
import Theorems.Thm_LinearMap_forall_smul_eq_zero_of_baseChange_eq_zero_and_forall_exists_baseChange_eq_smul_of_flat
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_IsQuasicoherent_exists_linearEquiv_tensorProduct_apply_one_tmul_eq_res
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_forall_smul_eq_zero_and_exists_eq_smul_of_le_of_flat_of_bijective
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_forall_thread_smul_eq_apply_and_smul_eq_zero_of_isIso_pullback_snd_of_isProper
p2m_attr_erase "instance" "DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I AlgebraicGeometry.ChowDatum.hι_closed AlgebraicGeometry.ChowDatumProj.hιN_closed AlgebraicGeometry.ChowDatumProj.hp_proper AlgebraicGeometry.ChowDatum.hp_isoU AlgebraicGeometry.ChowDatum.hp_proper AlgebraicGeometry.ProjSpace.algebraAway AlgebraicGeometry.ProjSpace.instIsProperProdOverπ AlgebraicGeometry.ChowDatumProj.hp_isoU AlgebraicGeometry.ProjSpace.isProper_π AlgebraicGeometry.ProjSpace.finiteType_mvPolynomial ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule"
p2m_attr_erase "simp" "DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq AlgebraicGeometry.ChowDatumProj.mk.sizeOf_spec AlgebraicGeometry.ChowDatum.mk.sizeOf_spec AlgebraicGeometry.ChowDatumProj.mk.injEq AlgebraicGeometry.ChowDatum.mk.injEq ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.mk.injEq"

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry TopologicalSpace
open scoped TensorProduct

universe u

namespace W_ASM

theorem algebraMap_smul_eq_app_appLE_smul
    {P V' Y : Scheme.{u}} (p' : V' ⟶ P) (W : P.affineOpens)
    (R : Type u) [CommRing R] [Algebra Γ(P, W.1) R]
    (sY : Y ⟶ Spec (CommRingCat.of R)) (t : Y ⟶ V')
    (hY : IsPullback t sY p' (Spec.map (CommRingCat.ofHom (algebraMap Γ(P, W.1) R)) ≫ W.2.fromSpec))
    (G : OModulePresheaf sY) (V : V'.Opens) (h : V ≤ p' ⁻¹ᵁ W.1) (a : Γ(P, W.1)) (y : G.obj (t ⁻¹ᵁ V)) :
    algebraMap Γ(P, W.1) R a • y = (t.app V).hom ((p'.appLE W.1 V h).hom a) • y := by
  letI inst := Scheme.TwoAffineOpenCover.algebraOfHom sY (t ⁻¹ᵁ V)
  rw [← IsScalarTower.algebraMap_smul Γ(Y, t ⁻¹ᵁ V) (algebraMap Γ(P, W.1) R a) y]
  congr 1

  have appLE_congr_hom : ∀ {f₁ f₂ : Y ⟶ P} (hf : f₁ = f₂) (e : t ⁻¹ᵁ V ≤ f₁ ⁻¹ᵁ W.1),
      f₁.appLE W.1 (t ⁻¹ᵁ V) e = f₂.appLE W.1 (t ⁻¹ᵁ V) (hf ▸ e) := by
    rintro f₁ f₂ rfl e; rfl
  have e1 : t ⁻¹ᵁ V ≤ (t ≫ p') ⁻¹ᵁ W.1 := (Opens.map t.base).monotone h
  have e4 : (⊤ : (Spec (P.presheaf.obj (Opposite.op W.1))).Opens) ≤ W.2.fromSpec ⁻¹ᵁ W.1 :=
    (W.2.fromSpec_preimage_self).symm.le
  have e3 : (⊤ : (Spec (CommRingCat.of R)).Opens)
      ≤ (Spec.map (CommRingCat.ofHom (algebraMap Γ(P, W.1) R)) ≫ W.2.fromSpec) ⁻¹ᵁ W.1 := by
    intro x _; exact e4 (Set.mem_univ _)

  have hR : p'.appLE W.1 V h ≫ t.app V
      = W.2.fromSpec.appLE W.1 ⊤ e4
        ≫ (Spec.map (CommRingCat.ofHom (algebraMap Γ(P, W.1) R))).appTop
        ≫ sY.appLE ⊤ (t ⁻¹ᵁ V) le_top := by
    rw [Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_comp_appLE, appLE_congr_hom hY.w,
      ← Scheme.Hom.appLE_comp_appLE sY _ W.1 ⊤ (t ⁻¹ᵁ V) e3 le_top,
      ← Scheme.Hom.appLE_comp_appLE (Spec.map (CommRingCat.ofHom (algebraMap Γ(P, W.1) R))) W.2.fromSpec
        W.1 ⊤ ⊤ e4 le_top]
    rfl

  have hF : W.2.fromSpec.appLE W.1 ⊤ e4 = (Scheme.ΓSpecIso (P.presheaf.obj (Opposite.op W.1))).inv := by
    rw [Scheme.Hom.appLE, IsAffineOpen.fromSpec_app_of_le W.2 W.1 le_rfl, Category.assoc, Category.assoc,
      ← Functor.map_comp]
    have h1 : (homOfLE (le_refl W.1)).op = 𝟙 _ := Subsingleton.elim _ _
    rw [h1, CategoryTheory.Functor.map_id, Category.id_comp]
    have h2 : ((homOfLE (le_top : W.2.fromSpec ⁻¹ᵁ W.1 ≤ ⊤)).op ≫ (homOfLE e4).op) = 𝟙 _ := Subsingleton.elim _ _
    rw [h2, CategoryTheory.Functor.map_id, Category.comp_id]

  change (sY.appLE ⊤ (t ⁻¹ᵁ V) le_top).hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom
      ((CommRingCat.ofHom (algebraMap Γ(P, W.1) R)).hom a)) = (p'.appLE W.1 V h ≫ t.app V).hom a
  rw [hR, hF]
  have nat := congrArg (fun f => f.hom a)
    (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap Γ(P, W.1) R)))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at nat ⊢
  rw [nat]
  rfl

theorem torsion_of_frame
    {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    {P : Scheme.{u}} (q : P ⟶ Spec (CommRingCat.of A)) [IsProper q]
    {Z : Scheme.{u}} (i : Z ⟶ P) [IsClosedImmersion i]
    {V' : Scheme.{u}} (g : V' ⟶ Z) [IsProper g] (K' : V'.OrderedAffineCover)
    (U : Z.Opens) (hU : IsIso (CategoryTheory.Limits.pullback.snd g U.ι))
    (T' : Closeds P) (hT' : ∀ z : Z, z ∉ U → i.base z ∈ T')

    (F : ℕ → OModulePresheaf q) (hFc : ∀ k, (F k).IsCoherent) (hFq : ∀ k, (F k).IsQuasicoherent)
    (φ : ∀ k, OModulePresheaf.AffHom (F (k + 1)) (F k))
    (hφs : ∀ (k : ℕ) (U : P.affineOpens), Function.Surjective ((φ k).app U))
    (hφk : ∀ (k : ℕ) (U : P.affineOpens),
      LinearMap.ker ((φ k).app U) = I ^ (k + 1) • (⊤ : Submodule A ((F (k + 1)).obj U.1)))
    (hFZ : ∀ k, OModulePresheaf.IdealAnnihilates q i.ker (F k))

    (F' : ℕ → OModulePresheaf ((g ≫ i) ≫ q)) (φ' : ∀ k, OModulePresheaf.AffHom (F' (k + 1)) (F' k))
    (η : ∀ (k : ℕ) (U₀ : P.affineOpens) (V : V'.affineOpens), V.1 ≤ (g ≫ i) ⁻¹ᵁ U₀.1 →
      ((F k).obj U₀.1 →ₗ[A] (F' k).obj V.1))
    (hηs : ∀ (k : ℕ) (U₀ : P.affineOpens) (V : V'.affineOpens) (h : V.1 ≤ (g ≫ i) ⁻¹ᵁ U₀.1) (a : Γ(P, U₀.1))
      (x : (F k).obj U₀.1), η k U₀ V h (a • x) = ((g ≫ i).appLE U₀.1 V.1 h).hom a • η k U₀ V h x)
    (hηV : ∀ (k : ℕ) (U₀ : P.affineOpens) (V₁ V₂ : V'.affineOpens) (h₁ : V₁.1 ≤ (g ≫ i) ⁻¹ᵁ U₀.1)
      (h₂ : V₂.1 ≤ (g ≫ i) ⁻¹ᵁ U₀.1) (hV : V₁.1 ≤ V₂.1) (x : (F k).obj U₀.1),
      (F' k).res hV (η k U₀ V₂ h₂ x) = η k U₀ V₁ h₁ x)
    (hηU : ∀ (k : ℕ) (U₁ U₂ : P.affineOpens) (V : V'.affineOpens) (h₁ : V.1 ≤ (g ≫ i) ⁻¹ᵁ U₁.1)
      (h₂ : V.1 ≤ (g ≫ i) ⁻¹ᵁ U₂.1) (hU₁₂ : U₁.1 ≤ U₂.1) (x : (F k).obj U₂.1),
      η k U₂ V h₂ x = η k U₁ V h₁ ((F k).res hU₁₂ x))
    (hηφ : ∀ (k : ℕ) (U₀ : P.affineOpens) (V : V'.affineOpens) (h : V.1 ≤ (g ≫ i) ⁻¹ᵁ U₀.1)
      (x : (F (k + 1)).obj U₀.1), (φ' k).app V (η (k + 1) U₀ V h x) = η k U₀ V h ((φ k).app U₀ x))
    (hβ : ∀ (k : ℕ) (U₀ : P.affineOpens) (V : V'.affineOpens) (h : V.1 ≤ (g ≫ i) ⁻¹ᵁ U₀.1),
      letI := ((g ≫ i).appLE U₀.1 V.1 h).hom.toAlgebra
      ∃ β : Γ(V', V.1) ⊗[Γ(P, U₀.1)] (F k).obj U₀.1 ≃ₗ[Γ(V', V.1)] (F' k).obj V.1,
        ∀ x : (F k).obj U₀.1, β (1 ⊗ₜ x) = η k U₀ V h x)

    (v : ∀ k, OModulePresheaf.AffHom (F k) (OModulePresheaf.cechPushforward (g ≫ i) q K' (F' k)))
    (hvη : ∀ (k : ℕ) (U₀ : P.affineOpens) (x : (F k).obj U₀.1) (j : K'.ι),
      ((v k).app U₀ x).1 j
        = η k U₀ (OModulePresheaf.AffHom.affineChart (g ≫ i) q K' U₀ j)
            (OModulePresheaf.cechPushforward.chart_le_preimage (g ≫ i) K' U₀.1 j) x)

    (W : P.affineOpens)
    (R : Type u) [CommRing R] [Algebra Γ(P, W.1) R]
    (L : Type u) [AddCommGroup L] [Module Γ(P, W.1) L] [Module R L] [IsScalarTower Γ(P, W.1) R L]
    [Module.Finite R L]
    (pr : ∀ n : ℕ, L →ₗ[Γ(P, W.1)] (F n).obj W.1)
    (hprc : ∀ (n : ℕ) (x : L), (φ n).app W (pr (n + 1) x) = pr n x)
    (hpri : ∀ x : L, (∀ n : ℕ, pr n x = 0) → x = 0)
    (hprs : ∀ n : ℕ, Function.Surjective (pr n))
    (hprk : ∀ n : ℕ, LinearMap.ker (pr n) = (I.map ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ q.appLE ⊤ W.1 le_top).hom) ^ (n + 1) • (⊤ : Submodule Γ(P, W.1) L))
    [IsNoetherianRing R] (hRc : IsAdicComplete (I.map ((algebraMap Γ(P, W.1) R).comp ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ q.appLE ⊤ W.1 le_top).hom)) R)

    {Y : Scheme.{u}} (sY : Y ⟶ Spec (CommRingCat.of R)) [IsProper sY] (t : Y ⟶ V')
    (hY : IsPullback t sY (g ≫ i) (Spec.map (CommRingCat.ofHom (algebraMap Γ(P, W.1) R)) ≫ W.2.fromSpec))
    (hta : ∀ V : V'.affineOpens, V.1 ≤ (g ≫ i) ⁻¹ᵁ W.1 → IsAffineOpen (t ⁻¹ᵁ V.1))

    (G : OModulePresheaf sY) (hGc : G.IsCoherent) (hGq : G.IsQuasicoherent)
    (ε : ∀ U : Y.Opens, L →ₗ[R] G.obj U)
    (hεr : ∀ (U U' : Y.Opens) (h : U ≤ U') (x : L), G.res h (ε U' x) = ε U x)
    (hεβ : ∀ U : Y.affineOpens,
      letI := Scheme.TwoAffineOpenCover.algebraOfHom sY U.1
      ∃ β : Γ(Y, U.1) ⊗[R] L ≃ₗ[Γ(Y, U.1)] G.obj U.1, ∀ x : L, β (1 ⊗ₜ x) = ε U.1 x)

    (θ : ∀ (n : ℕ) (V : V'.affineOpens), V.1 ≤ (g ≫ i) ⁻¹ᵁ W.1 → (G.obj (t ⁻¹ᵁ V.1) →+ (F' n).obj V.1))
    (hθs : ∀ (n : ℕ) (V : V'.affineOpens) (h : V.1 ≤ (g ≫ i) ⁻¹ᵁ W.1) (c : Γ(V', V.1))
      (y : G.obj (t ⁻¹ᵁ V.1)), θ n V h ((t.app V.1).hom c • y) = c • θ n V h y)
    (hθr : ∀ (n : ℕ) (V₁ V₂ : V'.affineOpens) (h₁ : V₁.1 ≤ (g ≫ i) ⁻¹ᵁ W.1) (h₂ : V₂.1 ≤ (g ≫ i) ⁻¹ᵁ W.1)
      (hV : V₁.1 ≤ V₂.1) (y : G.obj (t ⁻¹ᵁ V₂.1)),
      (F' n).res hV (θ n V₂ h₂ y) = θ n V₁ h₁ (G.res ((Opens.map t.base).monotone hV) y))
    (hθφ : ∀ (n : ℕ) (V : V'.affineOpens) (h : V.1 ≤ (g ≫ i) ⁻¹ᵁ W.1) (y : G.obj (t ⁻¹ᵁ V.1)),
      (φ' n).app V (θ (n + 1) V h y) = θ n V h y)
    (hθε : ∀ (n : ℕ) (V : V'.affineOpens) (h : V.1 ≤ (g ≫ i) ⁻¹ᵁ W.1) (x : L),
      θ n V h (ε (t ⁻¹ᵁ V.1) x) = η n W V h (pr n x))
    (hθo : ∀ (n : ℕ) (V : V'.affineOpens) (h : V.1 ≤ (g ≫ i) ⁻¹ᵁ W.1), Function.Surjective (θ n V h))
    (hθk : ∀ (n : ℕ) (V : V'.affineOpens) (h : V.1 ≤ (g ≫ i) ⁻¹ᵁ W.1) (y : G.obj (t ⁻¹ᵁ V.1)),
      θ n V h y = 0 ↔ y ∈ (I.map ((algebraMap Γ(P, W.1) R).comp ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ q.appLE ⊤ W.1 le_top).hom)) ^ (n + 1) • (⊤ : Submodule R (G.obj (t ⁻¹ᵁ V.1)))) :
    ∃ N : ℕ,
      (∀ x : L, (∀ j : K'.ι, ε (t ⁻¹ᵁ (OModulePresheaf.cechPushforward.chart (g ≫ i) K' W.1 j)) x = 0) →
        ∀ a ∈ (Scheme.IdealSheafData.vanishingIdeal T').ideal W ^ N, a • x = 0) ∧
      (∀ c : ∀ j : K'.ι, G.obj (t ⁻¹ᵁ (OModulePresheaf.cechPushforward.chart (g ≫ i) K' W.1 j)),
        (∀ j j' : K'.ι,
          G.res ((Opens.map t.base).monotone (inf_le_left : (OModulePresheaf.cechPushforward.chart (g ≫ i) K' W.1 j) ⊓ (OModulePresheaf.cechPushforward.chart (g ≫ i) K' W.1 j') ≤ _)) (c j)
            = G.res ((Opens.map t.base).monotone (inf_le_right : (OModulePresheaf.cechPushforward.chart (g ≫ i) K' W.1 j) ⊓ (OModulePresheaf.cechPushforward.chart (g ≫ i) K' W.1 j') ≤ _)) (c j')) →
        ∀ a ∈ (Scheme.IdealSheafData.vanishingIdeal T').ideal W ^ N,
          ∃ x : L, ∀ j : K'.ι, ε (t ⁻¹ᵁ (OModulePresheaf.cechPushforward.chart (g ≫ i) K' W.1 j)) x = algebraMap Γ(P, W.1) R a • c j) := by
  classical
  obtain ⟨-, -, h4c⟩ :=
    AlgebraicGeometry.OModulePresheaf.exists_forall_eq_thread_and_eq_zero_of_forall_eq_zero_of_isAdicComplete_of_isProper
      I q i g K' U hU T' hT' F hFc hFq φ hφs hφk hFZ F' φ' η hηs hηV hηU hηφ hβ v hvη W R L pr hprc hpri hprs hprk hRc sY t hY hta G hGc hGq ε hεr hεβ θ hθs hθr hθφ hθε hθo hθk
  have h5 :=
    AlgebraicGeometry.OModulePresheaf.exists_pow_smul_eq_zero_and_exists_eq_pow_smul_of_mem_vanishingIdeal_of_isIso_pullback_snd
      I q i g K' U hU T' hT' F hFc hFq φ hφs hφk hFZ F' φ' η hηs hηV hηU hηφ hβ v hvη W R L pr hprc hpri hprs hprk sY t hY hta G hGc hGq ε hεr hεβ

  let D : (∀ j : K'.ι, G.obj (t ⁻¹ᵁ (OModulePresheaf.cechPushforward.chart (g ≫ i) K' W.1 j))) →ₗ[R]
      (∀ p : K'.ι × K'.ι, G.obj (t ⁻¹ᵁ ((OModulePresheaf.cechPushforward.chart (g ≫ i) K' W.1 p.1) ⊓ (OModulePresheaf.cechPushforward.chart (g ≫ i) K' W.1 p.2)))) :=
    LinearMap.pi fun p =>
      (G.res ((Opens.map t.base).monotone (inf_le_left : (OModulePresheaf.cechPushforward.chart (g ≫ i) K' W.1 p.1) ⊓ (OModulePresheaf.cechPushforward.chart (g ≫ i) K' W.1 p.2) ≤ _))).comp
          (LinearMap.proj p.1) -
        (G.res ((Opens.map t.base).monotone (inf_le_right : (OModulePresheaf.cechPushforward.chart (g ≫ i) K' W.1 p.1) ⊓ (OModulePresheaf.cechPushforward.chart (g ≫ i) K' W.1 p.2) ≤ _))).comp
          (LinearMap.proj p.2)
  let H : Submodule R (∀ j : K'.ι, G.obj (t ⁻¹ᵁ (OModulePresheaf.cechPushforward.chart (g ≫ i) K' W.1 j))) := LinearMap.ker D
  have memH : ∀ c : ∀ j : K'.ι, G.obj (t ⁻¹ᵁ (OModulePresheaf.cechPushforward.chart (g ≫ i) K' W.1 j)), c ∈ H ↔ (∀ j j' : K'.ι,
          G.res ((Opens.map t.base).monotone (inf_le_left : (OModulePresheaf.cechPushforward.chart (g ≫ i) K' W.1 j) ⊓ (OModulePresheaf.cechPushforward.chart (g ≫ i) K' W.1 j') ≤ _)) (c j)
            = G.res ((Opens.map t.base).monotone (inf_le_right : (OModulePresheaf.cechPushforward.chart (g ≫ i) K' W.1 j) ⊓ (OModulePresheaf.cechPushforward.chart (g ≫ i) K' W.1 j') ≤ _)) (c j')) := by
    intro c
    simp only [H, D, LinearMap.mem_ker, funext_iff, LinearMap.pi_apply, LinearMap.sub_apply, LinearMap.comp_apply,
      LinearMap.proj_apply, Pi.zero_apply, sub_eq_zero, Prod.forall]

  let u0 : L →ₗ[R] (∀ j : K'.ι, G.obj (t ⁻¹ᵁ (OModulePresheaf.cechPushforward.chart (g ≫ i) K' W.1 j))) := LinearMap.pi fun j => ε (t ⁻¹ᵁ (OModulePresheaf.cechPushforward.chart (g ≫ i) K' W.1 j))
  have hu0 : ∀ x : L, u0 x ∈ H := fun x => (memH _).2 fun j j' => by
    simp only [u0, LinearMap.pi_apply]
    rw [hεr, hεr]
  let uu : L →ₗ[R] H := LinearMap.codRestrict H u0 hu0
  have huu : ∀ (x : L) (j : K'.ι), ((uu x : H) : ∀ j : K'.ι, G.obj (t ⁻¹ᵁ (OModulePresheaf.cechPushforward.chart (g ≫ i) K' W.1 j))) j = ε (t ⁻¹ᵁ (OModulePresheaf.cechPushforward.chart (g ≫ i) K' W.1 j)) x :=
    fun x j => rfl

  haveI : IsNoetherianRing Γ(P, W.1) := by
    haveI : IsLocallyNoetherian P := LocallyOfFiniteType.isLocallyNoetherian q
    exact IsLocallyNoetherian.component_noetherian W
  obtain ⟨S0, hS0⟩ := (isNoetherianRing_iff_ideal_fg Γ(P, W.1)).mp inferInstance ((Scheme.IdealSheafData.vanishingIdeal T').ideal W)
  let S : Finset R := S0.image (algebraMap Γ(P, W.1) R)
  let J : Ideal R := ((Scheme.IdealSheafData.vanishingIdeal T').ideal W).map (algebraMap Γ(P, W.1) R)
  have hSJ : Ideal.span (S : Set R) = J := by
    simp only [S, J, Finset.coe_image]
    rw [← Ideal.map_span, hS0]
  have hS0mem : ∀ a ∈ S0, a ∈ (Scheme.IdealSheafData.vanishingIdeal T').ideal W := fun a ha => hS0 ▸ Ideal.subset_span ha

  haveI : IsNoetherian R L := isNoetherian_of_isNoetherianRing_of_finite R L
  have hkerfg : (LinearMap.ker uu).FG := IsNoetherian.noetherian _
  have hHfg : H.FG := by
    obtain ⟨s, hs1, hs2⟩ := h4c
    refine ⟨s, le_antisymm (Submodule.span_le.2 fun c hc => (memH c).2 (hs1 c hc)) fun c hc => hs2 c ((memH c).1 hc)⟩
  haveI : Module.Finite R H := Module.Finite.iff_fg.mpr hHfg
  have hcoker : Module.Finite R (H ⧸ LinearMap.range uu) := inferInstance

  have hk : ∀ a ∈ S, ∀ x : L, uu x = 0 → ∃ k : ℕ, a ^ k • x = 0 := by
    intro a ha x hx
    obtain ⟨a0, ha0, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨k, hk⟩ := (h5 a0 (hS0mem a0 ha0)).1 x fun j => by
      rw [← huu x j, hx]; rfl
    exact ⟨k, by rw [← map_pow, algebraMap_smul]; exact hk⟩
  have hc : ∀ a ∈ S, ∀ y : H, ∃ (k : ℕ) (x : L), uu x = a ^ k • y := by
    intro a ha y
    obtain ⟨a0, ha0, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨k, x, hx⟩ := (h5 a0 (hS0mem a0 ha0)).2 y.1 ((memH _).1 y.2)
    refine ⟨k, x, Subtype.ext (funext fun j => ?_)⟩
    rw [huu, hx j]
    rfl
  obtain ⟨N, hN1, hN2⟩ :=
    Module.exists_pow_smul_ker_eq_zero_and_pow_smul_le_range_of_forall_exists_pow_smul S J hSJ uu hkerfg hcoker hk hc
  have hmemJ : ∀ a ∈ (Scheme.IdealSheafData.vanishingIdeal T').ideal W ^ N, algebraMap Γ(P, W.1) R a ∈ J ^ N := fun a ha => by
    rw [← Ideal.map_pow]; exact Ideal.mem_map_of_mem _ ha
  refine ⟨N, fun x hx a ha => ?_, fun c hcc a ha => ?_⟩
  · have h1 : uu x = 0 := Subtype.ext (funext fun j => by rw [huu, hx j]; rfl)
    have := hN1 x h1 _ (hmemJ a ha)
    rwa [algebraMap_smul] at this
  · obtain ⟨x, hx⟩ := hN2 ⟨c, (memH c).2 hcc⟩ _ (hmemJ a ha)
    exact ⟨x, fun j => by rw [← huu x j, hx]; rfl⟩

theorem threads_of_torsion
    {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    {P : Scheme.{u}} (q : P ⟶ Spec (CommRingCat.of A)) [IsProper q]
    {Z : Scheme.{u}} (i : Z ⟶ P) [IsClosedImmersion i]
    {V' : Scheme.{u}} (g : V' ⟶ Z) [IsProper g] (K' : V'.OrderedAffineCover)
    (U : Z.Opens) (hU : IsIso (CategoryTheory.Limits.pullback.snd g U.ι))
    (T' : Closeds P) (hT' : ∀ z : Z, z ∉ U → i.base z ∈ T')

    (F : ℕ → OModulePresheaf q) (hFc : ∀ k, (F k).IsCoherent) (hFq : ∀ k, (F k).IsQuasicoherent)
    (φ : ∀ k, OModulePresheaf.AffHom (F (k + 1)) (F k))
    (hφs : ∀ (k : ℕ) (U : P.affineOpens), Function.Surjective ((φ k).app U))
    (hφk : ∀ (k : ℕ) (U : P.affineOpens),
      LinearMap.ker ((φ k).app U) = I ^ (k + 1) • (⊤ : Submodule A ((F (k + 1)).obj U.1)))
    (hFZ : ∀ k, OModulePresheaf.IdealAnnihilates q i.ker (F k))

    (F' : ℕ → OModulePresheaf ((g ≫ i) ≫ q)) (φ' : ∀ k, OModulePresheaf.AffHom (F' (k + 1)) (F' k))
    (η : ∀ (k : ℕ) (U₀ : P.affineOpens) (V : V'.affineOpens), V.1 ≤ (g ≫ i) ⁻¹ᵁ U₀.1 →
      ((F k).obj U₀.1 →ₗ[A] (F' k).obj V.1))
    (hηs : ∀ (k : ℕ) (U₀ : P.affineOpens) (V : V'.affineOpens) (h : V.1 ≤ (g ≫ i) ⁻¹ᵁ U₀.1) (a : Γ(P, U₀.1))
      (x : (F k).obj U₀.1), η k U₀ V h (a • x) = ((g ≫ i).appLE U₀.1 V.1 h).hom a • η k U₀ V h x)
    (hηV : ∀ (k : ℕ) (U₀ : P.affineOpens) (V₁ V₂ : V'.affineOpens) (h₁ : V₁.1 ≤ (g ≫ i) ⁻¹ᵁ U₀.1)
      (h₂ : V₂.1 ≤ (g ≫ i) ⁻¹ᵁ U₀.1) (hV : V₁.1 ≤ V₂.1) (x : (F k).obj U₀.1),
      (F' k).res hV (η k U₀ V₂ h₂ x) = η k U₀ V₁ h₁ x)
    (hηU : ∀ (k : ℕ) (U₁ U₂ : P.affineOpens) (V : V'.affineOpens) (h₁ : V.1 ≤ (g ≫ i) ⁻¹ᵁ U₁.1)
      (h₂ : V.1 ≤ (g ≫ i) ⁻¹ᵁ U₂.1) (hU₁₂ : U₁.1 ≤ U₂.1) (x : (F k).obj U₂.1),
      η k U₂ V h₂ x = η k U₁ V h₁ ((F k).res hU₁₂ x))
    (hηφ : ∀ (k : ℕ) (U₀ : P.affineOpens) (V : V'.affineOpens) (h : V.1 ≤ (g ≫ i) ⁻¹ᵁ U₀.1)
      (x : (F (k + 1)).obj U₀.1), (φ' k).app V (η (k + 1) U₀ V h x) = η k U₀ V h ((φ k).app U₀ x))
    (hβ : ∀ (k : ℕ) (U₀ : P.affineOpens) (V : V'.affineOpens) (h : V.1 ≤ (g ≫ i) ⁻¹ᵁ U₀.1),
      letI := ((g ≫ i).appLE U₀.1 V.1 h).hom.toAlgebra
      ∃ β : Γ(V', V.1) ⊗[Γ(P, U₀.1)] (F k).obj U₀.1 ≃ₗ[Γ(V', V.1)] (F' k).obj V.1,
        ∀ x : (F k).obj U₀.1, β (1 ⊗ₜ x) = η k U₀ V h x)

    (v : ∀ k, OModulePresheaf.AffHom (F k) (OModulePresheaf.cechPushforward (g ≫ i) q K' (F' k)))
    (hvη : ∀ (k : ℕ) (U₀ : P.affineOpens) (x : (F k).obj U₀.1) (j : K'.ι),
      ((v k).app U₀ x).1 j
        = η k U₀ (OModulePresheaf.AffHom.affineChart (g ≫ i) q K' U₀ j)
            (OModulePresheaf.cechPushforward.chart_le_preimage (g ≫ i) K' U₀.1 j) x)

    (W : P.affineOpens)
    (R : Type u) [CommRing R] [Algebra Γ(P, W.1) R]
    (L : Type u) [AddCommGroup L] [Module Γ(P, W.1) L] [Module R L] [IsScalarTower Γ(P, W.1) R L]
    [Module.Finite R L]
    (pr : ∀ n : ℕ, L →ₗ[Γ(P, W.1)] (F n).obj W.1)
    (hprc : ∀ (n : ℕ) (x : L), (φ n).app W (pr (n + 1) x) = pr n x)
    (hpri : ∀ x : L, (∀ n : ℕ, pr n x = 0) → x = 0)
    (hprs : ∀ n : ℕ, Function.Surjective (pr n))
    (hprk : ∀ n : ℕ, LinearMap.ker (pr n) = (I.map ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ q.appLE ⊤ W.1 le_top).hom) ^ (n + 1) • (⊤ : Submodule Γ(P, W.1) L))
    (hprt : ∀ m : ∀ n : ℕ, (F n).obj W.1, (∀ n : ℕ, (φ n).app W (m (n + 1)) = m n) → ∃ x : L, ∀ n : ℕ, pr n x = m n)
    [IsNoetherianRing R] (hRc : IsAdicComplete (I.map ((algebraMap Γ(P, W.1) R).comp ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ q.appLE ⊤ W.1 le_top).hom)) R)

    {Y : Scheme.{u}} (sY : Y ⟶ Spec (CommRingCat.of R)) [IsProper sY] (t : Y ⟶ V')
    (hY : IsPullback t sY (g ≫ i) (Spec.map (CommRingCat.ofHom (algebraMap Γ(P, W.1) R)) ≫ W.2.fromSpec))
    (hta : ∀ V : V'.affineOpens, V.1 ≤ (g ≫ i) ⁻¹ᵁ W.1 → IsAffineOpen (t ⁻¹ᵁ V.1))

    (G : OModulePresheaf sY) (hGc : G.IsCoherent) (hGq : G.IsQuasicoherent)
    (ε : ∀ U : Y.Opens, L →ₗ[R] G.obj U)
    (hεr : ∀ (U U' : Y.Opens) (h : U ≤ U') (x : L), G.res h (ε U' x) = ε U x)
    (hεβ : ∀ U : Y.affineOpens,
      letI := Scheme.TwoAffineOpenCover.algebraOfHom sY U.1
      ∃ β : Γ(Y, U.1) ⊗[R] L ≃ₗ[Γ(Y, U.1)] G.obj U.1, ∀ x : L, β (1 ⊗ₜ x) = ε U.1 x)

    (θ : ∀ (n : ℕ) (V : V'.affineOpens), V.1 ≤ (g ≫ i) ⁻¹ᵁ W.1 → (G.obj (t ⁻¹ᵁ V.1) →+ (F' n).obj V.1))
    (hθs : ∀ (n : ℕ) (V : V'.affineOpens) (h : V.1 ≤ (g ≫ i) ⁻¹ᵁ W.1) (c : Γ(V', V.1))
      (y : G.obj (t ⁻¹ᵁ V.1)), θ n V h ((t.app V.1).hom c • y) = c • θ n V h y)
    (hθr : ∀ (n : ℕ) (V₁ V₂ : V'.affineOpens) (h₁ : V₁.1 ≤ (g ≫ i) ⁻¹ᵁ W.1) (h₂ : V₂.1 ≤ (g ≫ i) ⁻¹ᵁ W.1)
      (hV : V₁.1 ≤ V₂.1) (y : G.obj (t ⁻¹ᵁ V₂.1)),
      (F' n).res hV (θ n V₂ h₂ y) = θ n V₁ h₁ (G.res ((Opens.map t.base).monotone hV) y))
    (hθφ : ∀ (n : ℕ) (V : V'.affineOpens) (h : V.1 ≤ (g ≫ i) ⁻¹ᵁ W.1) (y : G.obj (t ⁻¹ᵁ V.1)),
      (φ' n).app V (θ (n + 1) V h y) = θ n V h y)
    (hθε : ∀ (n : ℕ) (V : V'.affineOpens) (h : V.1 ≤ (g ≫ i) ⁻¹ᵁ W.1) (x : L),
      θ n V h (ε (t ⁻¹ᵁ V.1) x) = η n W V h (pr n x))
    (hθo : ∀ (n : ℕ) (V : V'.affineOpens) (h : V.1 ≤ (g ≫ i) ⁻¹ᵁ W.1), Function.Surjective (θ n V h))
    (hθk : ∀ (n : ℕ) (V : V'.affineOpens) (h : V.1 ≤ (g ≫ i) ⁻¹ᵁ W.1) (y : G.obj (t ⁻¹ᵁ V.1)),
      θ n V h y = 0 ↔ y ∈ (I.map ((algebraMap Γ(P, W.1) R).comp ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ q.appLE ⊤ W.1 le_top).hom)) ^ (n + 1) • (⊤ : Submodule R (G.obj (t ⁻¹ᵁ V.1))))
    (N : ℕ)
    (hk : ∀ x : L, (∀ j : K'.ι, ε (t ⁻¹ᵁ (OModulePresheaf.cechPushforward.chart (g ≫ i) K' W.1 j)) x = 0) →
        ∀ a ∈ (Scheme.IdealSheafData.vanishingIdeal T').ideal W ^ N, a • x = 0)
    (hc : ∀ c : ∀ j : K'.ι, G.obj (t ⁻¹ᵁ (OModulePresheaf.cechPushforward.chart (g ≫ i) K' W.1 j)),
        (∀ j j' : K'.ι,
          G.res ((Opens.map t.base).monotone (inf_le_left : (OModulePresheaf.cechPushforward.chart (g ≫ i) K' W.1 j) ⊓ (OModulePresheaf.cechPushforward.chart (g ≫ i) K' W.1 j') ≤ _)) (c j)
            = G.res ((Opens.map t.base).monotone (inf_le_right : (OModulePresheaf.cechPushforward.chart (g ≫ i) K' W.1 j) ⊓ (OModulePresheaf.cechPushforward.chart (g ≫ i) K' W.1 j') ≤ _)) (c j')) →
        ∀ a ∈ (Scheme.IdealSheafData.vanishingIdeal T').ideal W ^ N,
          ∃ x : L, ∀ j : K'.ι, ε (t ⁻¹ᵁ (OModulePresheaf.cechPushforward.chart (g ≫ i) K' W.1 j)) x = algebraMap Γ(P, W.1) R a • c j) :
    (∀ (ℓ : ∀ n, (OModulePresheaf.cechPushforward (g ≫ i) q K' (F' n)).obj W.1),
        (∀ n, ((φ' n).cechPushforward (g ≫ i) q K').app W (ℓ (n + 1)) = ℓ n) →
        ∀ a : Γ(P, W.1), a ∈ (Scheme.IdealSheafData.vanishingIdeal T').ideal W ^ N →
          ∃ m : ∀ n, (F n).obj W.1,
            (∀ n, (φ n).app W (m (n + 1)) = m n) ∧ ∀ n, (v n).app W (m n) = a • ℓ n) ∧
      (∀ (m : ∀ n, (F n).obj W.1), (∀ n, (φ n).app W (m (n + 1)) = m n) →
        (∀ n, (v n).app W (m n) = 0) →
        ∀ a : Γ(P, W.1), a ∈ (Scheme.IdealSheafData.vanishingIdeal T').ideal W ^ N →
          ∀ n, a • m n = 0) := by
  classical
  obtain ⟨h4a, h4b, -⟩ :=
    AlgebraicGeometry.OModulePresheaf.exists_forall_eq_thread_and_eq_zero_of_forall_eq_zero_of_isAdicComplete_of_isProper
      I q i g K' U hU T' hT' F hFc hFq φ hφs hφk hFZ F' φ' η hηs hηV hηU hηφ hβ v hvη W R L pr hprc hpri hprs hprk hRc sY t hY hta G hGc hGq ε hεr hεβ θ hθs hθr hθφ hθε hθo hθk

  have hvθ : ∀ (n : ℕ) (x : L) (j : K'.ι),
      ((v n).app W (pr n x)).1 j
        = θ n (OModulePresheaf.AffHom.affineChart (g ≫ i) q K' W j)
            (OModulePresheaf.cechPushforward.chart_le_preimage (g ≫ i) K' W.1 j)
            (ε (t ⁻¹ᵁ (OModulePresheaf.cechPushforward.chart (g ≫ i) K' W.1 j)) x) := by
    intro n x j
    rw [hvη, hθε]
  refine ⟨?_, ?_⟩
  ·
    intro ℓ hℓ a ha
    obtain ⟨c, hcc, hcθ⟩ := h4a ℓ hℓ
    obtain ⟨x, hx⟩ := hc c hcc a ha
    refine ⟨fun n => pr n x, fun n => hprc n x, fun n => ?_⟩
    apply OModulePresheaf.cechPushforward.ext
    intro j
    rw [hvθ, hx j, OModulePresheaf.cechPushforward.coe_sectionsSMul, ← hcθ n j,
      algebraMap_smul_eq_app_appLE_smul (g ≫ i) W R sY t hY G _
        (OModulePresheaf.cechPushforward.chart_le_preimage (g ≫ i) K' W.1 j) a (c j),
      hθs]
  ·
    intro m hm hv0 a ha n
    obtain ⟨x, hx⟩ := hprt m hm
    have hcc : (∀ j j' : K'.ι,
          G.res ((Opens.map t.base).monotone (inf_le_left : (OModulePresheaf.cechPushforward.chart (g ≫ i) K' W.1 j) ⊓ (OModulePresheaf.cechPushforward.chart (g ≫ i) K' W.1 j') ≤ _)) ((fun j => ε (t ⁻¹ᵁ (OModulePresheaf.cechPushforward.chart (g ≫ i) K' W.1 j)) x) j)
            = G.res ((Opens.map t.base).monotone (inf_le_right : (OModulePresheaf.cechPushforward.chart (g ≫ i) K' W.1 j) ⊓ (OModulePresheaf.cechPushforward.chart (g ≫ i) K' W.1 j') ≤ _)) ((fun j => ε (t ⁻¹ᵁ (OModulePresheaf.cechPushforward.chart (g ≫ i) K' W.1 j)) x) j')) := fun j j' => by
      simp only []
      rw [hεr, hεr]
    have hzero := h4b (fun j => ε (t ⁻¹ᵁ (OModulePresheaf.cechPushforward.chart (g ≫ i) K' W.1 j)) x) hcc fun n j => by
      simp only []
      rw [← hvθ, hx n, hv0 n]
      rfl
    have hux : ∀ j : K'.ι, ε (t ⁻¹ᵁ (OModulePresheaf.cechPushforward.chart (g ≫ i) K' W.1 j)) x = 0 := fun j => congr_fun hzero j
    have hax : a • x = 0 := hk x hux a ha
    rw [← hx n, ← map_smul, hax, map_zero]

theorem exists_frame
    {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    {P : Scheme.{u}} (q : P ⟶ Spec (CommRingCat.of A)) [IsProper q]
    {Z : Scheme.{u}} (i : Z ⟶ P) [IsClosedImmersion i]
    {V' : Scheme.{u}} (g : V' ⟶ Z) [IsProper g] (K' : V'.OrderedAffineCover)
    (U : Z.Opens) (hU : IsIso (CategoryTheory.Limits.pullback.snd g U.ι))
    (T' : Closeds P) (hT' : ∀ z : Z, z ∉ U → i.base z ∈ T')

    (F : ℕ → OModulePresheaf q) (hFc : ∀ k, (F k).IsCoherent) (hFq : ∀ k, (F k).IsQuasicoherent)
    (φ : ∀ k, OModulePresheaf.AffHom (F (k + 1)) (F k))
    (hφs : ∀ (k : ℕ) (U : P.affineOpens), Function.Surjective ((φ k).app U))
    (hφk : ∀ (k : ℕ) (U : P.affineOpens),
      LinearMap.ker ((φ k).app U) = I ^ (k + 1) • (⊤ : Submodule A ((F (k + 1)).obj U.1)))
    (hFZ : ∀ k, OModulePresheaf.IdealAnnihilates q i.ker (F k))

    (F' : ℕ → OModulePresheaf ((g ≫ i) ≫ q)) (φ' : ∀ k, OModulePresheaf.AffHom (F' (k + 1)) (F' k))
    (η : ∀ (k : ℕ) (U₀ : P.affineOpens) (V : V'.affineOpens), V.1 ≤ (g ≫ i) ⁻¹ᵁ U₀.1 →
      ((F k).obj U₀.1 →ₗ[A] (F' k).obj V.1))
    (hηs : ∀ (k : ℕ) (U₀ : P.affineOpens) (V : V'.affineOpens) (h : V.1 ≤ (g ≫ i) ⁻¹ᵁ U₀.1) (a : Γ(P, U₀.1))
      (x : (F k).obj U₀.1), η k U₀ V h (a • x) = ((g ≫ i).appLE U₀.1 V.1 h).hom a • η k U₀ V h x)
    (hηV : ∀ (k : ℕ) (U₀ : P.affineOpens) (V₁ V₂ : V'.affineOpens) (h₁ : V₁.1 ≤ (g ≫ i) ⁻¹ᵁ U₀.1)
      (h₂ : V₂.1 ≤ (g ≫ i) ⁻¹ᵁ U₀.1) (hV : V₁.1 ≤ V₂.1) (x : (F k).obj U₀.1),
      (F' k).res hV (η k U₀ V₂ h₂ x) = η k U₀ V₁ h₁ x)
    (hηU : ∀ (k : ℕ) (U₁ U₂ : P.affineOpens) (V : V'.affineOpens) (h₁ : V.1 ≤ (g ≫ i) ⁻¹ᵁ U₁.1)
      (h₂ : V.1 ≤ (g ≫ i) ⁻¹ᵁ U₂.1) (hU₁₂ : U₁.1 ≤ U₂.1) (x : (F k).obj U₂.1),
      η k U₂ V h₂ x = η k U₁ V h₁ ((F k).res hU₁₂ x))
    (hηφ : ∀ (k : ℕ) (U₀ : P.affineOpens) (V : V'.affineOpens) (h : V.1 ≤ (g ≫ i) ⁻¹ᵁ U₀.1)
      (x : (F (k + 1)).obj U₀.1), (φ' k).app V (η (k + 1) U₀ V h x) = η k U₀ V h ((φ k).app U₀ x))
    (hβ : ∀ (k : ℕ) (U₀ : P.affineOpens) (V : V'.affineOpens) (h : V.1 ≤ (g ≫ i) ⁻¹ᵁ U₀.1),
      letI := ((g ≫ i).appLE U₀.1 V.1 h).hom.toAlgebra
      ∃ β : Γ(V', V.1) ⊗[Γ(P, U₀.1)] (F k).obj U₀.1 ≃ₗ[Γ(V', V.1)] (F' k).obj V.1,
        ∀ x : (F k).obj U₀.1, β (1 ⊗ₜ x) = η k U₀ V h x)

    (v : ∀ k, OModulePresheaf.AffHom (F k) (OModulePresheaf.cechPushforward (g ≫ i) q K' (F' k)))
    (hvη : ∀ (k : ℕ) (U₀ : P.affineOpens) (x : (F k).obj U₀.1) (j : K'.ι),
      ((v k).app U₀ x).1 j
        = η k U₀ (OModulePresheaf.AffHom.affineChart (g ≫ i) q K' U₀ j)
            (OModulePresheaf.cechPushforward.chart_le_preimage (g ≫ i) K' U₀.1 j) x)
    (W : P.affineOpens) (J : Ideal Γ(P, W.1)) (hJ : J = (I.map ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ q.appLE ⊤ W.1 le_top).hom)) :
    ∃ (L : Type u) (_ : AddCommGroup L) (_ : Module Γ(P, W.1) L) (_ : Module (AdicCompletion J Γ(P, W.1)) L)
      (_ : IsScalarTower Γ(P, W.1) (AdicCompletion J Γ(P, W.1)) L) (_ : Module.Finite (AdicCompletion J Γ(P, W.1)) L)
      (pr : ∀ n : ℕ, L →ₗ[Γ(P, W.1)] (F n).obj W.1),
      (∀ (n : ℕ) (x : L), (φ n).app W (pr (n + 1) x) = pr n x) ∧
      (∀ x : L, (∀ n : ℕ, pr n x = 0) → x = 0) ∧
      (∀ m : ∀ n : ℕ, (F n).obj W.1, (∀ n : ℕ, (φ n).app W (m (n + 1)) = m n) → ∃ x : L, ∀ n : ℕ, pr n x = m n) ∧
      (∀ n : ℕ, Function.Surjective (pr n)) ∧
      (∀ n : ℕ, LinearMap.ker (pr n) = (I.map ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ q.appLE ⊤ W.1 le_top).hom) ^ (n + 1) • (⊤ : Submodule Γ(P, W.1) L)) ∧
      IsAdicComplete (I.map ((algebraMap Γ(P, W.1) (AdicCompletion J Γ(P, W.1))).comp ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ q.appLE ⊤ W.1 le_top).hom)) (AdicCompletion J Γ(P, W.1)) ∧
    ∃ (Y : Scheme.{u}) (sY : Y ⟶ Spec (CommRingCat.of (AdicCompletion J Γ(P, W.1)))) (_ : IsProper sY) (t : Y ⟶ V'),
      IsPullback t sY (g ≫ i) (Spec.map (CommRingCat.ofHom (algebraMap Γ(P, W.1) (AdicCompletion J Γ(P, W.1)))) ≫ W.2.fromSpec) ∧
      (∀ V : V'.affineOpens, V.1 ≤ (g ≫ i) ⁻¹ᵁ W.1 → IsAffineOpen (t ⁻¹ᵁ V.1)) ∧
      ∃ (G : OModulePresheaf sY) (ε : ∀ U : Y.Opens, L →ₗ[(AdicCompletion J Γ(P, W.1))] G.obj U)
        (θ : ∀ (n : ℕ) (V : V'.affineOpens), V.1 ≤ (g ≫ i) ⁻¹ᵁ W.1 → (G.obj (t ⁻¹ᵁ V.1) →+ (F' n).obj V.1)),
        G.IsCoherent ∧ G.IsQuasicoherent ∧
        (∀ (U U' : Y.Opens) (h : U ≤ U') (x : L), G.res h (ε U' x) = ε U x) ∧
        (∀ U : Y.affineOpens,
          letI := Scheme.TwoAffineOpenCover.algebraOfHom sY U.1
          ∃ β : Γ(Y, U.1) ⊗[(AdicCompletion J Γ(P, W.1))] L ≃ₗ[Γ(Y, U.1)] G.obj U.1, ∀ x : L, β (1 ⊗ₜ x) = ε U.1 x) ∧
        (∀ (n : ℕ) (V : V'.affineOpens) (h : V.1 ≤ (g ≫ i) ⁻¹ᵁ W.1) (c : Γ(V', V.1))
          (y : G.obj (t ⁻¹ᵁ V.1)), θ n V h ((t.app V.1).hom c • y) = c • θ n V h y) ∧
        (∀ (n : ℕ) (V₁ V₂ : V'.affineOpens) (h₁ : V₁.1 ≤ (g ≫ i) ⁻¹ᵁ W.1) (h₂ : V₂.1 ≤ (g ≫ i) ⁻¹ᵁ W.1)
          (hV : V₁.1 ≤ V₂.1) (y : G.obj (t ⁻¹ᵁ V₂.1)),
          (F' n).res hV (θ n V₂ h₂ y) = θ n V₁ h₁ (G.res ((Opens.map t.base).monotone hV) y)) ∧
        (∀ (n : ℕ) (V : V'.affineOpens) (h : V.1 ≤ (g ≫ i) ⁻¹ᵁ W.1) (y : G.obj (t ⁻¹ᵁ V.1)),
          (φ' n).app V (θ (n + 1) V h y) = θ n V h y) ∧
        (∀ (n : ℕ) (V : V'.affineOpens) (h : V.1 ≤ (g ≫ i) ⁻¹ᵁ W.1) (x : L),
          θ n V h (ε (t ⁻¹ᵁ V.1) x) = η n W V h (pr n x)) ∧
        (∀ (n : ℕ) (V : V'.affineOpens) (h : V.1 ≤ (g ≫ i) ⁻¹ᵁ W.1), Function.Surjective (θ n V h)) ∧
        (∀ (n : ℕ) (V : V'.affineOpens) (h : V.1 ≤ (g ≫ i) ⁻¹ᵁ W.1) (y : G.obj (t ⁻¹ᵁ V.1)),
          θ n V h y = 0 ↔ y ∈ (I.map ((algebraMap Γ(P, W.1) (AdicCompletion J Γ(P, W.1))).comp ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ q.appLE ⊤ W.1 le_top).hom)) ^ (n + 1) • (⊤ : Submodule (AdicCompletion J Γ(P, W.1)) (G.obj (t ⁻¹ᵁ V.1)))) := by
  classical
  have hIfg : I.FG := (isNoetherianRing_iff_ideal_fg A).mp inferInstance I
  have hJfg : J.FG := by rw [hJ]; exact hIfg.map _

  let tB : ∀ n : ℕ, (F (n + 1)).obj W.1 →ₗ[Γ(P, W.1)] (F n).obj W.1 := fun n =>
    { toFun := fun x => (φ n).app W x
      map_add' := fun x y => map_add _ x y
      map_smul' := fun a x => by exact (φ n).app_smul W a x }
  have htB : ∀ (n : ℕ) (x : (F (n + 1)).obj W.1), tB n x = (φ n).app W x := fun n x => rfl
  have htBs : ∀ n : ℕ, Function.Surjective (tB n) := fun n => hφs n W

  have htBk : ∀ n : ℕ, LinearMap.ker (tB n) = J ^ (n + 1) • (⊤ : Submodule Γ(P, W.1) ((F (n + 1)).obj W.1)) := by
    intro n
    letI := Scheme.TwoAffineOpenCover.algebraOfHom q W.1
    have hsc : ∀ x : (F (n + 1)).obj W.1,
        x ∈ J ^ (n + 1) • (⊤ : Submodule Γ(P, W.1) ((F (n + 1)).obj W.1)) ↔
          x ∈ I ^ (n + 1) • (⊤ : Submodule A ((F (n + 1)).obj W.1)) := by
      intro x
      rw [hJ, ← Ideal.map_pow,
        show (((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ q.appLE ⊤ W.1 le_top).hom) = algebraMap A Γ(P, W.1) from rfl,
        ← Submodule.restrictScalars_mem A, Ideal.smul_restrictScalars, Submodule.restrictScalars_top]
    ext x
    rw [LinearMap.mem_ker, htB, hsc, ← LinearMap.mem_ker, hφk]
  have hfin0 : Module.Finite Γ(P, W.1) ((F 0).obj W.1) := hFc 0 W
  obtain ⟨L, i1, i2, i3, i4, i5, pr, hprc, hpri, hprt, hprs, hprk⟩ :=
    AdicCompletion.exists_module_finite_forall_comp_eq_and_ker_eq_pow_smul_top_of_forall_surjective
      J hJfg (fun n => (F n).obj W.1) tB htBs htBk hfin0
  have hprc' : ∀ (n : ℕ) (x : L), (φ n).app W (pr (n + 1) x) = pr n x :=
    fun n x => (htB n _).symm.trans (hprc n x)
  have hprt' : ∀ m : ∀ n : ℕ, (F n).obj W.1, (∀ n : ℕ, (φ n).app W (m (n + 1)) = m n) →
      ∃ x : L, ∀ n : ℕ, pr n x = m n := fun m hm => hprt m fun n => (htB n _).trans (hm n)
  have hprk' : ∀ n : ℕ, LinearMap.ker (pr n) = (I.map ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ q.appLE ⊤ W.1 le_top).hom) ^ (n + 1) • (⊤ : Submodule Γ(P, W.1) L) := by
    intro n; rw [hprk n, hJ]
  have hRc : IsAdicComplete (I.map ((algebraMap Γ(P, W.1) (AdicCompletion J Γ(P, W.1))).comp ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ q.appLE ⊤ W.1 le_top).hom)) (AdicCompletion J Γ(P, W.1)) := by
    rw [← Ideal.map_map, ← hJ]
    exact AdicCompletion.isAdicComplete_map_algebraMap_of_fg J hJfg
  obtain ⟨Y, sY, hsY, t, hY, hta, G, ε, θ, hrest⟩ :=
    AlgebraicGeometry.OModulePresheaf.exists_isPullback_isProper_and_exists_forall_surjective_ker_eq_pow_smul_top_of_forall_ker_eq_pow_smul_top
      I q i g K' U hU T' hT' F hFc hFq φ hφs hφk hFZ F' φ' η hηs hηV hηU hηφ hβ v hvη W (AdicCompletion J Γ(P, W.1)) L pr hprc' hpri hprs hprk'
  exact ⟨L, i1, i2, i3, i4, i5, pr, hprc', hpri, hprt', hprs, hprk', hRc, Y, sY, hsY, t, hY, hta, G, ε, θ, hrest⟩

end W_ASM

open W_ASM in
theorem solution
    {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    {P : Scheme.{u}} (q : P ⟶ Spec (CommRingCat.of A)) [IsProper q]
    {Z : Scheme.{u}} (i : Z ⟶ P) [IsClosedImmersion i]
    {V' : Scheme.{u}} (g : V' ⟶ Z) [IsProper g] (K' : V'.OrderedAffineCover)
    (U : Z.Opens) (hU : IsIso (CategoryTheory.Limits.pullback.snd g U.ι))
    (T' : Closeds P) (hT' : ∀ z : Z, z ∉ U → i.base z ∈ T')

    (F : ℕ → OModulePresheaf q) (hFc : ∀ k, (F k).IsCoherent) (hFq : ∀ k, (F k).IsQuasicoherent)
    (φ : ∀ k, OModulePresheaf.AffHom (F (k + 1)) (F k))
    (hφs : ∀ (k : ℕ) (U : P.affineOpens), Function.Surjective ((φ k).app U))
    (hφk : ∀ (k : ℕ) (U : P.affineOpens),
      LinearMap.ker ((φ k).app U) = I ^ (k + 1) • (⊤ : Submodule A ((F (k + 1)).obj U.1)))
    (hFZ : ∀ k, OModulePresheaf.IdealAnnihilates q i.ker (F k))

    (F' : ℕ → OModulePresheaf ((g ≫ i) ≫ q)) (φ' : ∀ k, OModulePresheaf.AffHom (F' (k + 1)) (F' k))
    (η : ∀ (k : ℕ) (U₀ : P.affineOpens) (V : V'.affineOpens), V.1 ≤ (g ≫ i) ⁻¹ᵁ U₀.1 →
      ((F k).obj U₀.1 →ₗ[A] (F' k).obj V.1))
    (hηs : ∀ (k : ℕ) (U₀ : P.affineOpens) (V : V'.affineOpens) (h : V.1 ≤ (g ≫ i) ⁻¹ᵁ U₀.1) (a : Γ(P, U₀.1))
      (x : (F k).obj U₀.1), η k U₀ V h (a • x) = ((g ≫ i).appLE U₀.1 V.1 h).hom a • η k U₀ V h x)
    (hηV : ∀ (k : ℕ) (U₀ : P.affineOpens) (V₁ V₂ : V'.affineOpens) (h₁ : V₁.1 ≤ (g ≫ i) ⁻¹ᵁ U₀.1)
      (h₂ : V₂.1 ≤ (g ≫ i) ⁻¹ᵁ U₀.1) (hV : V₁.1 ≤ V₂.1) (x : (F k).obj U₀.1),
      (F' k).res hV (η k U₀ V₂ h₂ x) = η k U₀ V₁ h₁ x)
    (hηU : ∀ (k : ℕ) (U₁ U₂ : P.affineOpens) (V : V'.affineOpens) (h₁ : V.1 ≤ (g ≫ i) ⁻¹ᵁ U₁.1)
      (h₂ : V.1 ≤ (g ≫ i) ⁻¹ᵁ U₂.1) (hU₁₂ : U₁.1 ≤ U₂.1) (x : (F k).obj U₂.1),
      η k U₂ V h₂ x = η k U₁ V h₁ ((F k).res hU₁₂ x))
    (hηφ : ∀ (k : ℕ) (U₀ : P.affineOpens) (V : V'.affineOpens) (h : V.1 ≤ (g ≫ i) ⁻¹ᵁ U₀.1)
      (x : (F (k + 1)).obj U₀.1), (φ' k).app V (η (k + 1) U₀ V h x) = η k U₀ V h ((φ k).app U₀ x))
    (hβ : ∀ (k : ℕ) (U₀ : P.affineOpens) (V : V'.affineOpens) (h : V.1 ≤ (g ≫ i) ⁻¹ᵁ U₀.1),
      letI := ((g ≫ i).appLE U₀.1 V.1 h).hom.toAlgebra
      ∃ β : Γ(V', V.1) ⊗[Γ(P, U₀.1)] (F k).obj U₀.1 ≃ₗ[Γ(V', V.1)] (F' k).obj V.1,
        ∀ x : (F k).obj U₀.1, β (1 ⊗ₜ x) = η k U₀ V h x)

    (v : ∀ k, OModulePresheaf.AffHom (F k) (OModulePresheaf.cechPushforward (g ≫ i) q K' (F' k)))
    (hvη : ∀ (k : ℕ) (U₀ : P.affineOpens) (x : (F k).obj U₀.1) (j : K'.ι),
      ((v k).app U₀ x).1 j
        = η k U₀ (OModulePresheaf.AffHom.affineChart (g ≫ i) q K' U₀ j)
            (OModulePresheaf.cechPushforward.chart_le_preimage (g ≫ i) K' U₀.1 j) x) :
    ∀ W₀ : P.affineOpens, ∃ N : ℕ, ∀ W : P.affineOpens, W.1 ≤ W₀.1 →
        (∀ (ℓ : ∀ n, (OModulePresheaf.cechPushforward (g ≫ i) q K' (F' n)).obj W.1),
          (∀ n, ((φ' n).cechPushforward (g ≫ i) q K').app W (ℓ (n + 1)) = ℓ n) →
          ∀ a : Γ(P, W.1), a ∈ (Scheme.IdealSheafData.vanishingIdeal T').ideal W ^ N →
            ∃ m : ∀ n, (F n).obj W.1,
              (∀ n, (φ n).app W (m (n + 1)) = m n) ∧ ∀ n, (v n).app W (m n) = a • ℓ n) ∧
        (∀ (m : ∀ n, (F n).obj W.1), (∀ n, (φ n).app W (m (n + 1)) = m n) →
          (∀ n, (v n).app W (m n) = 0) →
          ∀ a : Γ(P, W.1), a ∈ (Scheme.IdealSheafData.vanishingIdeal T').ideal W ^ N →
            ∀ n, a • m n = 0) := by
  classical
  intro W₀
  haveI : IsLocallyNoetherian P := LocallyOfFiniteType.isLocallyNoetherian q
  haveI hB₀ : IsNoetherianRing Γ(P, W₀.1) := IsLocallyNoetherian.component_noetherian W₀

  obtain ⟨L₀, _, _, _, _, _, pr₀, hprc₀, hpri₀, hprt₀, hprs₀, hprk₀, hRc₀, Y₀, sY₀, hsY₀, t₀, hY₀, hta₀, G₀, ε₀, θ₀,
      hGc₀, hGq₀, hεr₀, hεβ₀, hθs₀, hθr₀, hθφ₀, hθε₀, hθo₀, hθk₀⟩ :=
    exists_frame I q i g K' U hU T' hT' F hFc hFq φ hφs hφk hFZ F' φ' η hηs hηV hηU hηφ hβ v hvη W₀ (I.map ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ q.appLE ⊤ W₀.1 le_top).hom) rfl
  haveI := hsY₀
  haveI : IsNoetherianRing (AdicCompletion (I.map ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ q.appLE ⊤ W₀.1 le_top).hom) Γ(P, W₀.1)) :=
    AdicCompletion.isNoetherianRing_of_isNoetherianRing _
  obtain ⟨N, hk₀, hc₀⟩ :=
    torsion_of_frame I q i g K' U hU T' hT' F hFc hFq φ hφs hφk hFZ F' φ' η hηs hηV hηU hηφ hβ v hvη W₀ (AdicCompletion (I.map ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ q.appLE ⊤ W₀.1 le_top).hom) Γ(P, W₀.1)) L₀ pr₀ hprc₀ hpri₀ hprs₀ hprk₀
      hRc₀ sY₀ t₀ hY₀ hta₀ G₀ hGc₀ hGq₀ ε₀ hεr₀ hεβ₀ θ₀ hθs₀ hθr₀ hθφ₀ hθε₀ hθo₀ hθk₀
  refine ⟨N, fun W hW => ?_⟩
  haveI hB : IsNoetherianRing Γ(P, W.1) := IsLocallyNoetherian.component_noetherian W

  letI algW : Algebra Γ(P, W₀.1) Γ(P, W.1) := (P.presheaf.map (homOfLE hW).op).hom.toAlgebra
  have hresLE : (𝟙 P : P ⟶ P).appLE W₀.1 W.1 hW = P.presheaf.map (homOfLE hW).op := by
    rw [Scheme.Hom.appLE]
    have hid : (𝟙 P : P ⟶ P).app W₀.1 = 𝟙 _ := rfl
    rw [hid]
    exact Category.id_comp _
  haveI : Module.Flat Γ(P, W₀.1) Γ(P, W.1) := by
    have h := HasRingHomProperty.appLE @Flat (𝟙 P) inferInstance W₀ W hW
    rwa [hresLE] at h
  haveI : Algebra.FiniteType Γ(P, W₀.1) Γ(P, W.1) := by
    have h := HasRingHomProperty.appLE @LocallyOfFiniteType (𝟙 P) inferInstance W₀ W hW
    rwa [hresLE] at h

  have hJ : (I.map ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ q.appLE ⊤ W₀.1 le_top).hom).map (algebraMap Γ(P, W₀.1) Γ(P, W.1)) = (I.map ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ q.appLE ⊤ W.1 le_top).hom) := by
    rw [Ideal.map_map]
    congr 1
    change (((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ q.appLE ⊤ W₀.1 le_top) ≫ P.presheaf.map (homOfLE hW).op).hom
      = _
    rw [Category.assoc, Scheme.Hom.appLE_map]
  obtain ⟨L, _, _, _, _, _, pr, hprc, hpri, hprt, hprs, hprk, hRc, Y, sY, hsY, t, hY, hta, G, ε, θ,
      hGc, hGq, hεr, hεβ, hθs, hθr, hθφ, hθε, hθo, hθk⟩ :=
    exists_frame I q i g K' U hU T' hT' F hFc hFq φ hφs hφk hFZ F' φ' η hηs hηV hηU hηφ hβ v hvη W ((I.map ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ q.appLE ⊤ W₀.1 le_top).hom).map (algebraMap Γ(P, W₀.1) Γ(P, W.1))) hJ
  haveI := hsY
  haveI : IsNoetherianRing (AdicCompletion ((I.map ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ q.appLE ⊤ W₀.1 le_top).hom).map (algebraMap Γ(P, W₀.1) Γ(P, W.1))) Γ(P, W.1)) :=
    AdicCompletion.isNoetherianRing_of_isNoetherianRing _

  obtain ⟨f, hf, hflat⟩ :=
    AdicCompletion.exists_ringHom_comp_algebraMap_eq_and_flat_of_flat_of_finiteType
      (B₀ := Γ(P, W₀.1)) (B := Γ(P, W.1)) (I.map ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ q.appLE ⊤ W₀.1 le_top).hom)
  letI algR : Algebra (AdicCompletion (I.map ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ q.appLE ⊤ W₀.1 le_top).hom) Γ(P, W₀.1))
      (AdicCompletion ((I.map ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ q.appLE ⊤ W₀.1 le_top).hom).map (algebraMap Γ(P, W₀.1) Γ(P, W.1))) Γ(P, W.1)) := f.toAlgebra
  haveI : Module.Flat (AdicCompletion (I.map ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ q.appLE ⊤ W₀.1 le_top).hom) Γ(P, W₀.1))
      (AdicCompletion ((I.map ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ q.appLE ⊤ W₀.1 le_top).hom).map (algebraMap Γ(P, W₀.1) Γ(P, W.1))) Γ(P, W.1)) := hflat

  letI modn : ∀ n : ℕ, Module Γ(P, W₀.1) ((F n).obj W.1) := fun n =>
    Module.compHom ((F n).obj W.1) (algebraMap Γ(P, W₀.1) Γ(P, W.1))
  haveI towern : ∀ n : ℕ, IsScalarTower Γ(P, W₀.1) Γ(P, W.1) ((F n).obj W.1) := fun n =>
    IsScalarTower.of_algebraMap_smul fun r x => rfl
  let κ : ∀ n : ℕ, (F n).obj W₀.1 →ₗ[Γ(P, W₀.1)] (F n).obj W.1 := fun n =>
    { toFun := fun x => (F n).res hW x
      map_add' := fun x y => map_add _ x y
      map_smul' := fun a x => by
        rw [(F n).res_smul hW a x]
        rfl }
  have hκ : ∀ n : ℕ, IsBaseChange Γ(P, W.1) (κ n) := by
    intro n
    obtain ⟨β, hβ1⟩ :=
      AlgebraicGeometry.OModulePresheaf.IsQuasicoherent.exists_linearEquiv_tensorProduct_apply_one_tmul_eq_res
        (F n) (hFq n) W₀ W hW
    exact IsBaseChange.of_equiv β fun x => hβ1 x

  let tB₀ : ∀ n : ℕ, (F (n + 1)).obj W₀.1 →ₗ[Γ(P, W₀.1)] (F n).obj W₀.1 := fun n =>
    { toFun := fun x => (φ n).app W₀ x
      map_add' := fun x y => map_add _ x y
      map_smul' := fun a x => by exact (φ n).app_smul W₀ a x }
  let tB : ∀ n : ℕ, (F (n + 1)).obj W.1 →ₗ[Γ(P, W.1)] (F n).obj W.1 := fun n =>
    { toFun := fun x => (φ n).app W x
      map_add' := fun x y => map_add _ x y
      map_smul' := fun a x => by exact (φ n).app_smul W a x }
  have hκt : ∀ (n : ℕ) (x : (F (n + 1)).obj W₀.1), tB n (κ (n + 1) x) = κ n (tB₀ n x) := by
    intro n x
    exact (φ n).naturality_apply (U := W) (U' := W₀) hW x

  have hprk' : ∀ n : ℕ, LinearMap.ker (pr n)
      = ((I.map ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ q.appLE ⊤ W₀.1 le_top).hom).map (algebraMap Γ(P, W₀.1) Γ(P, W.1))) ^ (n + 1) • (⊤ : Submodule Γ(P, W.1) L) := by
    intro n; rw [hprk n, hJ]
  obtain ⟨e, heb, he⟩ :=
    AdicCompletion.exists_bijective_forall_apply_tmul_eq_of_isBaseChange_of_forall_ker_eq_pow_smul_top
      (I.map ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ q.appLE ⊤ W₀.1 le_top).hom) ((isNoetherianRing_iff_ideal_fg A).mp inferInstance I |>.map _)
      (fun n => (F n).obj W₀.1) tB₀ (fun n => (F n).obj W.1) tB κ hκ hκt
      L₀ pr₀ (fun n x => hprc₀ n x) hpri₀ (fun m hm => hprt₀ m hm) hprs₀ hprk₀
      L pr (fun n x => hprc n x) hpri (fun m hm => hprt m hm) hprs hprk' f hf

  obtain ⟨hk, hc⟩ :=
    AlgebraicGeometry.OModulePresheaf.forall_smul_eq_zero_and_exists_eq_smul_of_le_of_flat_of_bijective
      I q i g K' U hU T' hT' F hFc hFq φ hφs hφk hFZ F' φ' η hηs hηV hηU hηφ hβ v hvη
      W₀ (AdicCompletion (I.map ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ q.appLE ⊤ W₀.1 le_top).hom) Γ(P, W₀.1)) L₀ pr₀ hprc₀ hpri₀ hprs₀ hprk₀ sY₀ t₀ hY₀ hta₀ G₀ hGc₀ hGq₀ ε₀ hεr₀ hεβ₀
      W (AdicCompletion ((I.map ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ q.appLE ⊤ W₀.1 le_top).hom).map (algebraMap Γ(P, W₀.1) Γ(P, W.1))) Γ(P, W.1)) L pr hprc hpri hprs hprk
        sY t hY hta G hGc hGq ε hεr hεβ
      hW (fun b => hf b) e heb (fun n x₀ => he n x₀) N hk₀ hc₀
  exact threads_of_torsion I q i g K' U hU T' hT' F hFc hFq φ hφs hφk hFZ F' φ' η hηs hηV hηU hηφ hβ v hvη W _ L pr hprc hpri hprs hprk hprt hRc sY t hY hta G hGc hGq ε hεr hεβ
    θ hθs hθr hθφ hθε hθo hθk N hk hc

end S_AlgebraicGeometry_OModulePresheaf_exists_forall_thread_smul_eq_apply_and_smul_eq_zero_of_isIso_pullback_snd_of_isProper
end P2MW
export P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_forall_thread_smul_eq_apply_and_smul_eq_zero_of_isIso_pullback_snd_of_isProper (solution)
