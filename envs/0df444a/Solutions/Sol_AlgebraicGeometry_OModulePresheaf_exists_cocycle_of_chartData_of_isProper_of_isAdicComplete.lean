-- Prove2me | solution 1 for AlgebraicGeometry.OModulePresheaf.exists_cocycle_of_chartData_of_isProper_of_isAdicComplete
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/db676d3a-8add-5e93-ad5f-fef7cf3ce04c

import Mathlib
import Theorems.Thm_LinearMap_existsUnique_sub_eq_comp_comp_of_extension
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_cochain_internalHom_forall_eq_comp_sub_of_chartData
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_d_eq_zero_of_forall_eq_comp_sub_of_chartData
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_mem_pow_smul_sup_range_d_of_forall_eq_comp_sub_of_chartData
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_mem_range_d_of_d_eq_zero_of_forall_mem_pow_smul_sup_range_d_of_isAdicComplete_of_isProper
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_isCoherent_internalHom_and_existsUnique_eval_eq
import Definitions.Def_AlgebraicGeometry_OModulePresheafHom
import Definitions.Def_AlgebraicGeometry_OModulePresheafInternalHom
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_cocycle_of_chartData_of_isProper_of_isAdicComplete
p2m_attr_erase "instance" "AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul AlgebraicGeometry.OModulePresheaf.Leray.biC_module AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I AlgebraicGeometry.ChowDatum.hι_closed AlgebraicGeometry.ChowDatumProj.hιN_closed AlgebraicGeometry.ChowDatumProj.hp_proper AlgebraicGeometry.ChowDatum.hp_isoU AlgebraicGeometry.ChowDatum.hp_proper AlgebraicGeometry.ProjSpace.algebraAway AlgebraicGeometry.ProjSpace.instIsProperProdOverπ AlgebraicGeometry.ChowDatumProj.hp_isoU AlgebraicGeometry.ProjSpace.isProper_π AlgebraicGeometry.ProjSpace.finiteType_mvPolynomial ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero"
p2m_attr_erase "instance" "ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule"
p2m_attr_erase "simp" "AlgebraicGeometry.OModulePresheaf.prod_obj AlgebraicGeometry.OModulePresheaf.restrOpen_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq AlgebraicGeometry.OModulePresheaf.pushforward_obj AlgebraicGeometry.OModulePresheaf.im_obj AlgebraicGeometry.OModulePresheaf.pow_obj AlgebraicGeometry.OModulePresheaf.fstHom_app AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U AlgebraicGeometry.OModulePresheaf.sndHom_app AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq AlgebraicGeometry.ChowDatumProj.mk.sizeOf_spec AlgebraicGeometry.ChowDatum.mk.sizeOf_spec AlgebraicGeometry.ChowDatumProj.mk.injEq AlgebraicGeometry.ChowDatum.mk.injEq ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.mk.injEq"

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry TopologicalSpace

universe u

theorem RedY1.cocycle_of_regimes {ι : Type*} [LinearOrder ι] (N : ι → Type*)
    (w : ∀ i j : ι, N i → N j)
    (v : ∀ i j : ι, i < j → N i → N j) (vi : ∀ i j : ι, i < j → N j → N i)
    (hlt : ∀ (i j : ι) (h : i < j) (x : N i), w i j x = v i j h x)
    (hgt : ∀ (i j : ι) (h : j < i) (x : N i), w i j x = vi j i h x)
    (heq : ∀ (i : ι) (x : N i), w i i x = x)
    (hvcoc : ∀ (i j l : ι) (h : i < j) (h' : j < l) (x : N i), v j l h' (v i j h x) = v i l (h.trans h') x)
    (hvi_v : ∀ (i j : ι) (h : i < j) (x : N i), vi i j h (v i j h x) = x)
    (hv_vi : ∀ (i j : ι) (h : i < j) (z : N j), v i j h (vi i j h z) = z) :
    ∀ (i j l : ι) (x : N i), w j l (w i j x) = w i l x := by

  have hgt₁ : ∀ (i j : ι) (h : j < i) (x : N i), v j i h (w i j x) = x := fun i j h x => by
    rw [hgt i j h, hv_vi]
  have hgt₂ : ∀ (i j : ι) (h : j < i) (y : N j), w i j (v j i h y) = y := fun i j h y => by
    rw [hgt i j h, hvi_v]
  intro i j l x
  rcases lt_trichotomy i j with hij | rfl | hji
  · rcases lt_trichotomy j l with hjl | rfl | hlj
    ·
      rw [hlt i j hij, hlt j l hjl, hlt i l (hij.trans hjl), hvcoc]
    ·
      rw [heq]
    · rcases lt_trichotomy i l with hil | rfl | hli
      ·
        rw [hlt i j hij, hlt i l hil, ← hvcoc i l j hil hlj, hgt₂ j l hlj]
      ·
        rw [heq, hlt i j hij, hgt₂ j i hij]
      ·
        rw [hlt i j hij]
        have hx : x = v l i hli (w i l x) := (hgt₁ i l hli x).symm
        conv_lhs => rw [hx, hvcoc l i j hli hij, hgt₂ j l (hli.trans hij)]
  ·
    rw [heq]
  · rcases lt_trichotomy j l with hjl | rfl | hlj
    · rcases lt_trichotomy i l with hil | rfl | hli
      ·
        rw [hlt j l hjl, hlt i l hil]
        have hx : x = v j i hji (w i j x) := (hgt₁ i j hji x).symm
        conv_rhs => rw [hx, hvcoc j i l hji hil]
      ·
        rw [heq, hlt j i hji, hgt₁ i j hji]
      ·
        have hx : x = v j i hji (w i j x) := (hgt₁ i j hji x).symm
        rw [hlt j l hjl]
        conv_rhs => rw [hx, ← hvcoc j l i hjl hli, hgt₂ i l hli]
    ·
      rw [heq]
    ·
      have hx : x = v j i hji (w i j x) := (hgt₁ i j hji x).symm
      have hy : w i j x = v l j hlj (w j l (w i j x)) := (hgt₁ j l hlj _).symm
      have h3 : v l i (hlj.trans hji) (w j l (w i j x)) = x := by
        rw [← hvcoc l j i hlj hji, ← hy, ← hx]
      conv_rhs => rw [← h3]
      rw [hgt₂ i l (hlj.trans hji)]

theorem RedY1.cocAux {G : Type*} [AddCommGroup G] (a b c d e : G) (h : c - d + e = a - b) :
    a - c - e = b - d := by
  have h' : a = c - d + e + b := by rw [h, sub_add_cancel]
  rw [h']; abel

set_option maxHeartbeats 4000000 in
theorem solution
    {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A) [IsAdicComplete I A]
    {P : Scheme.{u}} (q : P ⟶ Spec (CommRingCat.of A)) [IsProper q]
    (F : ℕ → OModulePresheaf q) (hFc : ∀ k, (F k).IsCoherent) (hFq : ∀ k, (F k).IsQuasicoherent)
    (φ : ∀ k, OModulePresheaf.AffHom (F (k + 1)) (F k))
    (hφs : ∀ (k : ℕ) (U : P.affineOpens), Function.Surjective ((φ k).app U))
    (hφk : ∀ (k : ℕ) (U : P.affineOpens),
      LinearMap.ker ((φ k).app U) = I ^ (k + 1) • (⊤ : Submodule A ((F (k + 1)).obj U.1)))
    (E : ℕ → OModulePresheaf q) (hEc : ∀ k, (E k).IsCoherent) (hEq : ∀ k, (E k).IsQuasicoherent)
    (τ : ∀ k, OModulePresheaf.AffHom (E (k + 1)) (E k))
    (hτs : ∀ (k : ℕ) (U : P.affineOpens), Function.Surjective ((τ k).app U))
    (hτk : ∀ (k : ℕ) (U : P.affineOpens),
      LinearMap.ker ((τ k).app U) = I ^ (k + 1) • (⊤ : Submodule A ((E (k + 1)).obj U.1)))
    (ε : ∀ k, OModulePresheaf.AffHom (F k) (E k))
    (hεs : ∀ (k : ℕ) (U : P.affineOpens), Function.Surjective ((ε k).app U))
    (hεc : ∀ (k : ℕ) (U : P.affineOpens),
      (τ k).app U ∘ₗ (ε (k + 1)).app U = (ε k).app U ∘ₗ (φ k).app U)
    (GE : OModulePresheaf q) (hGEc : GE.IsCoherent) (hGEq : GE.IsQuasicoherent)
    (ψE : ∀ k, OModulePresheaf.AffHom GE (E k))
    (hψEs : ∀ (k : ℕ) (U : P.affineOpens), Function.Surjective ((ψE k).app U))
    (hψEk : ∀ (k : ℕ) (U : P.affineOpens),
      LinearMap.ker ((ψE k).app U) = I ^ (k + 1) • (⊤ : Submodule A (GE.obj U.1)))
    (hψEc : ∀ (k : ℕ) (U : P.affineOpens), (τ k).app U ∘ₗ (ψE (k + 1)).app U = (ψE k).app U)
    (GK : OModulePresheaf q) (hGKc : GK.IsCoherent) (hGKq : GK.IsQuasicoherent)
    (lam : ∀ k, OModulePresheaf.AffHom GK (F k))
    (hlamc : ∀ (k : ℕ) (U : P.affineOpens), (φ k).app U ∘ₗ (lam (k + 1)).app U = (lam k).app U)
    (hlamr : ∀ (k : ℕ) (U : P.affineOpens),
      LinearMap.range ((lam k).app U) = LinearMap.ker ((ε k).app U))
    (hlami : ∀ U : P.affineOpens, ∃ c : ℕ, ∀ k : ℕ,
      LinearMap.ker ((lam (k + c)).app U) ≤ I ^ (k + 1) • (⊤ : Submodule A (GK.obj U.1)))
    (K : P.OrderedAffineCover)
    (M : ∀ i : K.ι, {U : P.affineOpens // U.1 ≤ K.U i} → Type u)
    [∀ (i : K.ι) (U : {U : P.affineOpens // U.1 ≤ K.U i}), AddCommGroup (M i U)]
    [∀ (i : K.ι) (U : {U : P.affineOpens // U.1 ≤ K.U i}), Module A (M i U)]
    [iΓ : ∀ (i : K.ι) (U : {U : P.affineOpens // U.1 ≤ K.U i}), Module Γ(P, U.1.1) (M i U)]
    [∀ (i : K.ι) (U : {U : P.affineOpens // U.1 ≤ K.U i}),
        letI := Scheme.TwoAffineOpenCover.algebraOfHom q U.1.1; IsScalarTower A Γ(P, U.1.1) (M i U)]
    (res : ∀ (i : K.ι) {U U' : {U : P.affineOpens // U.1 ≤ K.U i}}, U'.1.1 ≤ U.1.1 → (M i U →ₗ[A] M i U'))
    (res_smul : ∀ (i : K.ι) {U U' : {U : P.affineOpens // U.1 ≤ K.U i}} (h : U'.1.1 ≤ U.1.1) (a : Γ(P, U.1.1)) (x : M i U),
        res i h (a • x) = (P.presheaf.map (homOfLE h).op).hom a • res i h x)
    (res_refl : ∀ (i : K.ι) (U : {U : P.affineOpens // U.1 ≤ K.U i}) (x : M i U), res i (le_refl U.1.1) x = x)
    (res_comp : ∀ (i : K.ι) {U U' U'' : {U : P.affineOpens // U.1 ≤ K.U i}} (h : U''.1.1 ≤ U'.1.1) (h' : U'.1.1 ≤ U.1.1)
        (x : M i U), res i (h.trans h') x = res i h (res i h' x))
    (hqc : ∀ (i : K.ι) (U Ug : {U : P.affineOpens // U.1 ≤ K.U i}) (g : Γ(P, U.1.1)) (hUg : Ug.1.1 = P.basicOpen g),
        (∀ y : M i Ug, ∃ (n : ℕ) (x : M i U),
            res i (hUg.trans_le (P.basicOpen_le g)) x =
              (P.presheaf.map (homOfLE (hUg.trans_le (P.basicOpen_le g))).op).hom (g ^ n) • y) ∧
        (∀ x : M i U, res i (hUg.trans_le (P.basicOpen_le g)) x = 0 → ∃ n : ℕ, (g ^ n) • x = 0))
    (hfg : ∀ (i : K.ι) (U : {U : P.affineOpens // U.1 ≤ K.U i}), Module.Finite (Γ(P, U.1.1) : Type u) (M i U))
    (ϑ : ∀ (i : K.ι) (U : {U : P.affineOpens // U.1 ≤ K.U i}), GK.obj U.1.1 →ₗ[A] M i U)
    (θE : ∀ (i : K.ι) (U : {U : P.affineOpens // U.1 ≤ K.U i}), M i U →ₗ[A] GE.obj U.1.1)
    (θF : ∀ (i : K.ι) (k : ℕ) (U : {U : P.affineOpens // U.1 ≤ K.U i}), M i U →ₗ[A] (F k).obj U.1.1)
    (hϑs : ∀ (i : K.ι) (U : {U : P.affineOpens // U.1 ≤ K.U i}) (a : Γ(P, U.1.1)) (x : GK.obj U.1.1), ϑ i U (a • x) = a • ϑ i U x)
    (hθEs : ∀ (i : K.ι) (U : {U : P.affineOpens // U.1 ≤ K.U i}) (a : Γ(P, U.1.1)) (x : M i U), θE i U (a • x) = a • θE i U x)
    (hθFs : ∀ (i : K.ι) (k : ℕ) (U : {U : P.affineOpens // U.1 ≤ K.U i}) (a : Γ(P, U.1.1)) (x : M i U),
        θF i k U (a • x) = a • θF i k U x)
    (hϑn : ∀ (i : K.ι) (U U' : {U : P.affineOpens // U.1 ≤ K.U i}) (h : U'.1.1 ≤ U.1.1) (x : GK.obj U.1.1),
        ϑ i U' (GK.res h x) = res i h (ϑ i U x))
    (hθEn : ∀ (i : K.ι) (U U' : {U : P.affineOpens // U.1 ≤ K.U i}) (h : U'.1.1 ≤ U.1.1) (x : M i U),
        θE i U' (res i h x) = GE.res h (θE i U x))
    (hθFn : ∀ (i : K.ι) (k : ℕ) (U U' : {U : P.affineOpens // U.1 ≤ K.U i}) (h : U'.1.1 ≤ U.1.1) (x : M i U),
        θF i k U' (res i h x) = (F k).res h (θF i k U x))
    (hexact : ∀ (i : K.ι) (U : {U : P.affineOpens // U.1 ≤ K.U i}), LinearMap.range (ϑ i U) = LinearMap.ker (θE i U))
    (hsurj : ∀ (i : K.ι) (U : {U : P.affineOpens // U.1 ≤ K.U i}), Function.Surjective (θE i U))
    (hϑi : ∀ (i : K.ι) (U : {U : P.affineOpens // U.1 ≤ K.U i}), Function.Injective (ϑ i U))
    (hc1 : ∀ (i : K.ι) (k : ℕ) (U : {U : P.affineOpens // U.1 ≤ K.U i}), (φ k).app U.1 ∘ₗ θF i (k + 1) U = θF i k U)
    (hc2 : ∀ (i : K.ι) (k : ℕ) (U : {U : P.affineOpens // U.1 ≤ K.U i}), θF i k U ∘ₗ ϑ i U = (lam k).app U.1)
    (hc3 : ∀ (i : K.ι) (k : ℕ) (U : {U : P.affineOpens // U.1 ≤ K.U i}), (ε k).app U.1 ∘ₗ θF i k U = (ψE k).app U.1 ∘ₗ θE i U)

    (u : ∀ (i j : K.ι) (W : {U : P.affineOpens // U.1 ≤ K.U i}) (hj : W.1.1 ≤ K.U j), M i W →ₗ[A] M j ⟨W.1, hj⟩)
    (hub : ∀ (i j : K.ι) (W : {U : P.affineOpens // U.1 ≤ K.U i}) (hj : W.1.1 ≤ K.U j), Function.Bijective (u i j W hj))
    (hus : ∀ (i j : K.ι) (W : {U : P.affineOpens // U.1 ≤ K.U i}) (hj : W.1.1 ≤ K.U j) (a : Γ(P, W.1.1)) (x : M i W),
        letI : Module Γ(P, W.1.1) (M j ⟨W.1, hj⟩) := iΓ j ⟨W.1, hj⟩
        u i j W hj (a • x) = a • u i j W hj x)
    (hun : ∀ (i j : K.ι) (W W' : {U : P.affineOpens // U.1 ≤ K.U i}) (hj : W.1.1 ≤ K.U j) (h : W'.1.1 ≤ W.1.1) (x : M i W),
        u i j W' (h.trans hj) (res i h x) = res j (U := ⟨W.1, hj⟩) (U' := ⟨W'.1, h.trans hj⟩) h (u i j W hj x))
    (huϑ : ∀ (i j : K.ι) (W : {U : P.affineOpens // U.1 ≤ K.U i}) (hj : W.1.1 ≤ K.U j) (x : GK.obj W.1.1),
        u i j W hj (ϑ i W x) = ϑ j ⟨W.1, hj⟩ x)
    (huθE : ∀ (i j : K.ι) (W : {U : P.affineOpens // U.1 ≤ K.U i}) (hj : W.1.1 ≤ K.U j) (x : M i W),
        θE j ⟨W.1, hj⟩ (u i j W hj x) = θE i W x)
    :
    ∃ (u' : ∀ (i j : K.ι) (W : {U : P.affineOpens // U.1 ≤ K.U i}) (hj : W.1.1 ≤ K.U j), M i W →ₗ[A] M j ⟨W.1, hj⟩),
      (∀ (i j : K.ι) (W : {U : P.affineOpens // U.1 ≤ K.U i}) (hj : W.1.1 ≤ K.U j), Function.Bijective (u' i j W hj)) ∧
      (∀ (i j : K.ι) (W : {U : P.affineOpens // U.1 ≤ K.U i}) (hj : W.1.1 ≤ K.U j) (a : Γ(P, W.1.1)) (x : M i W),
        letI : Module Γ(P, W.1.1) (M j ⟨W.1, hj⟩) := iΓ j ⟨W.1, hj⟩
        u' i j W hj (a • x) = a • u' i j W hj x) ∧
      (∀ (i j : K.ι) (W W' : {U : P.affineOpens // U.1 ≤ K.U i}) (hj : W.1.1 ≤ K.U j) (h : W'.1.1 ≤ W.1.1) (x : M i W),
        u' i j W' (h.trans hj) (res i h x) = res j (U := ⟨W.1, hj⟩) (U' := ⟨W'.1, h.trans hj⟩) h (u' i j W hj x)) ∧
      (∀ (i j : K.ι) (W : {U : P.affineOpens // U.1 ≤ K.U i}) (hj : W.1.1 ≤ K.U j) (x : GK.obj W.1.1), u' i j W hj (ϑ i W x) = ϑ j ⟨W.1, hj⟩ x) ∧
      (∀ (i j : K.ι) (W : {U : P.affineOpens // U.1 ≤ K.U i}) (hj : W.1.1 ≤ K.U j) (x : M i W), θE j ⟨W.1, hj⟩ (u' i j W hj x) = θE i W x) ∧

      (∀ (i j l : K.ι) (W : {U : P.affineOpens // U.1 ≤ K.U i}) (hj : W.1.1 ≤ K.U j) (hl : W.1.1 ≤ K.U l) (x : M i W),
        u' j l ⟨W.1, hj⟩ hl (u' i j W hj x) = u' i l W hl x) := by
  classical
  haveI : IsLocallyNoetherian P := LocallyOfFiniteType.isLocallyNoetherian q
  obtain ⟨hHc, hHq, -⟩ := OModulePresheaf.isCoherent_internalHom_and_existsUnique_eval_eq q GE GK hGEc hGEq hGKc hGKq
  obtain ⟨g, hg⟩ := AlgebraicGeometry.OModulePresheaf.exists_cochain_internalHom_forall_eq_comp_sub_of_chartData I q F hFc hFq φ hφs hφk E hEc hEq τ hτs hτk ε hεs hεc GE hGEc hGEq ψE hψEs hψEk hψEc GK hGKc hGKq lam hlamc hlamr hlami K M res res_smul res_refl res_comp hqc hfg ϑ θE θF hϑs hθEs hθFs hϑn hθEn hθFn hexact hsurj hϑi hc1 hc2 hc3 u hub hus hun huϑ huθE
  have hdg := AlgebraicGeometry.OModulePresheaf.d_eq_zero_of_forall_eq_comp_sub_of_chartData I q F hFc hFq φ hφs hφk E hEc hEq τ hτs hτk ε hεs hεc GE hGEc hGEq ψE hψEs hψEk hψEc GK hGKc hGKq lam hlamc hlamr hlami K M res res_smul res_refl res_comp hqc hfg ϑ θE θF hϑs hθEs hθFs hϑn hθEn hθFn hexact hsurj hϑi hc1 hc2 hc3 u hub hus hun huϑ huθE g hg
  have hform := AlgebraicGeometry.OModulePresheaf.mem_pow_smul_sup_range_d_of_forall_eq_comp_sub_of_chartData I q F hFc hFq φ hφs hφk E hEc hEq τ hτs hτk ε hεs hεc GE hGEc hGEq ψE hψEs hψEk hψEc GK hGKc hGKq lam hlamc hlamr hlami K M res res_smul res_refl res_comp hqc hfg ϑ θE θF hϑs hθEs hθFs hϑn hθEn hθFn hexact hsurj hϑi hc1 hc2 hc3 u hub hus hun huϑ huθE g hg
  obtain ⟨β, hβ⟩ := OModulePresheaf.mem_range_d_of_d_eq_zero_of_forall_mem_pow_smul_sup_range_d_of_isAdicComplete_of_isProper
    I q (OModulePresheaf.internalHom GE GK) hHc hHq K 1 g hdg hform
  let pr : ∀ (i j : K.ι), i < j → K.Idx 1 := fun i j h => ⟨![i, j], Fin.strictMono_iff_lt_succ.2 (fun a => by
    fin_cases a; simpa using h)⟩
  let tr : ∀ (i j l : K.ι), i < j → j < l → K.Idx 2 := fun i j l h h' => ⟨![i, j, l], Fin.strictMono_iff_lt_succ.2 (fun a => by
    fin_cases a
    · simpa using h
    · simpa using h')⟩
  have hpr : ∀ (i j : K.ι) (h : i < j) (W : P.affineOpens), W.1 ≤ K.U i → W.1 ≤ K.U j → W.1 ≤ K.inter (pr i j h) := by
    intro i j h W hi hj
    refine le_iInf fun a => ?_
    fin_cases a
    · exact hi
    · exact hj
  have htr : ∀ (i j l : K.ι) (h : i < j) (h' : j < l) (W : P.affineOpens),
      W.1 ≤ K.U i → W.1 ≤ K.U j → W.1 ≤ K.U l → W.1 ≤ K.inter (tr i j l h h') := by
    intro i j l h h' W hi hj hl
    refine le_iInf fun a => ?_
    fin_cases a
    · exact hi
    · exact hj
    · exact hl
  have hface0 : ∀ (i j l : K.ι) (h : i < j) (h' : j < l), K.face (tr i j l h h') 0 = pr j l h' := by
    intro i j l h h'; apply Subtype.ext; funext a
    rw [Scheme.OrderedAffineCover.face_val]
    fin_cases a <;> rfl
  have hface1 : ∀ (i j l : K.ι) (h : i < j) (h' : j < l), K.face (tr i j l h h') 1 = pr i l (h.trans h') := by
    intro i j l h h'; apply Subtype.ext; funext a
    rw [Scheme.OrderedAffineCover.face_val]
    fin_cases a <;> rfl
  have hface2 : ∀ (i j l : K.ι) (h : i < j) (h' : j < l), K.face (tr i j l h h') 2 = pr i j h := by
    intro i j l h h'; apply Subtype.ext; funext a
    rw [Scheme.OrderedAffineCover.face_val]
    fin_cases a <;> rfl
  have hcomp : ∀ (s s' : K.Idx 1) (e : s = s') (W : P.affineOpens) (hW : W.1 ≤ K.inter s) (hW' : W.1 ≤ K.inter s'),
      (β s).1 ⟨W, hW⟩ = (β s').1 ⟨W, hW'⟩ := by
    intro s s' e W hW hW'; subst e; rfl
  have hres : ∀ {U U' : P.Opens} (h : U ≤ U') (c : (OModulePresheaf.internalHom GE GK).obj U')
      (W : {U₀ : P.affineOpens // U₀.1 ≤ U}),
      ((OModulePresheaf.internalHom GE GK).res h c).1 W = c.1 ⟨W.1, W.2.trans h⟩ := fun _ _ _ => rfl
  let βp : ∀ (i j : K.ι), i < j → ∀ (W : P.affineOpens), W.1 ≤ K.U i → W.1 ≤ K.U j → (GE.obj W.1 →ₗ[A] GK.obj W.1) :=
    fun i j h W hi hj => (β (pr i j h)).1 ⟨W, hpr i j h W hi hj⟩
  have hkey : ∀ (i j l : K.ι) (h : i < j) (h' : j < l) (W : P.affineOpens) (hi : W.1 ≤ K.U i) (hj : W.1 ≤ K.U j)
      (hl : W.1 ≤ K.U l) (x : M i ⟨W, hi⟩),
      ϑ l ⟨W, hl⟩ (βp j l h' W hj hl (θE i ⟨W, hi⟩ x)) - ϑ l ⟨W, hl⟩ (βp i l (h.trans h') W hi hl (θE i ⟨W, hi⟩ x)) +
        ϑ l ⟨W, hl⟩ (βp i j h W hi hj (θE i ⟨W, hi⟩ x)) =
      u j l ⟨W, hj⟩ hl (u i j ⟨W, hi⟩ hj x) - u i l ⟨W, hi⟩ hl x := by
    intro i j l h h' W hi hj hl x
    have e1 := hg (tr i j l h h') ⟨W, htr i j l h h' W hi hj hl⟩ x
    rw [← hβ, OModulePresheaf.d_apply, Fin.sum_univ_three] at e1
    simp only [Fin.val_zero, Fin.val_one, Fin.val_two, pow_zero, pow_one, pow_two, neg_mul, neg_neg, one_mul,
      one_smul, neg_smul] at e1
    change ϑ l ⟨W, hl⟩ ((((β (K.face (tr i j l h h') 0)).1 ⟨W, _⟩ + -((β (K.face (tr i j l h h') 1)).1 ⟨W, _⟩)) +
        (β (K.face (tr i j l h h') 2)).1 ⟨W, _⟩) (θE i ⟨W, hi⟩ x)) =
      u j l ⟨W, hj⟩ hl (u i j ⟨W, hi⟩ hj x) - u i l ⟨W, hi⟩ hl x at e1
    rw [LinearMap.add_apply, LinearMap.add_apply, LinearMap.neg_apply, map_add, map_add, map_neg,
      hcomp _ _ (hface0 i j l h h') W _ (hpr j l h' W hj hl), hcomp _ _ (hface1 i j l h h') W _ (hpr i l (h.trans h') W hi hl),
      hcomp _ _ (hface2 i j l h h') W _ (hpr i j h W hi hj)] at e1
    rw [← e1]
    simp only [βp]
    abel
  have hβps : ∀ (i j : K.ι) (h : i < j) (W : P.affineOpens) (hi : W.1 ≤ K.U i) (hj : W.1 ≤ K.U j)
      (a : Γ(P, W.1)) (y : GE.obj W.1), βp i j h W hi hj (a • y) = a • βp i j h W hi hj y :=
    fun i j h W hi hj a y => (β (pr i j h)).2.1 ⟨W, hpr i j h W hi hj⟩ a y
  have hβpn : ∀ (i j : K.ι) (h : i < j) (W W' : P.affineOpens) (hi : W.1 ≤ K.U i) (hj : W.1 ≤ K.U j)
      (hi' : W'.1 ≤ K.U i) (hj' : W'.1 ≤ K.U j) (hW : W'.1 ≤ W.1) (y : GE.obj W.1),
      βp i j h W' hi' hj' (GE.res hW y) = GK.res hW (βp i j h W hi hj y) :=
    fun i j h W W' hi hj hi' hj' hW y => (β (pr i j h)).2.2 ⟨W', hpr i j h W' hi' hj'⟩ ⟨W, hpr i j h W hi hj⟩ hW y
  clear_value βp

  have hθEϑ : ∀ (i : K.ι) (U : {U : P.affineOpens // U.1 ≤ K.U i}) (y : GK.obj U.1.1), θE i U (ϑ i U y) = 0 := by
    intro i U y
    have : ϑ i U y ∈ LinearMap.ker (θE i U) := by rw [← hexact]; exact ⟨y, rfl⟩
    exact this

  have huθE' : ∀ (i j : K.ι) (W : P.affineOpens) (hi : W.1 ≤ K.U i) (hj : W.1 ≤ K.U j) (x : M i ⟨W, hi⟩),
      θE j ⟨W, hj⟩ (u i j ⟨W, hi⟩ hj x) = θE i ⟨W, hi⟩ x := fun i j W hi hj x => huθE i j ⟨W, hi⟩ hj x
  have huϑ' : ∀ (i j : K.ι) (W : P.affineOpens) (hi : W.1 ≤ K.U i) (hj : W.1 ≤ K.U j) (y : GK.obj W.1),
      u i j ⟨W, hi⟩ hj (ϑ i ⟨W, hi⟩ y) = ϑ j ⟨W, hj⟩ y := fun i j W hi hj y => huϑ i j ⟨W, hi⟩ hj y

  have hfive : ∀ (i j : K.ι) (W : P.affineOpens) (hi : W.1 ≤ K.U i) (hj : W.1 ≤ K.U j)
      (w : M i ⟨W, hi⟩ →ₗ[A] M j ⟨W, hj⟩),
      (∀ y, w (ϑ i ⟨W, hi⟩ y) = ϑ j ⟨W, hj⟩ y) → (∀ x, θE j ⟨W, hj⟩ (w x) = θE i ⟨W, hi⟩ x) →
      Function.Bijective w := by
    intro i j W hi hj w hwϑ hwθ
    constructor
    · intro x x' hxx'
      rw [← sub_eq_zero] at hxx' ⊢
      rw [← map_sub] at hxx'
      have hk : x - x' ∈ LinearMap.ker (θE i ⟨W, hi⟩) := by
        rw [LinearMap.mem_ker, ← hwθ, hxx', map_zero]
      rw [← hexact] at hk
      obtain ⟨y, hy⟩ := hk
      rw [← hy] at hxx' ⊢
      rw [hwϑ] at hxx'
      rw [hϑi j ⟨W, hj⟩ (hxx'.trans (map_zero _).symm), map_zero]
    · intro z
      obtain ⟨x₀, hx₀⟩ := hsurj i ⟨W, hi⟩ (θE j ⟨W, hj⟩ z)
      have hk : z - w x₀ ∈ LinearMap.ker (θE j ⟨W, hj⟩) := by
        rw [LinearMap.mem_ker, map_sub, hwθ, hx₀, sub_self]
      rw [← hexact] at hk
      obtain ⟨y, hy⟩ := hk
      refine ⟨x₀ + ϑ i ⟨W, hi⟩ y, ?_⟩
      rw [map_add, hwϑ, hy, add_sub_cancel]

  let v : ∀ (i j : K.ι), i < j → ∀ (W : P.affineOpens) (hi : W.1 ≤ K.U i) (hj : W.1 ≤ K.U j),
      M i ⟨W, hi⟩ →ₗ[A] M j ⟨W, hj⟩ :=
    fun i j h W hi hj => u i j ⟨W, hi⟩ hj - (ϑ j ⟨W, hj⟩ ∘ₗ βp i j h W hi hj ∘ₗ θE i ⟨W, hi⟩)
  have hv : ∀ (i j : K.ι) (h : i < j) (W : P.affineOpens) (hi : W.1 ≤ K.U i) (hj : W.1 ≤ K.U j) (x : M i ⟨W, hi⟩),
      v i j h W hi hj x = u i j ⟨W, hi⟩ hj x - ϑ j ⟨W, hj⟩ (βp i j h W hi hj (θE i ⟨W, hi⟩ x)) := fun _ _ _ _ _ _ _ => rfl
  clear_value v
  have hvϑ : ∀ (i j : K.ι) (h : i < j) (W : P.affineOpens) (hi : W.1 ≤ K.U i) (hj : W.1 ≤ K.U j) (y : GK.obj W.1),
      v i j h W hi hj (ϑ i ⟨W, hi⟩ y) = ϑ j ⟨W, hj⟩ y := by
    intro i j h W hi hj y
    rw [hv i j h W hi hj, huϑ' i j W hi hj y, hθEϑ, map_zero, map_zero, sub_zero]
  have hvθ : ∀ (i j : K.ι) (h : i < j) (W : P.affineOpens) (hi : W.1 ≤ K.U i) (hj : W.1 ≤ K.U j) (x : M i ⟨W, hi⟩),
      θE j ⟨W, hj⟩ (v i j h W hi hj x) = θE i ⟨W, hi⟩ x := by
    intro i j h W hi hj x
    rw [hv i j h W hi hj x, map_sub, huθE' i j W hi hj x, hθEϑ, sub_zero]
  have hvbij : ∀ (i j : K.ι) (h : i < j) (W : P.affineOpens) (hi : W.1 ≤ K.U i) (hj : W.1 ≤ K.U j),
      Function.Bijective (v i j h W hi hj) :=
    fun i j h W hi hj => hfive i j W hi hj _ (hvϑ i j h W hi hj) (hvθ i j h W hi hj)

  have hvcoc : ∀ (i j l : K.ι) (h : i < j) (h' : j < l) (W : P.affineOpens) (hi : W.1 ≤ K.U i) (hj : W.1 ≤ K.U j)
      (hl : W.1 ≤ K.U l) (x : M i ⟨W, hi⟩),
      v j l h' W hj hl (v i j h W hi hj x) = v i l (h.trans h') W hi hl x := by
    intro i j l h h' W hi hj hl x
    have k := hkey i j l h h' W hi hj hl x
    rw [hv i j h W hi hj x, (v j l h' W hj hl).map_sub, hvϑ j l h' W hj hl, hv j l h' W hj hl, hv i l (h.trans h') W hi hl x,
      huθE' i j W hi hj x]
    exact RedY1.cocAux _ _ _ _ _ k

  obtain ⟨vi, hvi_v, hv_vi⟩ : ∃ vi : ∀ (i j : K.ι), i < j → ∀ (W : P.affineOpens) (hi : W.1 ≤ K.U i) (hj : W.1 ≤ K.U j),
      M j ⟨W, hj⟩ →ₗ[A] M i ⟨W, hi⟩,
      (∀ (i j : K.ι) (h : i < j) (W : P.affineOpens) (hi : W.1 ≤ K.U i) (hj : W.1 ≤ K.U j) (x : M i ⟨W, hi⟩),
        vi i j h W hi hj (v i j h W hi hj x) = x) ∧
      (∀ (i j : K.ι) (h : i < j) (W : P.affineOpens) (hi : W.1 ≤ K.U i) (hj : W.1 ≤ K.U j) (z : M j ⟨W, hj⟩),
        v i j h W hi hj (vi i j h W hi hj z) = z) := by
    refine ⟨fun i j h W hi hj =>
        ((LinearEquiv.ofBijective (v i j h W hi hj) (hvbij i j h W hi hj)).symm : M j ⟨W, hj⟩ →ₗ[A] M i ⟨W, hi⟩), ?_, ?_⟩
    · intro i j h W hi hj x
      change (LinearEquiv.ofBijective (v i j h W hi hj) (hvbij i j h W hi hj)).symm (v i j h W hi hj x) = x
      rw [← LinearEquiv.ofBijective_apply (v i j h W hi hj) (hf := hvbij i j h W hi hj) x]
      exact LinearEquiv.symm_apply_apply _ _
    · intro i j h W hi hj z
      change v i j h W hi hj ((LinearEquiv.ofBijective (v i j h W hi hj) (hvbij i j h W hi hj)).symm z) = z
      rw [← LinearEquiv.ofBijective_apply (v i j h W hi hj) (hf := hvbij i j h W hi hj)]
      exact LinearEquiv.apply_symm_apply _ _
  have hviϑ : ∀ (i j : K.ι) (h : i < j) (W : P.affineOpens) (hi : W.1 ≤ K.U i) (hj : W.1 ≤ K.U j) (y : GK.obj W.1),
      vi i j h W hi hj (ϑ j ⟨W, hj⟩ y) = ϑ i ⟨W, hi⟩ y := by
    intro i j h W hi hj y
    apply (hvbij i j h W hi hj).1
    rw [hv_vi, hvϑ]
  have hviθ : ∀ (i j : K.ι) (h : i < j) (W : P.affineOpens) (hi : W.1 ≤ K.U i) (hj : W.1 ≤ K.U j) (z : M j ⟨W, hj⟩),
      θE i ⟨W, hi⟩ (vi i j h W hi hj z) = θE j ⟨W, hj⟩ z := by
    intro i j h W hi hj z
    conv_rhs => rw [← hv_vi i j h W hi hj z]
    rw [hvθ]

  have hvs : ∀ (i j : K.ι) (h : i < j) (W : P.affineOpens) (hi : W.1 ≤ K.U i) (hj : W.1 ≤ K.U j)
      (a : Γ(P, W.1)) (x : M i ⟨W, hi⟩),
      letI : Module Γ(P, W.1) (M i ⟨W, hi⟩) := iΓ i ⟨W, hi⟩
      letI : Module Γ(P, W.1) (M j ⟨W, hj⟩) := iΓ j ⟨W, hj⟩
      v i j h W hi hj (a • x) = a • v i j h W hi hj x := by
    intro i j h W hi hj a x
    letI : Module Γ(P, W.1) (M i ⟨W, hi⟩) := iΓ i ⟨W, hi⟩
    letI : Module Γ(P, W.1) (M j ⟨W, hj⟩) := iΓ j ⟨W, hj⟩
    rw [hv, hv, hus i j ⟨W, hi⟩ hj a x, hθEs i ⟨W, hi⟩ a x, hβps i j h W hi hj a, hϑs j ⟨W, hj⟩ a, smul_sub]
  have hvis : ∀ (i j : K.ι) (h : i < j) (W : P.affineOpens) (hi : W.1 ≤ K.U i) (hj : W.1 ≤ K.U j)
      (a : Γ(P, W.1)) (z : M j ⟨W, hj⟩),
      letI : Module Γ(P, W.1) (M i ⟨W, hi⟩) := iΓ i ⟨W, hi⟩
      letI : Module Γ(P, W.1) (M j ⟨W, hj⟩) := iΓ j ⟨W, hj⟩
      vi i j h W hi hj (a • z) = a • vi i j h W hi hj z := by
    intro i j h W hi hj a z
    letI : Module Γ(P, W.1) (M i ⟨W, hi⟩) := iΓ i ⟨W, hi⟩
    letI : Module Γ(P, W.1) (M j ⟨W, hj⟩) := iΓ j ⟨W, hj⟩
    apply (hvbij i j h W hi hj).1
    rw [hv_vi, hvs, hv_vi]
  have hvn : ∀ (i j : K.ι) (hij : i < j) (W W' : P.affineOpens) (hi : W.1 ≤ K.U i) (hj : W.1 ≤ K.U j)
      (hi' : W'.1 ≤ K.U i) (hj' : W'.1 ≤ K.U j) (h : W'.1 ≤ W.1) (x : M i ⟨W, hi⟩),
      v i j hij W' hi' hj' (res i (U := ⟨W, hi⟩) (U' := ⟨W', hi'⟩) h x) =
        res j (U := ⟨W, hj⟩) (U' := ⟨W', hj'⟩) h (v i j hij W hi hj x) := by
    intro i j hij W W' hi hj hi' hj' h x
    rw [hv, hv, map_sub (res j _), hun i j ⟨W, hi⟩ ⟨W', hi'⟩ hj h x, hθEn i ⟨W, hi⟩ ⟨W', hi'⟩ h x,
      hβpn i j hij W W' hi hj hi' hj' h, hϑn j ⟨W, hj⟩ ⟨W', hj'⟩ h]
  have hvin : ∀ (i j : K.ι) (hij : i < j) (W W' : P.affineOpens) (hi : W.1 ≤ K.U i) (hj : W.1 ≤ K.U j)
      (hi' : W'.1 ≤ K.U i) (hj' : W'.1 ≤ K.U j) (h : W'.1 ≤ W.1) (z : M j ⟨W, hj⟩),
      vi i j hij W' hi' hj' (res j (U := ⟨W, hj⟩) (U' := ⟨W', hj'⟩) h z) =
        res i (U := ⟨W, hi⟩) (U' := ⟨W', hi'⟩) h (vi i j hij W hi hj z) := by
    intro i j hij W W' hi hj hi' hj' h z
    apply (hvbij i j hij W' hi' hj').1
    rw [hv_vi, hvn i j hij W W' hi hj hi' hj' h, hv_vi]

  have hEU : ∀ (i j : K.ι) (W : P.affineOpens) (hi : W.1 ≤ K.U i) (hj : W.1 ≤ K.U j)
      (b : M i ⟨W, hi⟩ →ₗ[A] M j ⟨W, hj⟩), (∀ y, b (ϑ i ⟨W, hi⟩ y) = ϑ j ⟨W, hj⟩ y) → (∀ x, θE j ⟨W, hj⟩ (b x) = θE i ⟨W, hi⟩ x) →
      ∃! γ : GE.obj W.1 →ₗ[A] GK.obj W.1, u i j ⟨W, hi⟩ hj - b = ϑ j ⟨W, hj⟩ ∘ₗ γ ∘ₗ θE i ⟨W, hi⟩ := by
    intro i j W hi hj b hbϑ hbθ
    refine LinearMap.existsUnique_sub_eq_comp_comp_of_extension (ϑ i ⟨W, hi⟩) (θE i ⟨W, hi⟩) (ϑ j ⟨W, hj⟩) (θE j ⟨W, hj⟩)
      (hsurj _ _) (hexact _ _) (hϑi _ _) (hexact _ _) _ _ ?_ ?_
    · ext y; simp only [LinearMap.coe_comp, Function.comp_apply]; rw [huϑ', hbϑ]
    · ext y; simp only [LinearMap.coe_comp, Function.comp_apply]; rw [huθE', hbθ]
  have hdiag : ∀ (i : K.ι) (W : P.affineOpens) (hi hj : W.1 ≤ K.U i),
      ∃! γ : GE.obj W.1 →ₗ[A] GK.obj W.1,
        u i i ⟨W, hi⟩ hj - LinearMap.id = ϑ i ⟨W, hj⟩ ∘ₗ γ ∘ₗ θE i ⟨W, hi⟩ :=
    fun i W hi hj => hEU i i W hi hj LinearMap.id (fun _ => rfl) (fun _ => rfl)

  obtain ⟨βt, hβt_lt, hβt_gt, hβt_eq⟩ : ∃ βt : ∀ (i j : K.ι) (W : P.affineOpens) (hi : W.1 ≤ K.U i) (hj : W.1 ≤ K.U j),
      GE.obj W.1 →ₗ[A] GK.obj W.1,
      (∀ (i j : K.ι) (h : i < j) (W : P.affineOpens) (hi : W.1 ≤ K.U i) (hj : W.1 ≤ K.U j),
        βt i j W hi hj = βp i j h W hi hj) ∧
      (∀ (i j : K.ι) (h : j < i) (W : P.affineOpens) (hi : W.1 ≤ K.U i) (hj : W.1 ≤ K.U j),
        u i j ⟨W, hi⟩ hj - vi j i h W hj hi = ϑ j ⟨W, hj⟩ ∘ₗ βt i j W hi hj ∘ₗ θE i ⟨W, hi⟩) ∧
      (∀ (i : K.ι) (W : P.affineOpens) (hi hj : W.1 ≤ K.U i),
        u i i ⟨W, hi⟩ hj - LinearMap.id = ϑ i ⟨W, hj⟩ ∘ₗ βt i i W hi hj ∘ₗ θE i ⟨W, hi⟩) := by
    refine ⟨fun i j W hi hj =>
      if hij : i < j then βp i j hij W hi hj
      else if hji : j < i then
        (hEU i j W hi hj (vi j i hji W hj hi) (hviϑ j i hji W hj hi) (hviθ j i hji W hj hi)).exists.choose
      else (hdiag i W hi ((le_antisymm (not_lt.mp hji) (not_lt.mp hij)) ▸ hj)).exists.choose, ?_, ?_, ?_⟩
    · intro i j h W hi hj
      simp only [dif_pos h]
    · intro i j h W hi hj
      simp only [dif_neg (not_lt_of_gt h), dif_pos h]
      exact (hEU i j W hi hj (vi j i h W hj hi) (hviϑ j i h W hj hi) (hviθ j i h W hj hi)).exists.choose_spec
    · intro i W hi hj
      simp only [dif_neg (lt_irrefl i)]
      exact (hdiag i W hi hj).exists.choose_spec
  clear hdiag

  obtain ⟨u', hu'⟩ : ∃ u' : ∀ (i j : K.ι) (W : {U : P.affineOpens // U.1 ≤ K.U i}) (hj : W.1.1 ≤ K.U j),
      M i W →ₗ[A] M j ⟨W.1, hj⟩,
      ∀ (i j : K.ι) (W : P.affineOpens) (hi : W.1 ≤ K.U i) (hj : W.1 ≤ K.U j) (x : M i ⟨W, hi⟩),
        u' i j ⟨W, hi⟩ hj x = u i j ⟨W, hi⟩ hj x - ϑ j ⟨W, hj⟩ (βt i j W hi hj (θE i ⟨W, hi⟩ x)) :=
    ⟨fun i j W hj => u i j W hj - (ϑ j ⟨W.1, hj⟩ ∘ₗ βt i j W.1 W.2 hj ∘ₗ θE i W), fun _ _ _ _ _ _ => rfl⟩

  have hu'_lt : ∀ (i j : K.ι) (hij : i < j) (W : P.affineOpens) (hi : W.1 ≤ K.U i) (hj : W.1 ≤ K.U j) (x : M i ⟨W, hi⟩),
      u' i j ⟨W, hi⟩ hj x = v i j hij W hi hj x := by
    intro i j hij W hi hj x
    rw [hu', hβt_lt i j hij, hv]
  have hu'_gt : ∀ (i j : K.ι) (hji : j < i) (W : P.affineOpens) (hi : W.1 ≤ K.U i) (hj : W.1 ≤ K.U j) (x : M i ⟨W, hi⟩),
      u' i j ⟨W, hi⟩ hj x = vi j i hji W hj hi x := by
    intro i j hji W hi hj x
    have e := congrArg (fun f : M i ⟨W, hi⟩ →ₗ[A] M j ⟨W, hj⟩ => f x) (hβt_gt i j hji W hi hj)
    simp only [LinearMap.sub_apply, LinearMap.coe_comp, Function.comp_apply] at e
    rw [hu', ← e, sub_sub_cancel]
  have hu'_eq : ∀ (i : K.ι) (W : P.affineOpens) (hi hj : W.1 ≤ K.U i) (x : M i ⟨W, hi⟩), u' i i ⟨W, hi⟩ hj x = x := by
    intro i W hi hj x
    have e := congrArg (fun f : M i ⟨W, hi⟩ →ₗ[A] M i ⟨W, hj⟩ => f x) (hβt_eq i W hi hj)
    simp only [LinearMap.sub_apply, LinearMap.coe_comp, Function.comp_apply, LinearMap.id_coe, id_eq] at e
    rw [hu', ← e, sub_sub_cancel]

  have hu'ϑ : ∀ (i j : K.ι) (W : P.affineOpens) (hi : W.1 ≤ K.U i) (hj : W.1 ≤ K.U j) (y : GK.obj W.1),
      u' i j ⟨W, hi⟩ hj (ϑ i ⟨W, hi⟩ y) = ϑ j ⟨W, hj⟩ y := by
    intro i j W hi hj y
    rw [hu', huϑ' i j W hi hj, hθEϑ, map_zero, map_zero, sub_zero]
  have hu'θ : ∀ (i j : K.ι) (W : P.affineOpens) (hi : W.1 ≤ K.U i) (hj : W.1 ≤ K.U j) (x : M i ⟨W, hi⟩),
      θE j ⟨W, hj⟩ (u' i j ⟨W, hi⟩ hj x) = θE i ⟨W, hi⟩ x := by
    intro i j W hi hj x
    rw [hu', map_sub, huθE' i j W hi hj, hθEϑ, sub_zero]
  have hu'bij : ∀ (i j : K.ι) (W : P.affineOpens) (hi : W.1 ≤ K.U i) (hj : W.1 ≤ K.U j),
      Function.Bijective (u' i j ⟨W, hi⟩ hj) :=
    fun i j W hi hj => hfive i j W hi hj _ (hu'ϑ i j W hi hj) (hu'θ i j W hi hj)

  have hu's : ∀ (i j : K.ι) (W : P.affineOpens) (hi : W.1 ≤ K.U i) (hj : W.1 ≤ K.U j) (a : Γ(P, W.1))
      (x : M i ⟨W, hi⟩),
      letI : Module Γ(P, W.1) (M i ⟨W, hi⟩) := iΓ i ⟨W, hi⟩
      letI : Module Γ(P, W.1) (M j ⟨W, hj⟩) := iΓ j ⟨W, hj⟩
      u' i j ⟨W, hi⟩ hj (a • x) = a • u' i j ⟨W, hi⟩ hj x := by
    intro i j W hi hj a x
    letI : Module Γ(P, W.1) (M i ⟨W, hi⟩) := iΓ i ⟨W, hi⟩
    letI : Module Γ(P, W.1) (M j ⟨W, hj⟩) := iΓ j ⟨W, hj⟩
    rcases lt_trichotomy i j with hij | rfl | hji
    · rw [hu'_lt i j hij, hu'_lt i j hij, hvs]
    · rw [hu'_eq, hu'_eq]
    · rw [hu'_gt i j hji, hu'_gt i j hji, hvis]

  have hu'n : ∀ (i j : K.ι) (W W' : P.affineOpens) (hi : W.1 ≤ K.U i) (hj : W.1 ≤ K.U j) (hi' : W'.1 ≤ K.U i)
      (h : W'.1 ≤ W.1) (x : M i ⟨W, hi⟩),
      u' i j ⟨W', hi'⟩ (h.trans hj) (res i (U := ⟨W, hi⟩) (U' := ⟨W', hi'⟩) h x) =
        res j (U := ⟨W, hj⟩) (U' := ⟨W', h.trans hj⟩) h (u' i j ⟨W, hi⟩ hj x) := by
    intro i j W W' hi hj hi' h x
    rcases lt_trichotomy i j with hij | rfl | hji
    · rw [hu'_lt i j hij, hu'_lt i j hij]; exact hvn i j hij W W' hi hj hi' (h.trans hj) h x
    · rw [hu'_eq, hu'_eq]
    · rw [hu'_gt i j hji, hu'_gt i j hji]; exact hvin j i hji W W' hj hi (h.trans hj) hi' h x

  have hcoc : ∀ (i j l : K.ι) (W : P.affineOpens) (hi : W.1 ≤ K.U i) (hj : W.1 ≤ K.U j) (hl : W.1 ≤ K.U l)
      (x : M i ⟨W, hi⟩), u' j l ⟨W, hj⟩ hl (u' i j ⟨W, hi⟩ hj x) = u' i l ⟨W, hi⟩ hl x := by
    intro i j l W hi hj hl x
    exact RedY1.cocycle_of_regimes (ι := {i : K.ι // W.1 ≤ K.U i}) (fun i => M i.1 ⟨W, i.2⟩)
      (fun i j => u' i.1 j.1 ⟨W, i.2⟩ j.2) (fun i j h => v i.1 j.1 h W i.2 j.2) (fun i j h => vi i.1 j.1 h W i.2 j.2)
      (fun i j h x => hu'_lt i.1 j.1 h W i.2 j.2 x) (fun i j h x => hu'_gt i.1 j.1 h W i.2 j.2 x)
      (fun i x => hu'_eq i.1 W i.2 i.2 x)
      (fun i j l h h' x => hvcoc i.1 j.1 l.1 h h' W i.2 j.2 l.2 x)
      (fun i j h x => hvi_v i.1 j.1 h W i.2 j.2 x) (fun i j h z => hv_vi i.1 j.1 h W i.2 j.2 z)
      ⟨i, hi⟩ ⟨j, hj⟩ ⟨l, hl⟩ x
  refine ⟨u', ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rintro i j ⟨W, hi⟩ hj; exact hu'bij i j W hi hj
  · rintro i j ⟨W, hi⟩ hj a x; exact hu's i j W hi hj a x
  · rintro i j ⟨W, hi⟩ ⟨W', hi'⟩ hj h x; exact hu'n i j W W' hi hj hi' h x
  · rintro i j ⟨W, hi⟩ hj y; exact hu'ϑ i j W hi hj y
  · rintro i j ⟨W, hi⟩ hj x; exact hu'θ i j W hi hj x
  · rintro i j l ⟨W, hi⟩ hj hl x; exact hcoc i j l W hi hj hl x

end S_AlgebraicGeometry_OModulePresheaf_exists_cocycle_of_chartData_of_isProper_of_isAdicComplete
end P2MW
export P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_cocycle_of_chartData_of_isProper_of_isAdicComplete (solution)
