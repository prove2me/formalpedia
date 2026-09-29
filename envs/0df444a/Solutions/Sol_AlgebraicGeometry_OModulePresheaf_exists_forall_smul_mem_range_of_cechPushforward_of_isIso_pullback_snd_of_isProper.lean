-- Prove2me | solution 1 for AlgebraicGeometry.OModulePresheaf.exists_forall_smul_mem_range_of_cechPushforward_of_isIso_pullback_snd_of_isProper
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/232a2617-ab36-5356-94f1-25a2a459b481

import Mathlib
import Definitions.Def_AlgebraicGeometry_OModulePresheafIdealFiltration
import Definitions.Def_AlgebraicGeometry_OModulePresheafCechPushforward
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_forall_thread_smul_eq_apply_and_smul_eq_zero_of_isIso_pullback_snd_of_isProper
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_forall_affineOpens_thread_smul_of_forall_exists_forall_le_of_isProper
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_forall_smul_mem_range_of_forall_thread_of_cechPushforward
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_forall_smul_mem_range_of_cechPushforward_of_isIso_pullback_snd_of_isProper
p2m_attr_erase "instance" "DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I AlgebraicGeometry.ChowDatum.hι_closed AlgebraicGeometry.ChowDatumProj.hιN_closed AlgebraicGeometry.ChowDatumProj.hp_proper AlgebraicGeometry.ChowDatum.hp_isoU AlgebraicGeometry.ChowDatum.hp_proper AlgebraicGeometry.ProjSpace.algebraAway AlgebraicGeometry.ProjSpace.instIsProperProdOverπ AlgebraicGeometry.ChowDatumProj.hp_isoU AlgebraicGeometry.ProjSpace.isProper_π AlgebraicGeometry.ProjSpace.finiteType_mvPolynomial ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule"
p2m_attr_erase "simp" "DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq AlgebraicGeometry.ChowDatumProj.mk.sizeOf_spec AlgebraicGeometry.ChowDatum.mk.sizeOf_spec AlgebraicGeometry.ChowDatumProj.mk.injEq AlgebraicGeometry.ChowDatum.mk.injEq ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.mk.injEq"

set_option autoImplicit false

p2m_open "CategoryTheory AlgebraicGeometry~ChowDatum~ChowDatumProj TopologicalSpace"
open scoped TensorProduct

universe u

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

    (G' : OModulePresheaf ((g ≫ i) ≫ q)) (hG'c : G'.IsCoherent) (hG'q : G'.IsQuasicoherent)
    (ψ' : ∀ k, OModulePresheaf.AffHom G' (F' k))
    (hψ's : ∀ (k : ℕ) (V : V'.affineOpens), Function.Surjective ((ψ' k).app V))
    (hψ'k : ∀ (k : ℕ) (V : V'.affineOpens),
      LinearMap.ker ((ψ' k).app V) = I ^ (k + 1) • (⊤ : Submodule A (G'.obj V.1)))
    (hψ'c : ∀ (k : ℕ) (V : V'.affineOpens), (φ' k).app V ∘ₗ (ψ' (k + 1)).app V = (ψ' k).app V)

    (v : ∀ k, OModulePresheaf.AffHom (F k) (OModulePresheaf.cechPushforward (g ≫ i) q K' (F' k)))
    (hvη : ∀ (k : ℕ) (U₀ : P.affineOpens) (x : (F k).obj U₀.1) (j : K'.ι),
      ((v k).app U₀ x).1 j
        = η k U₀ (OModulePresheaf.AffHom.affineChart (g ≫ i) q K' U₀ j)
            (OModulePresheaf.cechPushforward.chart_le_preimage (g ≫ i) K' U₀.1 j) x)

    (Ps : ℕ → OModulePresheaf q) (hPsc : ∀ k, (Ps k).IsCoherent) (hPsq : ∀ k, (Ps k).IsQuasicoherent)
    (π : ∀ k, OModulePresheaf.AffHom (Ps (k + 1)) (Ps k))
    (hπs : ∀ (k : ℕ) (U : P.affineOpens), Function.Surjective ((π k).app U))
    (hπk : ∀ (k : ℕ) (U : P.affineOpens),
      LinearMap.ker ((π k).app U) = I ^ (k + 1) • (⊤ : Submodule A ((Ps (k + 1)).obj U.1)))
    (ψP : ∀ k, OModulePresheaf.AffHom (OModulePresheaf.cechPushforward (g ≫ i) q K' G') (Ps k))
    (hψPs : ∀ (k : ℕ) (W : P.affineOpens), Function.Surjective ((ψP k).app W))
    (hψPk : ∀ (k : ℕ) (W : P.affineOpens),
      LinearMap.ker ((ψP k).app W)
        = I ^ (k + 1) • (⊤ : Submodule A ((OModulePresheaf.cechPushforward (g ≫ i) q K' G').obj W.1)))
    (hψPc : ∀ (k : ℕ) (W : P.affineOpens), (π k).app W ∘ₗ (ψP (k + 1)).app W = (ψP k).app W)
    (ν : ∀ k, OModulePresheaf.AffHom (Ps k) (OModulePresheaf.cechPushforward (g ≫ i) q K' (F' k)))
    (hνc : ∀ (k : ℕ) (W : P.affineOpens),
      ((φ' k).cechPushforward (g ≫ i) q K').app W ∘ₗ (ν (k + 1)).app W = (ν k).app W ∘ₗ (π k).app W)
    (hνψP : ∀ (k : ℕ) (W : P.affineOpens),
      (ν k).app W ∘ₗ (ψP k).app W = ((ψ' k).cechPushforward (g ≫ i) q K').app W)
    (hνi : ∀ (W : P.affineOpens) (k : ℕ), ∃ c : ℕ,
      LinearMap.ker ((ν (k + c)).app W) ≤ I ^ (k + 1) • (⊤ : Submodule A ((Ps (k + c)).obj W.1)))
    (u : ∀ k, OModulePresheaf.AffHom (F k) (Ps k))
    (huc : ∀ (k : ℕ) (W : P.affineOpens), (π k).app W ∘ₗ (u (k + 1)).app W = (u k).app W ∘ₗ (φ k).app W)
    (hνu : ∀ (k : ℕ) (W : P.affineOpens), (ν k).app W ∘ₗ (u k).app W = (v k).app W) :
    ∃ N : ℕ,
      (∀ (k : ℕ) (W : P.affineOpens) (a : Γ(P, W.1)),
        a ∈ (Scheme.IdealSheafData.vanishingIdeal T').ideal W ^ N →
        ∀ y : (Ps k).obj W.1, ∃ x : (F k).obj W.1, (u k).app W x = a • y) ∧
      (∀ W : P.affineOpens, ∃ c : ℕ, ∀ (k : ℕ) (x : (F (k + c)).obj W.1), (u (k + c)).app W x = 0 →
        ∀ a : Γ(P, W.1), a ∈ (Scheme.IdealSheafData.vanishingIdeal T').ideal W ^ N →
          a • x ∈ I ^ (k + 1) • (⊤ : Submodule A ((F (k + c)).obj W.1))) := by
  have hloc := AlgebraicGeometry.OModulePresheaf.exists_forall_thread_smul_eq_apply_and_smul_eq_zero_of_isIso_pullback_snd_of_isProper
    I q i g K' U hU T' hT' F hFc hFq φ hφs hφk hFZ F' φ' η hηs hηV hηU hηφ hβ v hvη
  have hunif := AlgebraicGeometry.OModulePresheaf.exists_forall_affineOpens_thread_smul_of_forall_exists_forall_le_of_isProper
    I q i g K' U hU T' hT' F hFc hFq φ hφs hφk hFZ F' φ' η hηs hηV hηU hηφ hβ v hvη hloc
  exact AlgebraicGeometry.OModulePresheaf.exists_forall_smul_mem_range_of_forall_thread_of_cechPushforward
    I q i g K' U hU T' hT' F hFc hFq φ hφs hφk hFZ F' φ' η hηs hηV hηU hηφ hβ G' hG'c hG'q ψ' hψ's hψ'k hψ'c v hvη Ps hPsc hPsq π hπs hπk ψP hψPs hψPk hψPc ν hνc hνψP hνi u huc hνu hunif

end S_AlgebraicGeometry_OModulePresheaf_exists_forall_smul_mem_range_of_cechPushforward_of_isIso_pullback_snd_of_isProper
end P2MW
export P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_forall_smul_mem_range_of_cechPushforward_of_isIso_pullback_snd_of_isProper (solution)
