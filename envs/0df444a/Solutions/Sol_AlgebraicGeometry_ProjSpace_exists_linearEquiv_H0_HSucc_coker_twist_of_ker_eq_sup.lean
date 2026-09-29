-- Prove2me | solution 1 for AlgebraicGeometry.ProjSpace.exists_linearEquiv_H0_HSucc_coker_twist_of_ker_eq_sup
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/dfb41635-a353-5074-bf5f-c4c71346f5c6

import Mathlib
import Definitions.Def_AlgebraicGeometry_ProjSpace
import Definitions.Def_AlgebraicGeometry_ProjSpaceCover
import Definitions.Def_AlgebraicGeometry_ProjTwistDatum
import Definitions.Def_AlgebraicGeometry_OModulePresheafHom
import Definitions.Def_AlgebraicGeometry_OModulePresheafConstructions
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_ProjSpace_exists_linearEquiv_H0_HSucc_coker_twist_of_ker_eq_sup

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MvPolynomial

attribute [local instance] MvPolynomial.gradedAlgebra
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

universe u

namespace P2mQuotSec

section Generic

variable {R : Type*} [CommRing R]
  {M0 M1 M2 N0 N1 N2 : Type*} [AddCommGroup M0] [Module R M0] [AddCommGroup M1] [Module R M1]
  [AddCommGroup M2] [Module R M2] [AddCommGroup N0] [Module R N0] [AddCommGroup N1] [Module R N1]
  [AddCommGroup N2] [Module R N2]

noncomputable def kerEquiv (a : M0 →ₗ[R] M1) (b : N0 →ₗ[R] N1) (Φ0 : M0 →ₗ[R] N0) (Φ1 : M1 →ₗ[R] N1)
    (hcomm : Φ1 ∘ₗ a = b ∘ₗ Φ0) (h0 : Function.Bijective Φ0) (h1 : Function.Injective Φ1) :
    LinearMap.ker a ≃ₗ[R] LinearMap.ker b :=
  LinearEquiv.ofBijective
    ((Φ0 ∘ₗ (LinearMap.ker a).subtype).codRestrict (LinearMap.ker b) (fun x => by
      rw [LinearMap.mem_ker, LinearMap.comp_apply, ← LinearMap.comp_apply, ← hcomm, LinearMap.comp_apply,
        Submodule.subtype_apply, LinearMap.mem_ker.mp x.2, map_zero]))
    (by
      constructor
      · intro x y hxy
        apply Subtype.ext
        apply h0.1
        exact congrArg Subtype.val hxy
      · intro y
        obtain ⟨x, hx⟩ := h0.2 y.1
        have hxk : x ∈ LinearMap.ker a := by
          rw [LinearMap.mem_ker]
          apply h1
          rw [map_zero, ← LinearMap.comp_apply, hcomm, LinearMap.comp_apply, hx]
          exact LinearMap.mem_ker.mp y.2
        exact ⟨⟨x, hxk⟩, Subtype.ext hx⟩)

theorem kerEquiv_apply_val (a : M0 →ₗ[R] M1) (b : N0 →ₗ[R] N1) (Φ0 : M0 →ₗ[R] N0) (Φ1 : M1 →ₗ[R] N1)
    (hcomm : Φ1 ∘ₗ a = b ∘ₗ Φ0) (h0 : Function.Bijective Φ0) (h1 : Function.Injective Φ1)
    (x : LinearMap.ker a) : (kerEquiv a b Φ0 Φ1 hcomm h0 h1 x).1 = Φ0 x.1 := rfl

abbrev HQ (a0 : M0 →ₗ[R] M1) (a1 : M1 →ₗ[R] M2) : Type _ :=
  LinearMap.ker a1 ⧸ (LinearMap.range a0).comap (LinearMap.ker a1).subtype

noncomputable def HQEquiv (a0 : M0 →ₗ[R] M1) (a1 : M1 →ₗ[R] M2) (b0 : N0 →ₗ[R] N1) (b1 : N1 →ₗ[R] N2)
    (Φ0 : M0 →ₗ[R] N0) (Φ1 : M1 →ₗ[R] N1) (Φ2 : M2 →ₗ[R] N2)
    (hc0 : Φ1 ∘ₗ a0 = b0 ∘ₗ Φ0) (hc1 : Φ2 ∘ₗ a1 = b1 ∘ₗ Φ1)
    (h0 : Function.Surjective Φ0) (h1 : Function.Bijective Φ1) (h2 : Function.Injective Φ2) :
    HQ a0 a1 ≃ₗ[R] HQ b0 b1 := by

  let ψ : LinearMap.ker a1 →ₗ[R] LinearMap.ker b1 :=
    (Φ1 ∘ₗ (LinearMap.ker a1).subtype).codRestrict (LinearMap.ker b1) (fun x => by
      rw [LinearMap.mem_ker, LinearMap.comp_apply, ← LinearMap.comp_apply, ← hc1, LinearMap.comp_apply,
        Submodule.subtype_apply, LinearMap.mem_ker.mp x.2, map_zero])
  have hψ : ∀ x : LinearMap.ker a1, (ψ x).1 = Φ1 x.1 := fun _ => rfl
  refine LinearEquiv.ofBijective
    (Submodule.mapQ _ _ ψ (fun x hx => ?_)) ⟨?_, ?_⟩
  ·
    obtain ⟨y, hy⟩ := Submodule.mem_comap.mp hx
    refine Submodule.mem_comap.mpr ⟨Φ0 y, ?_⟩
    rw [Submodule.subtype_apply, hψ]
    have hy' : a0 y = x.1 := hy
    rw [← hy', ← LinearMap.comp_apply, ← hc0, LinearMap.comp_apply]
  ·
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro q hq
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    rw [LinearMap.mem_ker, Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero] at hq
    obtain ⟨z, hz⟩ := Submodule.mem_comap.mp hq
    rw [Submodule.subtype_apply, hψ] at hz
    obtain ⟨y, rfl⟩ := h0 z
    rw [Submodule.Quotient.mk_eq_zero]
    refine Submodule.mem_comap.mpr ⟨y, ?_⟩
    apply h1.1
    rw [Submodule.subtype_apply, ← hz, ← LinearMap.comp_apply, hc0, LinearMap.comp_apply]
  ·
    intro q
    obtain ⟨x', rfl⟩ := Submodule.Quotient.mk_surjective _ q
    obtain ⟨x, hx⟩ := h1.2 x'.1
    have hxk : x ∈ LinearMap.ker a1 := by
      rw [LinearMap.mem_ker]
      apply h2
      rw [map_zero, ← LinearMap.comp_apply, hc1, LinearMap.comp_apply, hx]
      exact LinearMap.mem_ker.mp x'.2
    refine ⟨Submodule.Quotient.mk ⟨x, hxk⟩, ?_⟩
    rw [Submodule.mapQ_apply]
    congr 1
    exact Subtype.ext hx

theorem HQEquiv_mk (a0 : M0 →ₗ[R] M1) (a1 : M1 →ₗ[R] M2) (b0 : N0 →ₗ[R] N1) (b1 : N1 →ₗ[R] N2)
    (Φ0 : M0 →ₗ[R] N0) (Φ1 : M1 →ₗ[R] N1) (Φ2 : M2 →ₗ[R] N2)
    (hc0 : Φ1 ∘ₗ a0 = b0 ∘ₗ Φ0) (hc1 : Φ2 ∘ₗ a1 = b1 ∘ₗ Φ1)
    (h0 : Function.Surjective Φ0) (h1 : Function.Bijective Φ1) (h2 : Function.Injective Φ2)
    (x : LinearMap.ker a1) :
    HQEquiv a0 a1 b0 b1 Φ0 Φ1 Φ2 hc0 hc1 h0 h1 h2 (Submodule.Quotient.mk x)
      = Submodule.Quotient.mk ⟨Φ1 x.1, by
          rw [LinearMap.mem_ker, ← LinearMap.comp_apply, ← hc1, LinearMap.comp_apply, LinearMap.mem_ker.mp x.2,
            map_zero]⟩ := rfl

end Generic

end P2mQuotSec

namespace P2mQuotSec

p2m_open "AlgebraicGeometry.ProjSpace AlgebraicGeometry.OModulePresheaf"

section Transport

variable {R : Type*} [CommRing R] {V : Scheme} {π : V ⟶ Spec (.of R)} (F : OModulePresheaf π)

theorem res_irrel {U₁ U₂ U₃ : V.Opens} (h₁ : U₁ ≤ U₂) (h₂ : U₂ ≤ U₃) (h₃ : U₁ ≤ U₃) (x : F.obj U₃) :
    F.res h₁ (F.res h₂ x) = F.res h₃ x := by
  rw [← LinearMap.comp_apply, ← F.res_comp]

theorem res_eq_bijective {U₁ U₂ : V.Opens} (h : U₁ = U₂) : Function.Bijective (F.res h.le) := by
  subst h
  rw [F.res_refl]
  exact Function.bijective_id

end Transport

theorem preimage_iInf_fin {X Y : Scheme} (f : X ⟶ Y) {m : ℕ} (U : Fin (m + 1) → Y.Opens) :
    f ⁻¹ᵁ (⨅ i, U i) = ⨅ i, f ⁻¹ᵁ U i := by
  classical
  rw [← Finset.inf_univ_eq_iInf, ← Finset.inf_univ_eq_iInf]
  induction (Finset.univ : Finset (Fin (m + 1))) using Finset.induction_on with
  | empty => rfl
  | insert a s _ ih => rw [Finset.inf_insert, Finset.inf_insert, Scheme.Hom.preimage_inf, ih]

end P2mQuotSec

namespace P2mQuotSec

p2m_open "AlgebraicGeometry.ProjSpace AlgebraicGeometry.OModulePresheaf HomogeneousLocalization"

section Res

variable {X Y : Scheme.{u}}

theorem restrictFun_bijective_of_le_le {W W' : X.Opens} (h : W ≤ W') (h' : W' ≤ W) :
    Function.Bijective (restrictFun h : Γ(X, W') → Γ(X, W)) :=
  Function.bijective_iff_has_inverse.2 ⟨restrictFun h',
    fun g => by rw [restrictFun_restrictFun]; exact restrictFun_refl g,
    fun g => by rw [restrictFun_restrictFun]; exact restrictFun_refl g⟩

theorem restrictFun_injective_of_le_le {W W' : X.Opens} (h : W ≤ W') (h' : W' ≤ W) {x y : Γ(X, W')}
    (e : restrictFun h x = restrictFun h y) : x = y :=
  (restrictFun_bijective_of_le_le h h').1 e

theorem app_restrictFun (f : X ⟶ Y) {W W' : Y.Opens} (h : W ≤ W') (x : Γ(Y, W')) :
    (f.app W).hom (restrictFun h x) = restrictFun (f.preimage_mono h) ((f.app W').hom x) := by
  have := CategoryTheory.ConcreteCategory.congr_hom (f.naturality (homOfLE h).op) x
  rw [CategoryTheory.ConcreteCategory.comp_apply, CategoryTheory.ConcreteCategory.comp_apply] at this
  exact this

end Res

section Principal

variable (n : ℕ) (k : Type u) [CommRing k]

local notation "𝒜" => MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k
local notation "S" => MvPolynomial (Fin (n + 1)) k

theorem X_pow_mem (i : Fin (n + 1)) (e : ℕ) : (X i : S) ^ e ∈ 𝒜 e :=
  (MvPolynomial.mem_homogeneousSubmodule e _).mpr (MvPolynomial.isHomogeneous_X_pow i e)

noncomputable def frac (i : Fin (n + 1)) (e : ℕ) (G : 𝒜 e) : Away 𝒜 (X i : S) :=
  HomogeneousLocalization.mk { deg := e, num := G, den := ⟨X i ^ e, X_pow_mem n k i e⟩, den_mem := ⟨e, rfl⟩ }

theorem frac_mul (i : Fin (n + 1)) (a b : ℕ) (G : 𝒜 a) (H : 𝒜 b) :
    frac n k i (a + b) ⟨(G : S) * (H : S), SetLike.GradedMul.mul_mem G.2 H.2⟩ = frac n k i a G * frac n k i b H := by
  apply HomogeneousLocalization.val_injective
  simp only [frac, HomogeneousLocalization.val_mul, HomogeneousLocalization.val_mk, Localization.mk_mul]
  congr 1
  exact Subtype.ext (pow_add _ _ _)

theorem frac_eq_zero (i : Fin (n + 1)) (e : ℕ) (G : 𝒜 e) (hG : (G : S) = 0) : frac n k i e G = 0 := by
  apply HomogeneousLocalization.val_injective
  simp only [frac, HomogeneousLocalization.val_zero, HomogeneousLocalization.val_mk, hG]
  exact Localization.mk_zero _

theorem frac_congr (i : Fin (n + 1)) {e : ℕ} {G H : 𝒜 e} (h : (G : S) = H) : frac n k i e G = frac n k i e H := by
  rw [Subtype.ext h]

theorem frac_mem_span (ℓ : S) (hℓ : ℓ.IsHomogeneous 1) (i : Fin (n + 1)) (d : ℕ) (G : S) (hG : G.IsHomogeneous d)
    (hGI : G ∈ Ideal.span {ℓ}) :
    Proj.awayToSection 𝒜 (X i) (frac n k i d ⟨G, (MvPolynomial.mem_homogeneousSubmodule d G).mpr hG⟩) ∈
      Ideal.span {Proj.awayToSection 𝒜 (X i) (frac n k i 1 ⟨ℓ, (MvPolynomial.mem_homogeneousSubmodule 1 ℓ).mpr hℓ⟩)} := by
  classical
  obtain ⟨H, hH⟩ := Ideal.mem_span_singleton'.mp hGI
  have hGd : (DirectSum.decompose 𝒜 G d : S) = G :=
    DirectSum.decompose_of_mem_same 𝒜 ((MvPolynomial.mem_homogeneousSubmodule d G).mpr hG)
  have hdec : (DirectSum.decompose 𝒜 G d : S) =
      if 1 ≤ d then (DirectSum.decompose 𝒜 H (d - 1) : S) * ℓ else 0 := by
    rw [← hH]; exact DirectSum.coe_decompose_mul_of_right_mem 𝒜 d ((MvPolynomial.mem_homogeneousSubmodule 1 ℓ).mpr hℓ)
  by_cases hd : 1 ≤ d
  · rw [if_pos hd] at hdec
    have key : frac n k i d ⟨G, (MvPolynomial.mem_homogeneousSubmodule d G).mpr hG⟩ =
        frac n k i (d - 1) (DirectSum.decompose 𝒜 H (d - 1)) *
          frac n k i 1 ⟨ℓ, (MvPolynomial.mem_homogeneousSubmodule 1 ℓ).mpr hℓ⟩ := by
      rw [← frac_mul]
      have : ∀ (e : ℕ) (he : e = d) (K : 𝒜 e), (K : S) = G →
          frac n k i d ⟨G, (MvPolynomial.mem_homogeneousSubmodule d G).mpr hG⟩ = frac n k i e K := by
        intro e he K hK; subst he; exact frac_congr n k i hK.symm
      exact this _ (Nat.sub_add_cancel hd) _ (by rw [← hGd, hdec])
    rw [key, map_mul]
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span rfl)
  · rw [if_neg hd] at hdec
    rw [frac_eq_zero n k i d _ (hGd.symm.trans hdec), map_zero]
    exact Ideal.zero_mem _

end Principal

section Main

variable {n : ℕ} {k : Type u} [CommRing k] {Zk Z' : Scheme.{u}}
  (ιk : Zk ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k)) (j : Z' ⟶ Zk)

local notation "𝒜" => MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k

theorem pullbackChart_comp (i : Fin (n + 1)) : pullbackChart (j ≫ ιk) i = j ⁻¹ᵁ pullbackChart ιk i := rfl

theorem frameUnit_comp (i l : Fin (n + 1)) :
    frameUnit (j ≫ ιk) i l = (j.app (pullbackChart ιk i)).hom (frameUnit ιk i l) := rfl

variable (m : ℕ)

noncomputable def resJVal (U : Zk.Opens) (g : twistObj (ιk ≫ ProjSpace.π k n) ιk m U) :
    ∀ i : Fin (n + 1), Γ(Z', (j ⁻¹ᵁ U) ⊓ pullbackChart (j ≫ ιk) i) :=
  fun i => (j.app (U ⊓ pullbackChart ιk i)).hom (g.val i)

theorem resJVal_compat (U : Zk.Opens) (g : twistObj (ιk ≫ ProjSpace.π k n) ιk m U) :
    TwistCompat (j ≫ ιk) m (j ⁻¹ᵁ U) (resJVal ιk j m U g) := by
  intro i l
  have h := congrArg (j.app ((U ⊓ pullbackChart ιk i) ⊓ pullbackChart ιk l)).hom (g.compat i l)
  rw [map_mul, map_pow, app_restrictFun, app_restrictFun, app_restrictFun] at h
  exact h

theorem app_algebraMap (U : Zk.Opens) (r : k) :
    (j.app U).hom ((Scheme.TwoAffineOpenCover.algebraOfHom (ιk ≫ ProjSpace.π k n) U).algebraMap r) =
      (Scheme.TwoAffineOpenCover.algebraOfHom ((j ≫ ιk) ≫ ProjSpace.π k n) (j ⁻¹ᵁ U)).algebraMap r := by
  rw [Scheme.TwoAffineOpenCover.algebraMap_algebraOfHom, Scheme.TwoAffineOpenCover.algebraMap_algebraOfHom]
  have h := CategoryTheory.ConcreteCategory.congr_hom
    (Scheme.Hom.appLE_comp_appLE j (ιk ≫ ProjSpace.π k n) ⊤ U (j ⁻¹ᵁ U) le_top le_rfl)
    ((Scheme.ΓSpecIso (.of k)).inv.hom r)
  rw [CategoryTheory.ConcreteCategory.comp_apply, Scheme.Hom.appLE_eq_app] at h
  exact h

noncomputable def resJ (U : Zk.Opens) :
    (twist (ιk ≫ ProjSpace.π k n) ιk m).obj U →ₗ[k] (twist ((j ≫ ιk) ≫ ProjSpace.π k n) (j ≫ ιk) m).obj (j ⁻¹ᵁ U) where
  toFun g := ⟨resJVal ιk j m U g, resJVal_compat ιk j m U g⟩
  map_add' g g' := twistObj.ext (funext fun i => by
    show (j.app _).hom (g.val i + g'.val i) = resJVal ιk j m U g i + resJVal ιk j m U g' i
    rw [map_add]; rfl)
  map_smul' r g := twistObj.ext (funext fun i => by
    show (j.app _).hom (restrictFun _ ((Scheme.TwoAffineOpenCover.algebraOfHom (ιk ≫ ProjSpace.π k n) U).algebraMap r) * g.val i)
      = restrictFun _ ((Scheme.TwoAffineOpenCover.algebraOfHom ((j ≫ ιk) ≫ ProjSpace.π k n) (j ⁻¹ᵁ U)).algebraMap r) *
          resJVal ιk j m U g i
    rw [map_mul, app_restrictFun, app_algebraMap]
    rfl)

theorem resJ_val (U : Zk.Opens) (g : (twist (ιk ≫ ProjSpace.π k n) ιk m).obj U) (i : Fin (n + 1)) :
    (resJ ιk j m U g).val i = (j.app (U ⊓ pullbackChart ιk i)).hom (g.val i) := rfl

theorem resJ_res {U U' : Zk.Opens} (h : U ≤ U') (g : (twist (ιk ≫ ProjSpace.π k n) ιk m).obj U') :
    resJ ιk j m U ((twist (ιk ≫ ProjSpace.π k n) ιk m).res h g) =
      (twist ((j ≫ ιk) ≫ ProjSpace.π k n) (j ≫ ιk) m).res (j.preimage_mono h) (resJ ιk j m U' g) := by
  refine twistObj.ext (funext fun i => ?_)
  rw [resJ_val, twist_res_val, twist_res_val, resJ_val, app_restrictFun]
  rfl

theorem resJ_smul (U : Zk.Opens) (a : Γ(Zk, U)) (g : (twist (ιk ≫ ProjSpace.π k n) ιk m).obj U) :
    resJ ιk j m U (a • g) = (j.app U).hom a • resJ ιk j m U g := by
  refine twistObj.ext (funext fun i => ?_)
  rw [resJ_val, twist_smul_val, twist_smul_val, resJ_val, map_mul, app_restrictFun]
  rfl

theorem spread_compat (i₀ : Fin (n + 1)) (W : Zk.Opens) (hW : W ≤ pullbackChart ιk i₀) (y : Γ(Zk, W)) :
    TwistCompat ιk m W (fun i =>
      restrictFun (inf_le_right : W ⊓ pullbackChart ιk i ≤ pullbackChart ιk i) (frameUnit ιk i i₀) ^ m *
        restrictFun (inf_le_left : W ⊓ pullbackChart ιk i ≤ W) y) := by
  intro i l
  simp only [map_mul, map_pow, restrictFun_restrictFun]
  have hO : (W ⊓ pullbackChart ιk i) ⊓ pullbackChart ιk l ≤ pullbackOverlap ιk i l := by
    rw [pullbackOverlap_eq_inf]; exact le_inf (inf_le_left.trans inf_le_right) inf_le_right
  have hc := congrArg (restrictFun hO) (frameUnit_cocycle ιk i l i₀)
  rw [map_mul, restrictFun_restrictFun, restrictFun_restrictFun, restrictFun_restrictFun] at hc
  have e1 : restrictFun ((inf_le_left : (W ⊓ pullbackChart ιk i) ⊓ pullbackChart ιk l ≤ _).trans inf_le_right)
      (frameUnit ιk i i₀) = restrictFun (hO.trans (pullbackOverlap_le_left ιk i l)) (frameUnit ιk i i₀) := rfl
  have e2 : restrictFun ((inf_le_left : (W ⊓ pullbackChart ιk i) ⊓ pullbackChart ιk l ≤ _).trans inf_le_left) y =
      restrictFun ((le_inf (le_trans inf_le_left inf_le_left) inf_le_right :
        (W ⊓ pullbackChart ιk i) ⊓ pullbackChart ιk l ≤ W ⊓ pullbackChart ιk l).trans inf_le_left) y := rfl
  have e3 : restrictFun (hO.trans (pullbackOverlap_le_left ιk i l)) (frameUnit ιk i l) =
      restrictFun (le_trans inf_le_left inf_le_right : (W ⊓ pullbackChart ιk i) ⊓ pullbackChart ιk l ≤ pullbackChart ιk i)
        (frameUnit ιk i l) := rfl
  have e4 : restrictFun (hO.trans (pullbackOverlap_le_right ιk i l)) (frameUnit ιk l i₀) =
      restrictFun ((le_inf (le_trans inf_le_left inf_le_left) inf_le_right :
        (W ⊓ pullbackChart ιk i) ⊓ pullbackChart ιk l ≤ W ⊓ pullbackChart ιk l).trans inf_le_right) (frameUnit ιk l i₀) := rfl
  rw [e1, ← hc, e2, e3, e4, mul_pow]
  ring

noncomputable def spread (i₀ : Fin (n + 1)) (W : Zk.Opens) (hW : W ≤ pullbackChart ιk i₀) (y : Γ(Zk, W)) :
    twistObj (ιk ≫ ProjSpace.π k n) ιk m W :=
  ⟨_, spread_compat ιk m i₀ W hW y⟩

theorem spread_val (i₀ : Fin (n + 1)) (W : Zk.Opens) (hW : W ≤ pullbackChart ιk i₀) (y : Γ(Zk, W)) (i : Fin (n + 1)) :
    (spread ιk m i₀ W hW y).val i =
      restrictFun (inf_le_right : W ⊓ pullbackChart ιk i ≤ pullbackChart ιk i) (frameUnit ιk i i₀) ^ m *
        restrictFun (inf_le_left : W ⊓ pullbackChart ιk i ≤ W) y := rfl

theorem eq_spread (i₀ : Fin (n + 1)) (W : Zk.Opens) (hW : W ≤ pullbackChart ιk i₀)
    (g : twistObj (ιk ≫ ProjSpace.π k n) ιk m W) :
    g = spread ιk m i₀ W hW (restrictFun (le_inf le_rfl hW : W ≤ W ⊓ pullbackChart ιk i₀) (g.val i₀)) := by
  refine twistObj.ext (funext fun i => ?_)
  rw [spread_val, restrictFun_restrictFun]
  have hc := g.compat i i₀

  apply restrictFun_injective_of_le_le
    (inf_le_left : (W ⊓ pullbackChart ιk i) ⊓ pullbackChart ιk i₀ ≤ W ⊓ pullbackChart ιk i)
    (le_inf le_rfl (inf_le_left.trans hW))
  rw [hc, map_mul, map_pow, restrictFun_restrictFun, restrictFun_restrictFun]

variable [IsClosedImmersion ιk] [IsClosedImmersion j]
  (ℓ : MvPolynomial (Fin (n + 1)) k) (hℓ : ℓ.IsHomogeneous 1)
  (𝓘ℓ : (Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k)).IdealSheafData)
  (h𝓘ℓ : ∀ i : Fin (n + 1),
      𝓘ℓ.ideal ⟨Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k) (MvPolynomial.X i),
        Proj.isAffineOpen_basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k) (MvPolynomial.X i)
          (ProjSpace.X_mem_one k n i) one_pos⟩ =
      Ideal.span { s | ∃ (d : ℕ) (G : MvPolynomial (Fin (n + 1)) k) (hG : G.IsHomogeneous d),
        G ∈ Ideal.span {ℓ} ∧
        s = Proj.awayToSection (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k) (MvPolynomial.X i)
            (HomogeneousLocalization.mk
              { deg := d
                num := ⟨G, (MvPolynomial.mem_homogeneousSubmodule d G).mpr hG⟩
                den := ⟨MvPolynomial.X i ^ d, (MvPolynomial.mem_homogeneousSubmodule d _).mpr (MvPolynomial.isHomogeneous_X_pow i d)⟩
                den_mem := ⟨d, rfl⟩ }) })
  (hker : (j ≫ ιk).ker = ιk.ker ⊔ 𝓘ℓ)

theorem twist_zero_val {X : Scheme.{u}} (π : X ⟶ Spec (.of k)) (φ : X ⟶ Proj 𝒜) (m : ℕ) (U : X.Opens) (i : Fin (n + 1)) :
    (0 : (twist π φ m).obj U).val i = 0 := rfl

noncomputable def tℓ (i : Fin (n + 1)) : Γ(Zk, pullbackChart ιk i) :=
  (ιk.app (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k) (MvPolynomial.X i)))
    (Proj.awayToSection (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k) (MvPolynomial.X i)
      (HomogeneousLocalization.mk
        { deg := 1
          num := ⟨ℓ, (MvPolynomial.mem_homogeneousSubmodule 1 ℓ).mpr hℓ⟩
          den := ⟨MvPolynomial.X i ^ 1, (MvPolynomial.mem_homogeneousSubmodule 1 _).mpr (MvPolynomial.isHomogeneous_X_pow i 1)⟩
          den_mem := ⟨1, rfl⟩ }))

include h𝓘ℓ hker

omit hker in

theorem ideal_𝓘ℓ_eq (i₀ : Fin (n + 1)) (V : (Proj 𝒜).affineOpens)
    (hV : (V : (Proj 𝒜).Opens) ≤ Proj.basicOpen 𝒜 (X i₀)) :
    𝓘ℓ.ideal V = Ideal.span {restrictFun hV
      (Proj.awayToSection 𝒜 (X i₀) (frac n k i₀ 1 ⟨ℓ, (MvPolynomial.mem_homogeneousSubmodule 1 ℓ).mpr hℓ⟩))} := by
  have hmap := 𝓘ℓ.map_ideal (U := V)
    (V := ⟨Proj.basicOpen 𝒜 (X i₀), Proj.isAffineOpen_basicOpen 𝒜 (X i₀) (ProjSpace.X_mem_one k n i₀) one_pos⟩) hV
  rw [← hmap, h𝓘ℓ i₀, Ideal.map_span]
  apply le_antisymm
  · refine Ideal.span_le.mpr ?_
    rintro _ ⟨s, ⟨d, G, hG, hGI, rfl⟩, rfl⟩
    have hmem := frac_mem_span n k ℓ hℓ i₀ d G hG hGI
    have := Ideal.mem_map_of_mem ((Proj 𝒜).presheaf.map (homOfLE hV).op).hom hmem
    rw [Ideal.map_span, Set.image_singleton] at this
    exact this
  · refine Ideal.span_le.mpr ?_
    rintro _ rfl
    exact Ideal.subset_span ⟨_, ⟨1, ℓ, hℓ, Ideal.subset_span rfl, rfl⟩, rfl⟩

include hker in

theorem ker_app_eq_span (i₀ : Fin (n + 1)) (V : (Proj 𝒜).affineOpens)
    (hV : (V : (Proj 𝒜).Opens) ≤ Proj.basicOpen 𝒜 (X i₀)) :
    RingHom.ker (j.app (ιk ⁻¹ᵁ (V : (Proj 𝒜).Opens))).hom =
      Ideal.span {restrictFun (ιk.preimage_mono hV : ιk ⁻¹ᵁ (V : (Proj 𝒜).Opens) ≤ pullbackChart ιk i₀) (tℓ ιk ℓ hℓ i₀)} := by

  have hsurj := ιk.app_surjective (V : (Proj 𝒜).Opens) V.2
  have hk₁ : RingHom.ker (ιk.app (V : (Proj 𝒜).Opens)).hom = ιk.ker.ideal V := (ιk.ker_apply V).symm
  have hk₂ : RingHom.ker ((j ≫ ιk).app (V : (Proj 𝒜).Opens)).hom = ιk.ker.ideal V ⊔ 𝓘ℓ.ideal V := by
    rw [← (j ≫ ιk).ker_apply V, hker]; rfl
  have hcomp : ∀ x, ((j ≫ ιk).app (V : (Proj 𝒜).Opens)).hom x =
      (j.app (ιk ⁻¹ᵁ (V : (Proj 𝒜).Opens))).hom ((ιk.app (V : (Proj 𝒜).Opens)).hom x) := fun x => rfl

  have hgen : restrictFun (ιk.preimage_mono hV : ιk ⁻¹ᵁ (V : (Proj 𝒜).Opens) ≤ pullbackChart ιk i₀) (tℓ ιk ℓ hℓ i₀) =
      (ιk.app (V : (Proj 𝒜).Opens)).hom (restrictFun hV
        (Proj.awayToSection 𝒜 (X i₀) (frac n k i₀ 1 ⟨ℓ, (MvPolynomial.mem_homogeneousSubmodule 1 ℓ).mpr hℓ⟩))) := by
    rw [app_restrictFun]; rfl
  apply le_antisymm
  · intro y hy
    obtain ⟨x, rfl⟩ := hsurj y
    have hx : x ∈ RingHom.ker ((j ≫ ιk).app (V : (Proj 𝒜).Opens)).hom := by
      rw [RingHom.mem_ker, hcomp]; exact hy
    rw [hk₂] at hx
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hx
    rw [← hk₁] at ha
    rw [map_add, show (ιk.app (V : (Proj 𝒜).Opens)).hom a = 0 from ha, zero_add]
    rw [ideal_𝓘ℓ_eq ℓ hℓ 𝓘ℓ h𝓘ℓ i₀ V hV, Ideal.mem_span_singleton'] at hb
    obtain ⟨c, rfl⟩ := hb
    rw [map_mul, ← hgen]
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span rfl)
  · rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, RingHom.mem_ker, hgen, ← hcomp]
    have hx : restrictFun hV
        (Proj.awayToSection 𝒜 (X i₀) (frac n k i₀ 1 ⟨ℓ, (MvPolynomial.mem_homogeneousSubmodule 1 ℓ).mpr hℓ⟩)) ∈
        RingHom.ker ((j ≫ ιk).app (V : (Proj 𝒜).Opens)).hom := by
      rw [hk₂]
      refine Submodule.mem_sup_right ?_
      rw [ideal_𝓘ℓ_eq ℓ hℓ 𝓘ℓ h𝓘ℓ i₀ V hV]
      exact Ideal.subset_span rfl
    exact hx

include hker in
theorem app_tℓ_eq_zero (i₀ : Fin (n + 1)) (V : (Proj 𝒜).affineOpens)
    (hV : (V : (Proj 𝒜).Opens) ≤ Proj.basicOpen 𝒜 (X i₀)) :
    (j.app (ιk ⁻¹ᵁ (V : (Proj 𝒜).Opens))).hom
      (restrictFun (ιk.preimage_mono hV : ιk ⁻¹ᵁ (V : (Proj 𝒜).Opens) ≤ pullbackChart ιk i₀) (tℓ ιk ℓ hℓ i₀)) = 0 := by
  have : restrictFun (ιk.preimage_mono hV : ιk ⁻¹ᵁ (V : (Proj 𝒜).Opens) ≤ pullbackChart ιk i₀) (tℓ ιk ℓ hℓ i₀) ∈
      RingHom.ker (j.app (ιk ⁻¹ᵁ (V : (Proj 𝒜).Opens))).hom := by
    rw [ker_app_eq_span ιk j ℓ hℓ 𝓘ℓ h𝓘ℓ hker i₀ V hV]; exact Ideal.subset_span rfl
  exact this

omit hℓ h𝓘ℓ hker in

theorem resJ_surjective (i₀ : Fin (n + 1)) (V : (Proj 𝒜).affineOpens)
    (hV : (V : (Proj 𝒜).Opens) ≤ Proj.basicOpen 𝒜 (X i₀)) :
    Function.Surjective (resJ ιk j m (ιk ⁻¹ᵁ (V : (Proj 𝒜).Opens))) := by
  intro g'
  have hW : ιk ⁻¹ᵁ (V : (Proj 𝒜).Opens) ≤ pullbackChart ιk i₀ := ιk.preimage_mono hV
  have hWaff : IsAffineOpen (ιk ⁻¹ᵁ (V : (Proj 𝒜).Opens)) := V.2.preimage ιk

  obtain ⟨y, hy⟩ := j.app_surjective (ιk ⁻¹ᵁ (V : (Proj 𝒜).Opens)) hWaff
    (restrictFun (j.preimage_mono (le_inf le_rfl hW : ιk ⁻¹ᵁ (V : (Proj 𝒜).Opens) ≤ _ ⊓ pullbackChart ιk i₀)) (g'.val i₀))
  refine ⟨spread ιk m i₀ _ hW y, ?_⟩

  rw [eq_spread (j ≫ ιk) m i₀ (j ⁻¹ᵁ ιk ⁻¹ᵁ (V : (Proj 𝒜).Opens)) (j.preimage_mono hW) g']
  refine twistObj.ext (funext fun i => ?_)
  rw [resJ_val, spread_val, spread_val, map_mul, map_pow, app_restrictFun, app_restrictFun, frameUnit_comp,
    show (j.app (ιk ⁻¹ᵁ (V : (Proj 𝒜).Opens))).hom y = _ from hy]
  simp only [restrictFun_restrictFun]
  rfl

include hker in

theorem resJ_eq_zero_iff
    (htc : ∀ i l : Fin (n + 1),
      restrictFun (inf_le_left : pullbackChart ιk i ⊓ pullbackChart ιk l ≤ pullbackChart ιk i) (tℓ ιk ℓ hℓ i)
        = restrictFun (inf_le_left : pullbackChart ιk i ⊓ pullbackChart ιk l ≤ pullbackChart ιk i) (frameUnit ιk i l) ^ 1
          * restrictFun (inf_le_right : pullbackChart ιk i ⊓ pullbackChart ιk l ≤ pullbackChart ιk l) (tℓ ιk ℓ hℓ l))
    (i₀ : Fin (n + 1)) (V : (Proj 𝒜).affineOpens) (hV : (V : (Proj 𝒜).Opens) ≤ Proj.basicOpen 𝒜 (X i₀))
    (d : ℕ) (g : (twist (ιk ≫ ProjSpace.π k n) ιk (d + 1)).obj (ιk ⁻¹ᵁ (V : (Proj 𝒜).Opens))) :
    resJ ιk j (d + 1) (ιk ⁻¹ᵁ (V : (Proj 𝒜).Opens)) g = 0 ↔
      ∃ h : (twist (ιk ≫ ProjSpace.π k n) ιk d).obj (ιk ⁻¹ᵁ (V : (Proj 𝒜).Opens)), ∀ i,
        g.val i = restrictFun (inf_le_right : ιk ⁻¹ᵁ (V : (Proj 𝒜).Opens) ⊓ pullbackChart ιk i ≤ pullbackChart ιk i)
          (tℓ ιk ℓ hℓ i) * h.val i := by
  have hW : ιk ⁻¹ᵁ (V : (Proj 𝒜).Opens) ≤ pullbackChart ιk i₀ := ιk.preimage_mono hV

  have htW : ∀ i, restrictFun (inf_le_right : (ιk ⁻¹ᵁ (V : (Proj 𝒜).Opens)) ⊓ pullbackChart ιk i ≤ pullbackChart ιk i) (tℓ ιk ℓ hℓ i) =
      restrictFun (inf_le_right : (ιk ⁻¹ᵁ (V : (Proj 𝒜).Opens)) ⊓ pullbackChart ιk i ≤ pullbackChart ιk i) (frameUnit ιk i i₀) *
        restrictFun (inf_le_left.trans hW : (ιk ⁻¹ᵁ (V : (Proj 𝒜).Opens)) ⊓ pullbackChart ιk i ≤ pullbackChart ιk i₀) (tℓ ιk ℓ hℓ i₀) := by
    intro i
    have := congrArg (restrictFun (le_inf inf_le_right (inf_le_left.trans hW) :
      (ιk ⁻¹ᵁ (V : (Proj 𝒜).Opens)) ⊓ pullbackChart ιk i ≤ pullbackChart ιk i ⊓ pullbackChart ιk i₀)) (htc i i₀)
    rw [map_mul, map_pow, pow_one, restrictFun_restrictFun, restrictFun_restrictFun, restrictFun_restrictFun] at this
    exact this
  constructor
  · intro hg

    have h0 : (j.app (ιk ⁻¹ᵁ (V : (Proj 𝒜).Opens))).hom (restrictFun (le_inf le_rfl hW : (ιk ⁻¹ᵁ (V : (Proj 𝒜).Opens)) ≤ (ιk ⁻¹ᵁ (V : (Proj 𝒜).Opens)) ⊓ pullbackChart ιk i₀) (g.val i₀)) = 0 := by
      rw [app_restrictFun, ← resJ_val ιk j (d + 1) (ιk ⁻¹ᵁ (V : (Proj 𝒜).Opens)) g i₀, hg, twist_zero_val]
      exact map_zero _
    have hmem : restrictFun (le_inf le_rfl hW : (ιk ⁻¹ᵁ (V : (Proj 𝒜).Opens)) ≤ (ιk ⁻¹ᵁ (V : (Proj 𝒜).Opens)) ⊓ pullbackChart ιk i₀) (g.val i₀) ∈
        RingHom.ker (j.app (ιk ⁻¹ᵁ (V : (Proj 𝒜).Opens))).hom := h0
    rw [ker_app_eq_span ιk j ℓ hℓ 𝓘ℓ h𝓘ℓ hker i₀ V hV, Ideal.mem_span_singleton'] at hmem
    obtain ⟨c, hc⟩ := hmem
    refine ⟨spread ιk d i₀ (ιk ⁻¹ᵁ (V : (Proj 𝒜).Opens)) hW c, fun i => ?_⟩
    rw [spread_val, htW i]

    have hgc := g.compat i i₀
    apply restrictFun_injective_of_le_le
      (inf_le_left : ((ιk ⁻¹ᵁ (V : (Proj 𝒜).Opens)) ⊓ pullbackChart ιk i) ⊓ pullbackChart ιk i₀ ≤ (ιk ⁻¹ᵁ (V : (Proj 𝒜).Opens)) ⊓ pullbackChart ιk i)
      (le_inf le_rfl (inf_le_left.trans hW))
    rw [hgc]

    have hg0 : restrictFun (le_inf (le_trans inf_le_left inf_le_left) inf_le_right :
        ((ιk ⁻¹ᵁ (V : (Proj 𝒜).Opens)) ⊓ pullbackChart ιk i) ⊓ pullbackChart ιk i₀ ≤ (ιk ⁻¹ᵁ (V : (Proj 𝒜).Opens)) ⊓ pullbackChart ιk i₀) (g.val i₀) =
        restrictFun (inf_le_left.trans inf_le_left : ((ιk ⁻¹ᵁ (V : (Proj 𝒜).Opens)) ⊓ pullbackChart ιk i) ⊓ pullbackChart ιk i₀ ≤ (ιk ⁻¹ᵁ (V : (Proj 𝒜).Opens)))
          (c * restrictFun hW (tℓ ιk ℓ hℓ i₀)) := by
      rw [show restrictFun (le_inf (le_trans inf_le_left inf_le_left) inf_le_right :
          ((ιk ⁻¹ᵁ (V : (Proj 𝒜).Opens)) ⊓ pullbackChart ιk i) ⊓ pullbackChart ιk i₀ ≤ (ιk ⁻¹ᵁ (V : (Proj 𝒜).Opens)) ⊓ pullbackChart ιk i₀) (g.val i₀) =
          restrictFun (inf_le_left.trans inf_le_left : ((ιk ⁻¹ᵁ (V : (Proj 𝒜).Opens)) ⊓ pullbackChart ιk i) ⊓ pullbackChart ιk i₀ ≤ (ιk ⁻¹ᵁ (V : (Proj 𝒜).Opens)))
            (restrictFun (le_inf le_rfl hW : (ιk ⁻¹ᵁ (V : (Proj 𝒜).Opens)) ≤ _ ⊓ pullbackChart ιk i₀) (g.val i₀))
          from (restrictFun_restrictFun _ _ _).symm, ← hc]
      rfl
    rw [hg0]
    simp only [map_mul, map_pow, restrictFun_restrictFun]
    ring
  · rintro ⟨h, hh⟩
    refine twistObj.ext (funext fun i => ?_)
    rw [resJ_val, hh i, htW i, map_mul, map_mul, twist_zero_val]
    have hz : (j.app ((ιk ⁻¹ᵁ (V : (Proj 𝒜).Opens)) ⊓ pullbackChart ιk i)).hom
        (restrictFun (inf_le_left.trans hW : (ιk ⁻¹ᵁ (V : (Proj 𝒜).Opens)) ⊓ pullbackChart ιk i ≤ pullbackChart ιk i₀)
          (tℓ ιk ℓ hℓ i₀)) = 0 := by
      rw [← restrictFun_restrictFun (inf_le_left : (ιk ⁻¹ᵁ (V : (Proj 𝒜).Opens)) ⊓ pullbackChart ιk i ≤ _) hW,
        app_restrictFun,
        show restrictFun hW (tℓ ιk ℓ hℓ i₀) =
          restrictFun (ιk.preimage_mono hV : ιk ⁻¹ᵁ (V : (Proj 𝒜).Opens) ≤ pullbackChart ιk i₀) (tℓ ιk ℓ hℓ i₀) from rfl,
        app_tℓ_eq_zero ιk j ℓ hℓ 𝓘ℓ h𝓘ℓ hker i₀ V hV, map_zero]
    rw [hz, mul_zero, zero_mul]
    rfl

omit hℓ h𝓘ℓ hker in
theorem resJ_surjective' (W : Zk.Opens) (V : (Proj 𝒜).affineOpens) (i₀ : Fin (n + 1))
    (hV : (V : (Proj 𝒜).Opens) ≤ Proj.basicOpen 𝒜 (X i₀)) (hWV : W = ιk ⁻¹ᵁ (V : (Proj 𝒜).Opens)) :
    Function.Surjective (resJ ιk j m W) := by
  subst hWV
  exact resJ_surjective ιk j m i₀ V hV

include hker in
theorem resJ_eq_zero_iff'
    (htc : ∀ i l : Fin (n + 1),
      restrictFun (inf_le_left : pullbackChart ιk i ⊓ pullbackChart ιk l ≤ pullbackChart ιk i) (tℓ ιk ℓ hℓ i)
        = restrictFun (inf_le_left : pullbackChart ιk i ⊓ pullbackChart ιk l ≤ pullbackChart ιk i) (frameUnit ιk i l) ^ 1
          * restrictFun (inf_le_right : pullbackChart ιk i ⊓ pullbackChart ιk l ≤ pullbackChart ιk l) (tℓ ιk ℓ hℓ l))
    (W : Zk.Opens) (V : (Proj 𝒜).affineOpens) (i₀ : Fin (n + 1))
    (hV : (V : (Proj 𝒜).Opens) ≤ Proj.basicOpen 𝒜 (X i₀)) (hWV : W = ιk ⁻¹ᵁ (V : (Proj 𝒜).Opens))
    (d : ℕ) (g : (twist (ιk ≫ ProjSpace.π k n) ιk (d + 1)).obj W) :
    resJ ιk j (d + 1) W g = 0 ↔
      ∃ h : (twist (ιk ≫ ProjSpace.π k n) ιk d).obj W, ∀ i,
        g.val i = restrictFun (inf_le_right : W ⊓ pullbackChart ιk i ≤ pullbackChart ιk i) (tℓ ιk ℓ hℓ i) * h.val i := by
  subst hWV
  exact resJ_eq_zero_iff ιk j ℓ hℓ 𝓘ℓ h𝓘ℓ hker htc i₀ V hV d g

end Main

section TlCocycle

variable {n : ℕ} {k : Type u} [CommRing k] {Zk : Scheme.{u}}
  (ιk : Zk ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k))
  (ℓ : MvPolynomial (Fin (n + 1)) k) (hℓ : ℓ.IsHomogeneous 1)

local notation "𝒜" => MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k
local notation "S" => MvPolynomial (Fin (n + 1)) k

theorem restrictFun_app_awayToSection_left (i l : Fin (n + 1)) (z : Away 𝒜 (X i : S)) :
    restrictFun (pullbackOverlap_le_left ιk i l)
        ((ιk.app (Proj.basicOpen 𝒜 (X i))).hom ((Proj.awayToSection 𝒜 (X i)).hom z))
      = (ιk.app (Proj.basicOpen 𝒜 (X i * X l))).hom
          ((Proj.awayToSection 𝒜 (X i * X l)).hom (awayMap 𝒜 (X_mem_one k n l) rfl z)) := by
  have h1 := congrArg (fun (ψ : CommRingCat.of (Away 𝒜 (X i : S)) ⟶ _) => ψ.hom z)
    (Proj.awayMap_awayToSection 𝒜 (X_mem_one k n l) (rfl : (X i * X l : S) = X i * X l))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at h1
  rw [h1]
  have h2 := congrArg (fun ψ => ψ.hom ((Proj.awayToSection 𝒜 (X i)).hom z))
    (ιk.naturality (homOfLE (show Proj.basicOpen 𝒜 (X i * X l : S) ≤ Proj.basicOpen 𝒜 (X i) from by
      rw [Proj.basicOpen_mul]; exact inf_le_left)).op)
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at h2
  rw [h2]
  rfl

theorem restrictFun_app_awayToSection_right (i l : Fin (n + 1)) (z : Away 𝒜 (X l : S)) :
    restrictFun (pullbackOverlap_le_right ιk i l)
        ((ιk.app (Proj.basicOpen 𝒜 (X l))).hom ((Proj.awayToSection 𝒜 (X l)).hom z))
      = (ιk.app (Proj.basicOpen 𝒜 (X i * X l))).hom
          ((Proj.awayToSection 𝒜 (X i * X l)).hom
            (awayMap 𝒜 (X_mem_one k n i) (mul_comm (X i) (X l) : (X i * X l : S) = X l * X i) z)) := by
  have h1 := congrArg (fun (ψ : CommRingCat.of (Away 𝒜 (X l : S)) ⟶ _) => ψ.hom z)
    (Proj.awayMap_awayToSection 𝒜 (X_mem_one k n i) (mul_comm (X i) (X l) : (X i * X l : S) = X l * X i))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at h1
  rw [h1]
  have h2 := congrArg (fun ψ => ψ.hom ((Proj.awayToSection 𝒜 (X l)).hom z))
    (ιk.naturality (homOfLE (show Proj.basicOpen 𝒜 (X i * X l : S) ≤ Proj.basicOpen 𝒜 (X l) from by
      rw [Proj.basicOpen_mul]; exact inf_le_right)).op)
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at h2
  rw [h2]
  rfl

theorem awayMap_tfrac (i l : Fin (n + 1)) :
    awayMap 𝒜 (X_mem_one k n l) rfl (frac n k i 1 ⟨ℓ, (MvPolynomial.mem_homogeneousSubmodule 1 ℓ).mpr hℓ⟩)
      = awayMap 𝒜 (X_mem_one k n l) rfl (ratio k n i l)
        * awayMap 𝒜 (X_mem_one k n i) (mul_comm (X i) (X l) : (X i * X l : S) = X l * X i)
            (frac n k l 1 ⟨ℓ, (MvPolynomial.mem_homogeneousSubmodule 1 ℓ).mpr hℓ⟩) := by
  apply HomogeneousLocalization.val_injective
  rw [HomogeneousLocalization.val_mul,
    val_awayMap_ratio k n i l l (X_mem_one k n l) rfl _ ℓ (by rw [frac, HomogeneousLocalization.val_mk]),
    val_awayMap_ratio k n i l l (X_mem_one k n l) rfl _ (X l) (by rw [ratio, Away.val_mk]),
    val_awayMap_ratio k n i l l (X_mem_one k n i) (mul_comm (X i) (X l)) _ ℓ (by rw [frac, HomogeneousLocalization.val_mk]),
    Localization.mk_mul, Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  refine ⟨1, ?_⟩
  simp only [OneMemClass.coe_one, one_mul, Submonoid.coe_mul]
  ring

theorem tℓ_cocycle (i l : Fin (n + 1)) :
    restrictFun (inf_le_left : pullbackChart ιk i ⊓ pullbackChart ιk l ≤ pullbackChart ιk i) (tℓ ιk ℓ hℓ i)
      = restrictFun (inf_le_left : pullbackChart ιk i ⊓ pullbackChart ιk l ≤ pullbackChart ιk i) (frameUnit ιk i l) ^ 1
        * restrictFun (inf_le_right : pullbackChart ιk i ⊓ pullbackChart ιk l ≤ pullbackChart ιk l) (tℓ ιk ℓ hℓ l) := by

  have hO : restrictFun (pullbackOverlap_le_left ιk i l) (tℓ ιk ℓ hℓ i)
      = restrictFun (pullbackOverlap_le_left ιk i l) (frameUnit ιk i l)
        * restrictFun (pullbackOverlap_le_right ιk i l) (tℓ ιk ℓ hℓ l) := by
    have e1 : restrictFun (pullbackOverlap_le_left ιk i l) (tℓ ιk ℓ hℓ i) =
        restrictFun (pullbackOverlap_le_left ιk i l) ((ιk.app (Proj.basicOpen 𝒜 (X i))).hom
          ((Proj.awayToSection 𝒜 (X i)).hom (frac n k i 1 ⟨ℓ, (MvPolynomial.mem_homogeneousSubmodule 1 ℓ).mpr hℓ⟩))) := rfl
    have e2 : restrictFun (pullbackOverlap_le_right ιk i l) (tℓ ιk ℓ hℓ l) =
        restrictFun (pullbackOverlap_le_right ιk i l) ((ιk.app (Proj.basicOpen 𝒜 (X l))).hom
          ((Proj.awayToSection 𝒜 (X l)).hom (frac n k l 1 ⟨ℓ, (MvPolynomial.mem_homogeneousSubmodule 1 ℓ).mpr hℓ⟩))) := rfl
    rw [e1, e2, restrictFun_frameUnit_left, restrictFun_app_awayToSection_left, restrictFun_app_awayToSection_right,
      awayMap_tfrac ℓ hℓ i l, map_mul, map_mul]
    rfl
  have hle : pullbackChart ιk i ⊓ pullbackChart ιk l ≤ pullbackOverlap ιk i l := (pullbackOverlap_eq_inf ιk i l).symm.le
  have := congrArg (restrictFun hle) hO
  rw [map_mul, restrictFun_restrictFun, restrictFun_restrictFun, restrictFun_restrictFun] at this
  rw [pow_one]
  exact this

end TlCocycle

end P2mQuotSec

namespace P2mQuotSec

p2m_open "AlgebraicGeometry.ProjSpace AlgebraicGeometry.OModulePresheaf"

section Cech

variable {k : Type} [CommRing k] {n : ℕ} {Zk Z' : Scheme.{0}}
  (ιk : Zk ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k)) [IsClosedImmersion ιk]
  (j : Z' ⟶ Zk) [IsClosedImmersion j] (d : ℕ)
  (μ : Hom (twist (ιk ≫ ProjSpace.π k n) ιk d) (twist (ιk ≫ ProjSpace.π k n) ιk (d + 1)))
  (resJ : ∀ U : Zk.Opens, (twist (ιk ≫ ProjSpace.π k n) ιk (d + 1)).obj U →ₗ[k]
    (twist ((j ≫ ιk) ≫ ProjSpace.π k n) (j ≫ ιk) (d + 1)).obj (j ⁻¹ᵁ U))
  (resJ_res : ∀ {U U' : Zk.Opens} (h : U ≤ U') (g : (twist (ιk ≫ ProjSpace.π k n) ιk (d + 1)).obj U'),
    resJ U ((twist (ιk ≫ ProjSpace.π k n) ιk (d + 1)).res h g)
      = (twist ((j ≫ ιk) ≫ ProjSpace.π k n) (j ≫ ιk) (d + 1)).res (show j ⁻¹ᵁ U ≤ j ⁻¹ᵁ U' from fun _ hx => h hx)
          (resJ U' g))
  (resJ_μ : ∀ (U : Zk.Opens) (x : (twist (ιk ≫ ProjSpace.π k n) ιk d).obj U), resJ U (μ.app U x) = 0)
  (hsurj : ∀ (W : Zk.Opens) (V : (Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k)).affineOpens)
    (i₀ : Fin (n + 1)), V.1 ≤ Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k) (MvPolynomial.X i₀) →
    W = ιk ⁻¹ᵁ V.1 → Function.Surjective (resJ W))
  (hker : ∀ (W : Zk.Opens) (V : (Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k)).affineOpens)
    (i₀ : Fin (n + 1)), V.1 ≤ Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k) (MvPolynomial.X i₀) →
    W = ιk ⁻¹ᵁ V.1 → ∀ g, resJ W g = 0 → g ∈ LinearMap.range (μ.app W))

local notation "F" => twist (ιk ≫ ProjSpace.π k n) ιk (d + 1)
local notation "F'" => twist ((j ≫ ιk) ≫ ProjSpace.π k n) (j ≫ ιk) (d + 1)
local notation "Q" => OModulePresheaf.coker μ
local notation "K" => ProjSpace.stdCoverPullback ιk
local notation "K'" => ProjSpace.stdCoverPullback (j ≫ ιk)
local notation "K₀" => ProjSpace.stdCover k n

theorem K'_inter {i : ℕ} (s : (K).Idx i) : (K').inter s = j ⁻¹ᵁ ((K).inter s) := by
  show (⨅ m, (K').U (s.1 m)) = j ⁻¹ᵁ (⨅ m, (K).U (s.1 m))
  rw [preimage_iInf_fin]
  rfl

theorem K_inter {i : ℕ} (s : (K).Idx i) : (K).inter s = ιk ⁻¹ᵁ ((K₀).inter s) := by
  show (⨅ m, (K).U (s.1 m)) = ιk ⁻¹ᵁ (⨅ m, (K₀).U (s.1 m))
  rw [preimage_iInf_fin]
  rfl

noncomputable def σ (W : Zk.Opens) : (Q).obj W →ₗ[k] (F').obj (j ⁻¹ᵁ W) :=
  (LinearMap.range (μ.app W)).liftQ (resJ W) (by
    rintro _ ⟨x, rfl⟩
    exact resJ_μ W x)

theorem σ_mk (W : Zk.Opens) (g : (F).obj W) :
    σ ιk j d μ resJ resJ_μ W (Submodule.Quotient.mk g) = resJ W g := rfl

include resJ_res in
theorem σ_res {W W' : Zk.Opens} (h : W ≤ W') (q : (Q).obj W') :
    σ ιk j d μ resJ resJ_μ W ((Q).res h q)
      = (F').res (show j ⁻¹ᵁ W ≤ j ⁻¹ᵁ W' from fun _ hx => h hx) (σ ιk j d μ resJ resJ_μ W' q) := by
  obtain ⟨g, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  rw [coker_res_mk, σ_mk, σ_mk, resJ_res]

noncomputable def T {i : ℕ} (s : (K).Idx i) : (Q).obj ((K).inter s) →ₗ[k] (F').obj ((K').inter s) :=
  (F').res (K'_inter ιk j s).le ∘ₗ σ ιk j d μ resJ resJ_μ ((K).inter s)

include resJ_res in
theorem T_res {i i' : ℕ} (s : (K).Idx i) (s' : (K).Idx i') (h : (K).inter s ≤ (K).inter s')
    (h' : (K').inter s ≤ (K').inter s') (q : (Q).obj ((K).inter s')) :
    T ιk j d μ resJ resJ_μ s ((Q).res h q) = (F').res h' (T ιk j d μ resJ resJ_μ s' q) := by
  simp only [T, LinearMap.comp_apply]
  rw [σ_res ιk j d μ resJ resJ_res resJ_μ h,
    res_irrel (F') _ _ ((K'_inter ιk j s).le.trans (show j ⁻¹ᵁ (K).inter s ≤ j ⁻¹ᵁ (K).inter s' from fun _ hx => h hx)),
    res_irrel (F') _ _ ((K'_inter ιk j s).le.trans (show j ⁻¹ᵁ (K).inter s ≤ j ⁻¹ᵁ (K).inter s' from fun _ hx => h hx))]

include hsurj hker in
theorem T_bijective {i : ℕ} (s : (K).Idx i) : Function.Bijective (T ιk j d μ resJ resJ_μ s) := by
  haveI : IsSeparated (ProjSpace.π k n) := inferInstance
  have hV : IsAffineOpen ((K₀).inter s) := (K₀).isAffineOpen_inter (ProjSpace.π k n) s
  have hle : (K₀).inter s ≤ Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k) (MvPolynomial.X (s.1 0).down) :=
    (K₀).inter_le s 0
  have hW : (K).inter s = ιk ⁻¹ᵁ ((K₀).inter s) := K_inter ιk s
  refine (res_eq_bijective (F') (K'_inter ιk j s)).comp ⟨?_, ?_⟩
  ·
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro q hq
    obtain ⟨g, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    rw [LinearMap.mem_ker, σ_mk] at hq
    exact (Submodule.Quotient.mk_eq_zero _).mpr (hker _ ⟨_, hV⟩ _ hle hW g hq)
  · intro y
    obtain ⟨g, hg⟩ := hsurj _ ⟨_, hV⟩ _ hle hW y
    exact ⟨Submodule.Quotient.mk g, by rw [σ_mk, hg]⟩

noncomputable def Φ (i : ℕ) : (Q).cochain (K) i →ₗ[k] (F').cochain (K') i :=
  LinearMap.pi fun s => T ιk j d μ resJ resJ_μ s ∘ₗ LinearMap.proj s

theorem Φ_apply (i : ℕ) (c : (Q).cochain (K) i) (s : (K).Idx i) :
    Φ ιk j d μ resJ resJ_μ i c s = T ιk j d μ resJ resJ_μ s (c s) := rfl

include hsurj hker in
theorem Φ_bijective (i : ℕ) : Function.Bijective (Φ ιk j d μ resJ resJ_μ i) := by
  constructor
  · intro c c' h
    funext s
    exact (T_bijective ιk j d μ resJ resJ_μ hsurj hker s).1 (by rw [← Φ_apply, ← Φ_apply, h])
  · intro c'
    refine ⟨fun s => (T_bijective ιk j d μ resJ resJ_μ hsurj hker s).2 (c' s) |>.choose, funext fun s => ?_⟩
    rw [Φ_apply]
    exact ((T_bijective ιk j d μ resJ resJ_μ hsurj hker s).2 (c' s)).choose_spec

include resJ_res in
theorem Φ_comm (i : ℕ) :
    Φ ιk j d μ resJ resJ_μ (i + 1) ∘ₗ (Q).d (K) i = (F').d (K') i ∘ₗ Φ ιk j d μ resJ resJ_μ i := by
  refine LinearMap.ext fun c => funext fun s => ?_
  rw [LinearMap.comp_apply, LinearMap.comp_apply, Φ_apply, OModulePresheaf.d_apply, OModulePresheaf.d_apply, map_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [map_zsmul, Φ_apply]
  congr 1
  exact T_res ιk j d μ resJ resJ_res resJ_μ s ((K).face s m) ((K).inter_le_inter_face s m)
    ((K').inter_le_inter_face s m) (c ((K).face s m))

noncomputable def e₀ : (Q).H0 (K) ≃ₗ[k] (F').H0 (K') :=
  kerEquiv ((Q).d (K) 0) ((F').d (K') 0) (Φ ιk j d μ resJ resJ_μ 0) (Φ ιk j d μ resJ resJ_μ 1)
    (Φ_comm ιk j d μ resJ resJ_res resJ_μ 0) (Φ_bijective ιk j d μ resJ resJ_μ hsurj hker 0)
    (Φ_bijective ιk j d μ resJ resJ_μ hsurj hker 1).1

noncomputable def eS (i : ℕ) : (Q).HSucc (K) i ≃ₗ[k] (F').HSucc (K') i :=
  HQEquiv ((Q).d (K) i) ((Q).d (K) (i + 1)) ((F').d (K') i) ((F').d (K') (i + 1))
    (Φ ιk j d μ resJ resJ_μ i) (Φ ιk j d μ resJ resJ_μ (i + 1)) (Φ ιk j d μ resJ resJ_μ (i + 2))
    (Φ_comm ιk j d μ resJ resJ_res resJ_μ i) (Φ_comm ιk j d μ resJ resJ_res resJ_μ (i + 1))
    (Φ_bijective ιk j d μ resJ resJ_μ hsurj hker i).2 (Φ_bijective ιk j d μ resJ resJ_μ hsurj hker (i + 1))
    (Φ_bijective ιk j d μ resJ resJ_μ hsurj hker (i + 2)).1

theorem e₀_val (c : (Q).H0 (K)) (s : (K').Idx 0) :
    (e₀ ιk j d μ resJ resJ_res resJ_μ hsurj hker c).1 s = T ιk j d μ resJ resJ_μ s (c.1 s) := rfl

theorem e₀_proj_val (c : (F).cochain (K) 0) (hc : c ∈ (F).H0 (K)) (s : (K').Idx 0) (i : Fin (n + 1))
    (h : (K').inter s ⊓ pullbackChart (j ≫ ιk) i ≤ j ⁻¹ᵁ ((K).inter s) ⊓ pullbackChart (j ≫ ιk) i) :
    ((e₀ ιk j d μ resJ resJ_res resJ_μ hsurj hker
        ((OModulePresheaf.imCokerSES μ).proj.toAffHom.H0Map (K) ⟨c, hc⟩)).1 s).val i
      = ProjSpace.restrictFun h ((resJ ((K).inter s) (c s)).val i) := rfl

end Cech

end P2mQuotSec

theorem solution
    (n : ℕ) (k : Type) [CommRing k]
    (Zk : Scheme.{0}) (ιk : Zk ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k)) [IsClosedImmersion ιk]
    (ℓ : MvPolynomial (Fin (n + 1)) k) (hℓ : ℓ.IsHomogeneous 1)
    (hnzd : ∀ (i : Fin (n + 1)) (t : Γ(Zk, ιk ⁻¹ᵁ Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k) (MvPolynomial.X i))),
      (ιk.app (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k) (MvPolynomial.X i))
        (Proj.awayToSection (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k) (MvPolynomial.X i)
          (HomogeneousLocalization.mk
            { deg := 1
              num := ⟨ℓ, (MvPolynomial.mem_homogeneousSubmodule 1 ℓ).mpr hℓ⟩
              den := ⟨MvPolynomial.X i ^ 1, (MvPolynomial.mem_homogeneousSubmodule 1 _).mpr (MvPolynomial.isHomogeneous_X_pow i 1)⟩
              den_mem := ⟨1, rfl⟩ }))) * t = 0 → t = 0)
    (𝓘ℓ : (Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k)).IdealSheafData)
    (h𝓘ℓ : (∀ i : Fin (n + 1),
        𝓘ℓ.ideal ⟨Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k) (MvPolynomial.X i),
          Proj.isAffineOpen_basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k) (MvPolynomial.X i) (ProjSpace.X_mem_one k n i) one_pos⟩ =
        Ideal.span { s | ∃ (d : ℕ) (G : MvPolynomial (Fin (n + 1)) k) (hG : G.IsHomogeneous d),
          G ∈ Ideal.span {ℓ} ∧
          s = Proj.awayToSection (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k) (MvPolynomial.X i)
              (HomogeneousLocalization.mk
                { deg := d
                  num := ⟨G, (MvPolynomial.mem_homogeneousSubmodule d G).mpr hG⟩
                  den := ⟨MvPolynomial.X i ^ d, (MvPolynomial.mem_homogeneousSubmodule d _).mpr (MvPolynomial.isHomogeneous_X_pow i d)⟩
                  den_mem := ⟨d, rfl⟩ }) }))
    (Z' : Scheme.{0}) (ι' : Z' ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k)) [IsClosedImmersion ι']
    (hker : ι'.ker = ιk.ker ⊔ 𝓘ℓ) (d : ℕ)
    (htc : ∀ i j : Fin (n + 1),
      ProjSpace.restrictFun (inf_le_left : ProjSpace.pullbackChart ιk i ⊓ ProjSpace.pullbackChart ιk j ≤ _)
          ((ιk.app (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k) (MvPolynomial.X i)))
            (Proj.awayToSection (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k) (MvPolynomial.X i)
              (HomogeneousLocalization.mk
                { deg := 1
                  num := ⟨ℓ, (MvPolynomial.mem_homogeneousSubmodule 1 ℓ).mpr hℓ⟩
                  den := ⟨MvPolynomial.X i ^ 1, (MvPolynomial.mem_homogeneousSubmodule 1 _).mpr (MvPolynomial.isHomogeneous_X_pow i 1)⟩
                  den_mem := ⟨1, rfl⟩ })))
        = ProjSpace.restrictFun (inf_le_left : ProjSpace.pullbackChart ιk i ⊓ ProjSpace.pullbackChart ιk j ≤ _)
            (ProjSpace.frameUnit ιk i j) ^ 1
          * ProjSpace.restrictFun (inf_le_right : ProjSpace.pullbackChart ιk i ⊓ ProjSpace.pullbackChart ιk j ≤ _)
          ((ιk.app (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k) (MvPolynomial.X j)))
            (Proj.awayToSection (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k) (MvPolynomial.X j)
              (HomogeneousLocalization.mk
                { deg := 1
                  num := ⟨ℓ, (MvPolynomial.mem_homogeneousSubmodule 1 ℓ).mpr hℓ⟩
                  den := ⟨MvPolynomial.X j ^ 1, (MvPolynomial.mem_homogeneousSubmodule 1 _).mpr (MvPolynomial.isHomogeneous_X_pow j 1)⟩
                  den_mem := ⟨1, rfl⟩ }))))
    (μ : OModulePresheaf.Hom (ProjSpace.twist (ιk ≫ ProjSpace.π k n) ιk d)
      (ProjSpace.twist (ιk ≫ ProjSpace.π k n) ιk (d + 1)))
    (hμ : ∀ (U : Zk.Opens) (g : (ProjSpace.twist (ιk ≫ ProjSpace.π k n) ιk d).obj U) (i : Fin (n + 1)),
      (μ.app U g).val i
        = ProjSpace.restrictFun (inf_le_right : U ⊓ ProjSpace.pullbackChart ιk i ≤ _)
          ((ιk.app (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k) (MvPolynomial.X i)))
            (Proj.awayToSection (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k) (MvPolynomial.X i)
              (HomogeneousLocalization.mk
                { deg := 1
                  num := ⟨ℓ, (MvPolynomial.mem_homogeneousSubmodule 1 ℓ).mpr hℓ⟩
                  den := ⟨MvPolynomial.X i ^ 1, (MvPolynomial.mem_homogeneousSubmodule 1 _).mpr (MvPolynomial.isHomogeneous_X_pow i 1)⟩
                  den_mem := ⟨1, rfl⟩ }))) * g.val i) :
    ∃ (e₀ : (OModulePresheaf.coker μ).H0 (ProjSpace.stdCoverPullback ιk) ≃ₗ[k]
        (ProjSpace.twist (ι' ≫ ProjSpace.π k n) ι' (d + 1)).H0 (ProjSpace.stdCoverPullback ι'))
      (_e : ∀ i : ℕ, (OModulePresheaf.coker μ).HSucc (ProjSpace.stdCoverPullback ιk) i ≃ₗ[k]
        (ProjSpace.twist (ι' ≫ ProjSpace.π k n) ι' (d + 1)).HSucc (ProjSpace.stdCoverPullback ι') i),
      ∀ (c : (ProjSpace.twist (ιk ≫ ProjSpace.π k n) ιk (d + 1)).cochain (ProjSpace.stdCoverPullback ιk) 0)
        (hc : c ∈ (ProjSpace.twist (ιk ≫ ProjSpace.π k n) ιk (d + 1)).H0 (ProjSpace.stdCoverPullback ιk))
        (G : MvPolynomial (Fin (n + 1)) k) (hG : G.IsHomogeneous (d + 1)),
          (∀ (s : (ProjSpace.stdCoverPullback ιk).Idx 0) (i : Fin (n + 1)),
            (c s).val i =
              ProjSpace.restrictFun
                (inf_le_right : (ProjSpace.stdCoverPullback ιk).inter s ⊓ ProjSpace.pullbackChart ιk i ≤
                  ProjSpace.pullbackChart ιk i)
                (ιk.app (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k) (MvPolynomial.X i))
              (Proj.awayToSection (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k) (MvPolynomial.X i)
                (HomogeneousLocalization.mk
                  { deg := d + 1
                    num := ⟨G, (MvPolynomial.mem_homogeneousSubmodule (d + 1) G).mpr hG⟩
                    den := ⟨MvPolynomial.X i ^ (d + 1), (MvPolynomial.mem_homogeneousSubmodule (d + 1) _).mpr
                      (MvPolynomial.isHomogeneous_X_pow i (d + 1))⟩
                    den_mem := ⟨d + 1, rfl⟩ })))) →
          ∀ (s : (ProjSpace.stdCoverPullback ι').Idx 0) (i : Fin (n + 1)),
            ((e₀ ((OModulePresheaf.imCokerSES μ).proj.toAffHom.H0Map (ProjSpace.stdCoverPullback ιk) ⟨c, hc⟩)).1 s).val i =
              ProjSpace.restrictFun
                (inf_le_right : (ProjSpace.stdCoverPullback ι').inter s ⊓ ProjSpace.pullbackChart ι' i ≤
                  ProjSpace.pullbackChart ι' i)
                (ι'.app (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k) (MvPolynomial.X i))
              (Proj.awayToSection (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k) (MvPolynomial.X i)
                (HomogeneousLocalization.mk
                  { deg := d + 1
                    num := ⟨G, (MvPolynomial.mem_homogeneousSubmodule (d + 1) G).mpr hG⟩
                    den := ⟨MvPolynomial.X i ^ (d + 1), (MvPolynomial.mem_homogeneousSubmodule (d + 1) _).mpr
                      (MvPolynomial.isHomogeneous_X_pow i (d + 1))⟩
                    den_mem := ⟨d + 1, rfl⟩ }))) := by
  classical

  obtain ⟨j, hj⟩ : ∃ j : Z' ⟶ Zk, j ≫ ιk = ι' :=
    ⟨IsClosedImmersion.lift ιk ι' (hker ▸ le_sup_left), IsClosedImmersion.lift_fac _ _ _⟩
  subst hj
  haveI : IsClosedImmersion j := IsClosedImmersion.of_comp_isClosedImmersion j ιk

  have resJ_μ : ∀ (U : Zk.Opens) (x : (ProjSpace.twist (ιk ≫ ProjSpace.π k n) ιk d).obj U),
      P2mQuotSec.resJ ιk j (d + 1) U (μ.app U x) = 0 := by
    intro U x
    refine ProjSpace.twistObj.ext (funext fun i => ?_)
    have hV : IsAffineOpen (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k) (MvPolynomial.X i)) :=
      (ProjSpace.stdCover k n).isAffineOpen ⟨i⟩
    have h0 := P2mQuotSec.app_tℓ_eq_zero ιk j ℓ hℓ 𝓘ℓ h𝓘ℓ hker i ⟨_, hV⟩ le_rfl
    have h0' : (j.app (ProjSpace.pullbackChart ιk i)).hom
        (ProjSpace.restrictFun (le_refl (ProjSpace.pullbackChart ιk i)) (P2mQuotSec.tℓ ιk ℓ hℓ i)) = 0 := h0
    rw [ProjSpace.restrictFun_refl] at h0'
    have h1 : (j.app (U ⊓ ProjSpace.pullbackChart ιk i)).hom
        (ProjSpace.restrictFun (inf_le_right : U ⊓ ProjSpace.pullbackChart ιk i ≤ ProjSpace.pullbackChart ιk i)
          (P2mQuotSec.tℓ ιk ℓ hℓ i)) = 0 := by
      rw [P2mQuotSec.app_restrictFun, h0', map_zero]
    rw [P2mQuotSec.resJ_val, hμ, map_mul, P2mQuotSec.twist_zero_val]
    change (j.app (U ⊓ ProjSpace.pullbackChart ιk i)).hom
        (ProjSpace.restrictFun (inf_le_right : U ⊓ ProjSpace.pullbackChart ιk i ≤ ProjSpace.pullbackChart ιk i)
          (P2mQuotSec.tℓ ιk ℓ hℓ i)) * _ = 0
    rw [h1, zero_mul]
  have hsurj : ∀ (W : Zk.Opens) (V : (Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k)).affineOpens)
      (i₀ : Fin (n + 1)), V.1 ≤ Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k) (MvPolynomial.X i₀) →
      W = ιk ⁻¹ᵁ V.1 → Function.Surjective (P2mQuotSec.resJ ιk j (d + 1) W) :=
    fun W V i₀ hV hW => P2mQuotSec.resJ_surjective' ιk j (d + 1) W V i₀ hV hW
  have hker' : ∀ (W : Zk.Opens) (V : (Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k)).affineOpens)
      (i₀ : Fin (n + 1)), V.1 ≤ Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k) (MvPolynomial.X i₀) →
      W = ιk ⁻¹ᵁ V.1 → ∀ g, P2mQuotSec.resJ ιk j (d + 1) W g = 0 → g ∈ LinearMap.range (μ.app W) := by
    intro W V i₀ hV hW g hg
    obtain ⟨h, hh⟩ := (P2mQuotSec.resJ_eq_zero_iff' ιk j ℓ hℓ 𝓘ℓ h𝓘ℓ hker htc W V i₀ hV hW d g).mp hg
    refine ⟨h, ProjSpace.twistObj.ext (funext fun i => ?_)⟩
    rw [hμ]
    exact (hh i).symm
  refine ⟨P2mQuotSec.e₀ ιk j d μ (P2mQuotSec.resJ ιk j (d + 1)) (fun h g => P2mQuotSec.resJ_res ιk j (d + 1) h g)
      resJ_μ hsurj hker',
    fun i => P2mQuotSec.eS ιk j d μ (P2mQuotSec.resJ ιk j (d + 1)) (fun h g => P2mQuotSec.resJ_res ιk j (d + 1) h g)
      resJ_μ hsurj hker' i, ?_⟩
  intro c hc G hG hcG s i
  rw [P2mQuotSec.e₀_proj_val ιk j d μ (P2mQuotSec.resJ ιk j (d + 1)) (fun h g => P2mQuotSec.resJ_res ιk j (d + 1) h g)
      resJ_μ hsurj hker' c hc s i (inf_le_inf_right _ (P2mQuotSec.K'_inter ιk j s).le),
    P2mQuotSec.resJ_val, hcG s i, P2mQuotSec.app_restrictFun]
  refine (ProjSpace.restrictFun_restrictFun _ _ _).trans ?_
  rfl

end S_AlgebraicGeometry_ProjSpace_exists_linearEquiv_H0_HSucc_coker_twist_of_ker_eq_sup
end P2MW
export P2MW.S_AlgebraicGeometry_ProjSpace_exists_linearEquiv_H0_HSucc_coker_twist_of_ker_eq_sup (solution)
