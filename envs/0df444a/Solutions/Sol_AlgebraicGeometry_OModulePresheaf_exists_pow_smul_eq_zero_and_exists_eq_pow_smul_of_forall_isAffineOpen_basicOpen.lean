-- Prove2me | solution 1 for AlgebraicGeometry.OModulePresheaf.exists_pow_smul_eq_zero_and_exists_eq_pow_smul_of_forall_isAffineOpen_basicOpen
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/47ea2dc8-b03d-53e9-9521-f53157d00947

import Mathlib
import Definitions.Def_AlgebraicGeometry_OModulePresheafIdealFiltration
import Definitions.Def_AlgebraicGeometry_OModulePresheafCechPushforward
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_bijective_cechPushforward_of_isAffineOpen_preimage
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_pow_smul_eq_zero_and_exists_eq_pow_smul_of_forall_isAffineOpen_basicOpen

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry TopologicalSpace
open scoped TensorProduct

universe u

noncomputable section

namespace K72W5b

theorem sheafAffine {R : Type u} [CommRing R] {Y : Scheme.{u}} (q : Y ⟶ Spec (CommRingCat.of R)) [IsSeparated q]
    {pq : Y ⟶ Spec (CommRingCat.of R)} (hpq : 𝟙 Y ≫ q = pq)
    (G : OModulePresheaf pq) (hqc : G.IsQuasicoherent) (K : Y.OrderedAffineCover) (Wa : Y.affineOpens) :
    (∀ x y : G.obj Wa.1,
      (∀ j : K.ι, G.res (inf_le_right : K.U j ⊓ Wa.1 ≤ Wa.1) x = G.res (inf_le_right : K.U j ⊓ Wa.1 ≤ Wa.1) y) →
        x = y) ∧
    ∀ c : ∀ j : K.ι, G.obj (K.U j ⊓ Wa.1),
      (∀ j j' : K.ι, G.res (inf_le_left : (K.U j ⊓ Wa.1) ⊓ (K.U j' ⊓ Wa.1) ≤ K.U j ⊓ Wa.1) (c j)
        = G.res (inf_le_right : (K.U j ⊓ Wa.1) ⊓ (K.U j' ⊓ Wa.1) ≤ K.U j' ⊓ Wa.1) (c j')) →
      ∃ x : G.obj Wa.1, ∀ j : K.ι, c j = G.res (inf_le_right : K.U j ⊓ Wa.1 ≤ Wa.1) x := by
  subst hpq
  obtain ⟨h1, h2⟩ :=
    AlgebraicGeometry.OModulePresheaf.bijective_cechPushforward_of_isAffineOpen_preimage q (𝟙 Y) K G hqc Wa Wa.2
  refine ⟨h1, fun c hc => ?_⟩
  obtain ⟨x, hx⟩ := h2 ⟨c, (OModulePresheaf.cechPushforward.mem_cocycles_iff (𝟙 Y) q K G Wa.1 c).mpr hc⟩
  exact ⟨x, hx⟩

section Cover

variable {P : Scheme.{u}} {Z : Scheme.{u}} (i : Z ⟶ P) {V' : Scheme.{u}} (g : V' ⟶ Z)
  (K' : V'.OrderedAffineCover) (W : P.affineOpens) {Y : Scheme.{u}} (t : Y ⟶ V')

def KY (hta : ∀ j : K'.ι, IsAffineOpen (t ⁻¹ᵁ (OModulePresheaf.cechPushforward.chart (g ≫ i) K' W.1 j)))
    (hcov : ⨆ j : K'.ι, t ⁻¹ᵁ (OModulePresheaf.cechPushforward.chart (g ≫ i) K' W.1 j) = ⊤) :
    Y.OrderedAffineCover where
  ι := K'.ι
  U j := t ⁻¹ᵁ (OModulePresheaf.cechPushforward.chart (g ≫ i) K' W.1 j)
  isAffineOpen := hta
  iSup_eq_top := hcov

theorem iSup_preimage_chart_eq_top {S : Scheme.{u}} (sY : Y ⟶ S) (f : S ⟶ P)
    (hf : f ⁻¹ᵁ W.1 = ⊤) (hw : t ≫ (g ≫ i) = sY ≫ f) :
    ⨆ j : K'.ι, t ⁻¹ᵁ (OModulePresheaf.cechPushforward.chart (g ≫ i) K' W.1 j) = ⊤ := by
  have hW : t ⁻¹ᵁ ((g ≫ i) ⁻¹ᵁ W.1) = ⊤ := by
    rw [← Scheme.Hom.comp_preimage, hw, Scheme.Hom.comp_preimage, hf, Scheme.Hom.preimage_top]
  have hj : ∀ j : K'.ι, t ⁻¹ᵁ (OModulePresheaf.cechPushforward.chart (g ≫ i) K' W.1 j) = t ⁻¹ᵁ K'.U j :=
    fun j => by
      show t ⁻¹ᵁ K'.U j ⊓ t ⁻¹ᵁ ((g ≫ i) ⁻¹ᵁ W.1) = t ⁻¹ᵁ K'.U j
      rw [hW, inf_top_eq]
  simp_rw [hj]
  exact t.iSup_preimage_eq_top K'.iSup_eq_top

end Cover

section Functions

variable {R : Type u} [CommRing R] {Y : Scheme.{u}} (sY : Y ⟶ Spec (CommRingCat.of R))

abbrev fn (U : Y.Opens) (r : R) : Γ(Y, U) :=
  ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ sY.appLE ⊤ U le_top).hom r

theorem fn_eq_algebraMap (U : Y.Opens) (r : R) :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom sY U
    fn sY U r = algebraMap R Γ(Y, U) r := rfl

theorem map_fn {U U' : Y.Opens} (h : U ≤ U') (r : R) :
    (Y.presheaf.map (homOfLE h).op).hom (fn sY U' r) = fn sY U r := by
  show ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ sY.appLE ⊤ U' le_top ≫ Y.presheaf.map (homOfLE h).op).hom r = _
  rw [Scheme.Hom.appLE_map]

theorem basicOpen_fn (U : Y.Opens) (r : R) : Y.basicOpen (fn sY U r) = U ⊓ Y.basicOpen (fn sY ⊤ r) := by
  rw [← map_fn sY (le_top : U ≤ ⊤) r, Scheme.basicOpen_res]

theorem fn_smul (G : OModulePresheaf sY) (U : Y.Opens) (r : R) (y : G.obj U) : fn sY U r • y = r • y := by
  letI := Scheme.TwoAffineOpenCover.algebraOfHom sY U
  haveI := G.isScalarTower U
  exact algebraMap_smul Γ(Y, U) r y

theorem fn_pow_smul (G : OModulePresheaf sY) (U : Y.Opens) (r : R) (n : ℕ) (y : G.obj U) :
    fn sY U r ^ n • y = r ^ n • y := by
  rw [← map_pow]; exact fn_smul sY G U (r ^ n) y

theorem res_eq_zero_iff_of_eq (G : OModulePresheaf sY) {U O O' : Y.Opens} (e : O = O') (hO : O ≤ U) (hO' : O' ≤ U)
    (y : G.obj U) : G.res hO y = 0 ↔ G.res hO' y = 0 := by
  subst e; rfl

end Functions

end K72W5b

end

open K72W5b in
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

    {Y : Scheme.{u}} (sY : Y ⟶ Spec (CommRingCat.of R)) [IsProper sY] (t : Y ⟶ V')
    (hY : IsPullback t sY (g ≫ i) (Spec.map (CommRingCat.ofHom (algebraMap Γ(P, W.1) R)) ≫ W.2.fromSpec))
    (hta : ∀ V : V'.affineOpens, V.1 ≤ (g ≫ i) ⁻¹ᵁ W.1 → IsAffineOpen (t ⁻¹ᵁ V.1))

    (G : OModulePresheaf sY) (hGc : G.IsCoherent) (hGq : G.IsQuasicoherent)
    (ε : ∀ U : Y.Opens, L →ₗ[R] G.obj U)
    (hεr : ∀ (U U' : Y.Opens) (h : U ≤ U') (x : L), G.res h (ε U' x) = ε U x)
    (hεβ : ∀ U : Y.affineOpens,
      letI := Scheme.TwoAffineOpenCover.algebraOfHom sY U.1
      ∃ β : Γ(Y, U.1) ⊗[R] L ≃ₗ[Γ(Y, U.1)] G.obj U.1, ∀ x : L, β (1 ⊗ₜ x) = ε U.1 x)

    (hYa : ∀ a ∈ (Scheme.IdealSheafData.vanishingIdeal T').ideal W,
      IsAffineOpen (Y.basicOpen (((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ sY.appLE ⊤ ⊤ le_top).hom (algebraMap Γ(P, W.1) R a))))
    (hKa : ∀ a ∈ (Scheme.IdealSheafData.vanishingIdeal T').ideal W,
      ∀ x : L, ε (Y.basicOpen (((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ sY.appLE ⊤ ⊤ le_top).hom (algebraMap Γ(P, W.1) R a))) x = 0 → ∃ k : ℕ, a ^ k • x = 0)
    (hCa : ∀ a ∈ (Scheme.IdealSheafData.vanishingIdeal T').ideal W,
      ∀ z : G.obj (Y.basicOpen (((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ sY.appLE ⊤ ⊤ le_top).hom (algebraMap Γ(P, W.1) R a))),
        ∃ (k : ℕ) (x : L), ε (Y.basicOpen (((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ sY.appLE ⊤ ⊤ le_top).hom (algebraMap Γ(P, W.1) R a))) x = (algebraMap Γ(P, W.1) R a) ^ k • z) :
    ∀ a ∈ (Scheme.IdealSheafData.vanishingIdeal T').ideal W,
      (∀ x : L, (∀ j : K'.ι, ε (t ⁻¹ᵁ (OModulePresheaf.cechPushforward.chart (g ≫ i) K' W.1 j)) x = 0) → ∃ k : ℕ, a ^ k • x = 0) ∧
      (∀ c : ∀ j : K'.ι, G.obj (t ⁻¹ᵁ (OModulePresheaf.cechPushforward.chart (g ≫ i) K' W.1 j)),
        (∀ j j' : K'.ι,
          G.res ((Opens.map t.base).monotone (inf_le_left : (OModulePresheaf.cechPushforward.chart (g ≫ i) K' W.1 j) ⊓ (OModulePresheaf.cechPushforward.chart (g ≫ i) K' W.1 j') ≤ _)) (c j)
            = G.res ((Opens.map t.base).monotone (inf_le_right : (OModulePresheaf.cechPushforward.chart (g ≫ i) K' W.1 j) ⊓ (OModulePresheaf.cechPushforward.chart (g ≫ i) K' W.1 j') ≤ _)) (c j')) →
        ∃ (k : ℕ) (x : L), ∀ j : K'.ι,
          ε (t ⁻¹ᵁ (OModulePresheaf.cechPushforward.chart (g ≫ i) K' W.1 j)) x = (algebraMap Γ(P, W.1) R a) ^ k • c j) := by
  classical
  intro a ha
  haveI : IsSeparated ((g ≫ i) ≫ q) := inferInstance

  let aR : R := algebraMap Γ(P, W.1) R a
  let Ya : Y.Opens := Y.basicOpen (fn sY ⊤ aR)
  have hYa' : IsAffineOpen Ya := hYa a ha
  let Wa : Y.affineOpens := ⟨Ya, hYa'⟩

  let aC : K'.ι → V'.affineOpens := fun j => OModulePresheaf.AffHom.affineChart (g ≫ i) q K' W j
  have hC : ∀ j, (aC j).1 ≤ (g ≫ i) ⁻¹ᵁ W.1 := fun j =>
    OModulePresheaf.cechPushforward.chart_le_preimage (g ≫ i) K' W.1 j
  have hcov : ⨆ j : K'.ι, t ⁻¹ᵁ (OModulePresheaf.cechPushforward.chart (g ≫ i) K' W.1 j) = ⊤ :=
    iSup_preimage_chart_eq_top i g K' W t sY
      (Spec.map (CommRingCat.ofHom (algebraMap Γ(P, W.1) R)) ≫ W.2.fromSpec)
      (by rw [Scheme.Hom.comp_preimage, W.2.fromSpec_preimage_self, Scheme.Hom.preimage_top]) hY.w
  let KYc : Y.OrderedAffineCover := KY i g K' W t (fun j => hta (aC j) (hC j)) hcov

  have haL : ∀ (n : ℕ) (x : L), a ^ n • x = aR ^ n • x := fun n x => by
    rw [← algebraMap_smul (A := R) (a ^ n) x, map_pow]

  obtain ⟨hsep, hglue⟩ := sheafAffine sY (Category.id_comp sY) G hGq KYc Wa
  refine ⟨?_, ?_⟩
  ·
    intro x hx
    apply hKa a ha x
    apply hsep
    intro j
    rw [map_zero, hεr, ← hεr (KYc.U j ⊓ Ya) (KYc.U j) inf_le_left x]
    show G.res _ (ε (t ⁻¹ᵁ (OModulePresheaf.cechPushforward.chart (g ≫ i) K' W.1 j)) x) = 0
    rw [hx j, map_zero]
  ·
    intro c hc

    let c' : ∀ j : K'.ι, G.obj (KYc.U j) := c
    have hc' : ∀ j j' : K'.ι, G.res (inf_le_left : KYc.U j ⊓ KYc.U j' ≤ KYc.U j) (c' j)
        = G.res (inf_le_right : KYc.U j ⊓ KYc.U j' ≤ KYc.U j') (c' j') := hc
    obtain ⟨z, hz⟩ := hglue (fun j => G.res (inf_le_left : KYc.U j ⊓ Ya ≤ KYc.U j) (c' j)) (fun j j' => by
      rw [G.res_res, G.res_res]
      have h := congrArg (G.res (le_inf (inf_le_left.trans inf_le_left) (inf_le_right.trans inf_le_left) :
        (KYc.U j ⊓ Ya) ⊓ (KYc.U j' ⊓ Ya) ≤ KYc.U j ⊓ KYc.U j')) (hc' j j')
      rw [G.res_res, G.res_res] at h
      exact h)
    obtain ⟨k, x, hx⟩ := hCa a ha z

    have hd : ∀ j : K'.ι, ∃ n : ℕ, aR ^ n • (ε (KYc.U j) x - aR ^ k • c' j) = 0 := fun j => by
      have hq := (hGq ⟨KYc.U j, KYc.isAffineOpen j⟩ (fn sY (KYc.U j) aR)).2 (ε (KYc.U j) x - aR ^ k • c' j)
      have hvan : G.res (inf_le_left : KYc.U j ⊓ Ya ≤ KYc.U j) (ε (KYc.U j) x - aR ^ k • c' j) = 0 := by
        rw [map_sub, LinearMap.map_smul, hεr, ← hεr (KYc.U j ⊓ Ya) Ya inf_le_right x, hx,
          LinearMap.map_smul, ← hz j, sub_self]
      obtain ⟨n, hn⟩ := hq ((res_eq_zero_iff_of_eq sY G (basicOpen_fn sY (KYc.U j) aR)
        (Y.basicOpen_le _) inf_le_left _).mpr hvan)
      exact ⟨n, by rw [← fn_pow_smul sY G (KYc.U j) aR n]; exact hn⟩
    choose n hn using hd
    refine ⟨(∑ j, n j) + k, a ^ (∑ j, n j) • x, fun j => ?_⟩
    have hle : n j ≤ ∑ j', n j' := Finset.single_le_sum (fun j _ => Nat.zero_le (n j)) (Finset.mem_univ j)
    have hkill : aR ^ (∑ j', n j') • (ε (KYc.U j) x - aR ^ k • c' j) = 0 := by
      rw [← Nat.sub_add_cancel hle, pow_add, mul_smul, hn j, smul_zero]
    rw [smul_sub, sub_eq_zero, ← mul_smul, ← pow_add] at hkill
    show ε (KYc.U j) (a ^ (∑ j, n j) • x) = aR ^ ((∑ j, n j) + k) • c' j
    rw [haL, LinearMap.map_smul]
    exact hkill

end S_AlgebraicGeometry_OModulePresheaf_exists_pow_smul_eq_zero_and_exists_eq_pow_smul_of_forall_isAffineOpen_basicOpen
end P2MW
export P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_pow_smul_eq_zero_and_exists_eq_pow_smul_of_forall_isAffineOpen_basicOpen (solution)
