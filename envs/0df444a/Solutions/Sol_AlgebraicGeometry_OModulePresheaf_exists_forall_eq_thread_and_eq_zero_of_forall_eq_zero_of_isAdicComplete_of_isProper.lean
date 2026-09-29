-- Prove2me | solution 1 for AlgebraicGeometry.OModulePresheaf.exists_forall_eq_thread_and_eq_zero_of_forall_eq_zero_of_isAdicComplete_of_isProper
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/81a6bae8-b691-5f09-b76d-2182257b65de

import Mathlib
import Definitions.Def_AlgebraicGeometry_OModulePresheafIdealFiltration
import Definitions.Def_AlgebraicGeometry_OModulePresheafCechPushforward
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_existsUnique_d_eq_zero_forall_sub_mem_pow_smul_of_isAdicComplete_of_isProper
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_cechFinite_of_isProper
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_forall_eq_thread_and_eq_zero_of_forall_eq_zero_of_isAdicComplete_of_isProper
p2m_attr_erase "instance" "DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I AlgebraicGeometry.ChowDatum.hι_closed AlgebraicGeometry.ChowDatumProj.hιN_closed AlgebraicGeometry.ChowDatumProj.hp_proper AlgebraicGeometry.ChowDatum.hp_isoU AlgebraicGeometry.ChowDatum.hp_proper AlgebraicGeometry.ProjSpace.algebraAway AlgebraicGeometry.ProjSpace.instIsProperProdOverπ AlgebraicGeometry.ChowDatumProj.hp_isoU AlgebraicGeometry.ProjSpace.isProper_π AlgebraicGeometry.ProjSpace.finiteType_mvPolynomial ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule"
p2m_attr_erase "simp" "DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq AlgebraicGeometry.ChowDatumProj.mk.sizeOf_spec AlgebraicGeometry.ChowDatum.mk.sizeOf_spec AlgebraicGeometry.ChowDatumProj.mk.injEq AlgebraicGeometry.ChowDatum.mk.injEq ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.mk.injEq"

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry TopologicalSpace
open scoped TensorProduct

universe u

noncomputable section

namespace K72W4

theorem mem_smul_top_pi_iff {R : Type*} [CommRing R] {ι : Type*} [Fintype ι] [DecidableEq ι]
    {M : ι → Type*} [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)] (I : Ideal R) (x : ∀ i, M i) :
    x ∈ I • (⊤ : Submodule R (∀ i, M i)) ↔ ∀ i, x i ∈ I • (⊤ : Submodule R (M i)) := by
  constructor
  · intro hx i
    have := Submodule.mem_map_of_mem (f := LinearMap.proj (R := R) (φ := M) i) hx
    rw [Submodule.map_smul'', Submodule.map_top, LinearMap.range_eq_top.mpr (LinearMap.proj_surjective i)]
      at this
    exact this
  · intro hx
    have : x = ∑ i, Pi.single i (x i) := by
      ext j; simp [Finset.sum_apply]
    rw [this]
    refine Submodule.sum_mem _ fun i _ => ?_
    have := Submodule.mem_map_of_mem (f := LinearMap.single R M i) (hx i)
    rw [Submodule.map_smul'', Submodule.map_top] at this
    exact Submodule.smul_mono le_rfl le_top this

theorem smul_top_mem_map {R : Type*} [CommRing R] {M N : Type*} [AddCommGroup M] [AddCommGroup N]
    [Module R M] [Module R N] (I : Ideal R) (f : M →ₗ[R] N) {x : M} (hx : x ∈ I • (⊤ : Submodule R M)) :
    f x ∈ I • (⊤ : Submodule R N) := by
  have h := Submodule.mem_map_of_mem (f := f) hx
  rw [Submodule.map_smul''] at h
  exact Submodule.smul_mono le_rfl le_top h

theorem core
    {R : Type*} [CommRing R] (I : Ideal R)
    {C0 C1 : Type*} [AddCommGroup C0] [Module R C0] [AddCommGroup C1] [Module R C1]
    (d : C0 →ₗ[R] C1)
    (L0 L1 : ℕ → Type*) [∀ n, AddCommGroup (L0 n)] [∀ n, AddCommGroup (L1 n)]
    (lam0 : ∀ n, C0 →+ L0 n) (lam1 : ∀ n, C1 →+ L1 n)
    (hsurj : ∀ n, Function.Surjective (lam0 n))
    (hker0 : ∀ n (x : C0), lam0 n x = 0 ↔ x ∈ I ^ (n + 1) • (⊤ : Submodule R C0))
    (hker1 : ∀ n (x : C1), lam1 n x = 0 → x ∈ I ^ (n + 1) • (⊤ : Submodule R C1))
    (dn : ∀ n, L0 n →+ L1 n) (hd : ∀ n (x : C0), dn n (lam0 n x) = lam1 n (d x))
    (τ : ∀ n, L0 (n + 1) →+ L0 n) (hτ : ∀ n (x : C0), τ n (lam0 (n + 1) x) = lam0 n x)
    (H : ∀ t : ℕ → C0, (∀ n, d (t n) ∈ I ^ (n + 1) • (⊤ : Submodule R C1)) →
      (∀ n, t (n + 1) - t n ∈ I ^ (n + 1) • (⊤ : Submodule R C0)) →
      ∃! a : C0, d a = 0 ∧ ∀ n, a - t n ∈ I ^ (n + 1) • (⊤ : Submodule R C0)) :
    (∀ a : C0, d a = 0 → (∀ n, lam0 n a = 0) → a = 0) ∧
    (∀ ℓ : ∀ n, L0 n, (∀ n, dn n (ℓ n) = 0) → (∀ n, τ n (ℓ (n + 1)) = ℓ n) →
      ∃ a : C0, d a = 0 ∧ ∀ n, lam0 n a = ℓ n) := by
  constructor
  · intro a hda hlam
    obtain ⟨a', -, huniq⟩ := H (fun _ => 0) (fun n => by simp) (fun n => by simp)
    have h1 : a = a' := huniq a ⟨hda, fun n => by rw [sub_zero, ← hker0 n]; exact hlam n⟩
    have h2 : (0 : C0) = a' := huniq 0 ⟨map_zero d, fun n => by simp⟩
    rw [h1, ← h2]
  · intro ℓ hdℓ hτℓ
    choose t ht using fun n => hsurj n (ℓ n)
    have hdt : ∀ n, d (t n) ∈ I ^ (n + 1) • (⊤ : Submodule R C1) := fun n => by
      apply hker1 n
      rw [← hd, ht, hdℓ]
    have htt : ∀ n, t (n + 1) - t n ∈ I ^ (n + 1) • (⊤ : Submodule R C0) := fun n => by
      rw [← hker0 n, map_sub, ← hτ, ht, ht, hτℓ, sub_self]
    obtain ⟨a, ⟨hda, han⟩, -⟩ := H t hdt htt
    refine ⟨a, hda, fun n => ?_⟩
    have : lam0 n (a - t n) = 0 := (hker0 n _).mpr (han n)
    rw [map_sub, sub_eq_zero] at this
    rw [this, ht]

section Bridge

variable {R : Type u} [CommRing R] {Y : Scheme.{u}} {π : Y ⟶ Spec (CommRingCat.of R)}
  (G : OModulePresheaf π) (K : Y.OrderedAffineCover)

def σ (i : K.ι) : K.Idx 0 := ⟨fun _ => i, fun a b hab => absurd (Fin.lt_def.mp hab) (by omega)⟩

@[scoped simp] theorem σ_val (i : K.ι) (k : Fin 1) : (σ K i).1 k = i := rfl

theorem eq_σ (s : K.Idx 0) : σ K (s.1 0) = s :=
  Subtype.ext (funext fun k => by rw [σ_val, Fin.fin_one_eq_zero k])

theorem le_inter_σ (i : K.ι) : K.U i ≤ K.inter (σ K i) := le_iInf fun _ => le_rfl

theorem inter_le_fst {n : ℕ} (s : K.Idx n) : K.inter s ≤ K.U (s.1 0) := K.inter_le s 0

abbrev pairU (s : K.Idx 1) : Y.Opens := K.U (s.1 0) ⊓ K.U (s.1 1)

theorem inter_le_pairU (s : K.Idx 1) : K.inter s ≤ pairU K s := le_inf (K.inter_le s 0) (K.inter_le s 1)

theorem pairU_le_inter (s : K.Idx 1) : pairU K s ≤ K.inter s :=
  le_iInf fun k => by
    fin_cases k
    · exact inf_le_left
    · exact inf_le_right

theorem res_congr_idx (x : G.cochain K 0) {s s' : K.Idx 0} (h : s = s')
    {O : Y.Opens} (h1 : O ≤ K.inter s) :
    G.res h1 (x s) = G.res (h ▸ h1) (x s') := by
  subst h; rfl

def E0 : G.cochain K 0 ≃ₗ[R] (∀ i : K.ι, G.obj (K.U i)) where
  toFun x i := G.res (le_inter_σ K i) (x (σ K i))
  invFun y s := G.res (inter_le_fst K s) (y (s.1 0))
  map_add' x y := funext fun i => map_add _ _ _
  map_smul' r x := funext fun i => LinearMap.map_smul _ _ _
  left_inv x := by
    funext s
    show G.res _ (G.res _ (x (σ K (s.1 0)))) = x s
    rw [G.res_res, res_congr_idx G K x (eq_σ K s)]
    exact G.res_refl_apply _ _
  right_inv y := by
    funext i
    show G.res _ (G.res _ (y i)) = y i
    rw [G.res_res]
    exact G.res_refl_apply _ _

theorem E0_apply (x : G.cochain K 0) (i : K.ι) : E0 G K x i = G.res (le_inter_σ K i) (x (σ K i)) := rfl

def E1 : G.cochain K 1 ≃ₗ[R] (∀ s : K.Idx 1, G.obj (pairU K s)) where
  toFun x s := G.res (pairU_le_inter K s) (x s)
  invFun y s := G.res (inter_le_pairU K s) (y s)
  map_add' x y := funext fun s => map_add _ _ _
  map_smul' r x := funext fun s => LinearMap.map_smul _ _ _
  left_inv x := by
    funext s
    show G.res _ (G.res _ (x s)) = x s
    rw [G.res_res]
    exact G.res_refl_apply _ _
  right_inv y := by
    funext s
    show G.res _ (G.res _ (y s)) = y s
    rw [G.res_res]
    exact G.res_refl_apply _ _

theorem E1_apply (x : G.cochain K 1) (s : K.Idx 1) : E1 G K x s = G.res (pairU_le_inter K s) (x s) := rfl

theorem face_zero_eq (s : K.Idx 1) : K.face s 0 = σ K (s.1 1) :=
  Subtype.ext (funext fun k => by
    rw [Scheme.OrderedAffineCover.face_val, σ_val, Function.comp_apply, Fin.fin_one_eq_zero k]
    rfl)

theorem face_one_eq (s : K.Idx 1) : K.face s 1 = σ K (s.1 0) :=
  Subtype.ext (funext fun k => by
    rw [Scheme.OrderedAffineCover.face_val, σ_val, Function.comp_apply, Fin.fin_one_eq_zero k]
    rfl)

theorem E1_d0 (x : G.cochain K 0) (s : K.Idx 1) :
    E1 G K (G.d K 0 x) s =
      G.res inf_le_right (E0 G K x (s.1 1)) - G.res inf_le_left (E0 G K x (s.1 0)) := by
  rw [E1_apply, OModulePresheaf.d_apply, Fin.sum_univ_two]
  simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one, one_smul, neg_smul, map_add, map_neg]
  rw [G.res_res, G.res_res, res_congr_idx G K x (face_zero_eq K s), res_congr_idx G K x (face_one_eq K s),
    E0_apply, E0_apply, G.res_res, G.res_res, sub_eq_add_neg]

def σ₂ {i j : K.ι} (hij : i < j) : K.Idx 1 :=
  ⟨![i, j], Fin.strictMono_iff_lt_succ.mpr fun k => by fin_cases k; exact hij⟩

theorem σ₂_fst {i j : K.ι} (hij : i < j) : (σ₂ K hij).1 0 = i := rfl
theorem σ₂_snd {i j : K.ι} (hij : i < j) : (σ₂ K hij).1 1 = j := rfl

theorem d0_eq_zero_iff (x : G.cochain K 0) :
    G.d K 0 x = 0 ↔ ∀ i j : K.ι,
      G.res (inf_le_left : K.U i ⊓ K.U j ≤ K.U i) (E0 G K x i)
        = G.res (inf_le_right : K.U i ⊓ K.U j ≤ K.U j) (E0 G K x j) := by
  constructor
  · intro hd
    have key : ∀ s : K.Idx 1,
        G.res (inf_le_left : pairU K s ≤ K.U (s.1 0)) (E0 G K x (s.1 0))
          = G.res (inf_le_right : pairU K s ≤ K.U (s.1 1)) (E0 G K x (s.1 1)) := fun s => by
      have hs : E1 G K (G.d K 0 x) s = 0 := by rw [hd, map_zero]; rfl
      rw [E1_d0, sub_eq_zero] at hs
      exact hs.symm
    intro i j
    rcases lt_trichotomy i j with hij | rfl | hji
    · exact key (σ₂ K hij)
    · rfl
    · have hk : G.res (inf_le_left : K.U j ⊓ K.U i ≤ K.U j) (E0 G K x j)
          = G.res (inf_le_right : K.U j ⊓ K.U i ≤ K.U i) (E0 G K x i) := key (σ₂ K hji)
      have h := congrArg (G.res (le_inf inf_le_right inf_le_left : K.U i ⊓ K.U j ≤ K.U j ⊓ K.U i)) hk
      rw [G.res_res, G.res_res] at h
      exact h.symm
  · intro h
    apply (E1 G K).injective
    rw [map_zero]
    funext s
    rw [E1_d0, Pi.zero_apply, sub_eq_zero]
    exact (h (s.1 0) (s.1 1)).symm

theorem mem_H0_iff (x : G.cochain K 0) :
    x ∈ G.H0 K ↔ ∀ i j : K.ι,
      G.res (inf_le_left : K.U i ⊓ K.U j ≤ K.U i) (E0 G K x i)
        = G.res (inf_le_right : K.U i ⊓ K.U j ≤ K.U j) (E0 G K x j) := by
  rw [OModulePresheaf.H0, LinearMap.mem_ker, d0_eq_zero_iff]

end Bridge

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

theorem KY_U (hta : ∀ j : K'.ι, IsAffineOpen (t ⁻¹ᵁ (OModulePresheaf.cechPushforward.chart (g ≫ i) K' W.1 j)))
    (hcov : ⨆ j : K'.ι, t ⁻¹ᵁ (OModulePresheaf.cechPushforward.chart (g ≫ i) K' W.1 j) = ⊤) (j : K'.ι) :
    (KY i g K' W t hta hcov).U j = t ⁻¹ᵁ (OModulePresheaf.cechPushforward.chart (g ≫ i) K' W.1 j) := rfl

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

end K72W4
p2m_reactivate "P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_forall_eq_thread_and_eq_zero_of_forall_eq_zero_of_isAdicComplete_of_isProper.K72W4"

end
p2m_reactivate "P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_forall_eq_thread_and_eq_zero_of_forall_eq_zero_of_isAdicComplete_of_isProper.K72W4"

open K72W4 in
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
    (∀ (ℓ : ∀ n, (OModulePresheaf.cechPushforward (g ≫ i) q K' (F' n)).obj W.1),
        (∀ n, ((φ' n).cechPushforward (g ≫ i) q K').app W (ℓ (n + 1)) = ℓ n) →
        ∃ c : ∀ j : K'.ι, G.obj (t ⁻¹ᵁ (OModulePresheaf.cechPushforward.chart (g ≫ i) K' W.1 j)),
          (∀ j j' : K'.ι,
          G.res ((Opens.map t.base).monotone (inf_le_left : (OModulePresheaf.cechPushforward.chart (g ≫ i) K' W.1 j) ⊓ (OModulePresheaf.cechPushforward.chart (g ≫ i) K' W.1 j') ≤ _)) (c j)
            = G.res ((Opens.map t.base).monotone (inf_le_right : (OModulePresheaf.cechPushforward.chart (g ≫ i) K' W.1 j) ⊓ (OModulePresheaf.cechPushforward.chart (g ≫ i) K' W.1 j') ≤ _)) (c j')) ∧
          ∀ (n : ℕ) (j : K'.ι),
            θ n (OModulePresheaf.AffHom.affineChart (g ≫ i) q K' W j)
              (OModulePresheaf.cechPushforward.chart_le_preimage (g ≫ i) K' W.1 j) (c j) = (ℓ n).1 j) ∧
    (∀ c : ∀ j : K'.ι, G.obj (t ⁻¹ᵁ (OModulePresheaf.cechPushforward.chart (g ≫ i) K' W.1 j)),
        (∀ j j' : K'.ι,
          G.res ((Opens.map t.base).monotone (inf_le_left : (OModulePresheaf.cechPushforward.chart (g ≫ i) K' W.1 j) ⊓ (OModulePresheaf.cechPushforward.chart (g ≫ i) K' W.1 j') ≤ _)) (c j)
            = G.res ((Opens.map t.base).monotone (inf_le_right : (OModulePresheaf.cechPushforward.chart (g ≫ i) K' W.1 j) ⊓ (OModulePresheaf.cechPushforward.chart (g ≫ i) K' W.1 j') ≤ _)) (c j')) →
        (∀ (n : ℕ) (j : K'.ι),
            θ n (OModulePresheaf.AffHom.affineChart (g ≫ i) q K' W j)
              (OModulePresheaf.cechPushforward.chart_le_preimage (g ≫ i) K' W.1 j) (c j) = 0) →
        c = 0) ∧
    (∃ s : Finset (∀ j : K'.ι, G.obj (t ⁻¹ᵁ (OModulePresheaf.cechPushforward.chart (g ≫ i) K' W.1 j))),
        (∀ c ∈ s, (∀ j j' : K'.ι,
          G.res ((Opens.map t.base).monotone (inf_le_left : (OModulePresheaf.cechPushforward.chart (g ≫ i) K' W.1 j) ⊓ (OModulePresheaf.cechPushforward.chart (g ≫ i) K' W.1 j') ≤ _)) (c j)
            = G.res ((Opens.map t.base).monotone (inf_le_right : (OModulePresheaf.cechPushforward.chart (g ≫ i) K' W.1 j) ⊓ (OModulePresheaf.cechPushforward.chart (g ≫ i) K' W.1 j') ≤ _)) (c j'))) ∧
        ∀ c : ∀ j : K'.ι, G.obj (t ⁻¹ᵁ (OModulePresheaf.cechPushforward.chart (g ≫ i) K' W.1 j)),
          (∀ j j' : K'.ι,
          G.res ((Opens.map t.base).monotone (inf_le_left : (OModulePresheaf.cechPushforward.chart (g ≫ i) K' W.1 j) ⊓ (OModulePresheaf.cechPushforward.chart (g ≫ i) K' W.1 j') ≤ _)) (c j)
            = G.res ((Opens.map t.base).monotone (inf_le_right : (OModulePresheaf.cechPushforward.chart (g ≫ i) K' W.1 j) ⊓ (OModulePresheaf.cechPushforward.chart (g ≫ i) K' W.1 j') ≤ _)) (c j')) → c ∈ Submodule.span R (s : Set (∀ j : K'.ι, G.obj (t ⁻¹ᵁ (OModulePresheaf.cechPushforward.chart (g ≫ i) K' W.1 j))))) := by
  classical
  haveI := hRc
  haveI : IsSeparated ((g ≫ i) ≫ q) := inferInstance

  set J : Ideal R := I.map ((algebraMap Γ(P, W.1) R).comp
    ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ q.appLE ⊤ W.1 le_top).hom) with hJ

  let aC : K'.ι → V'.affineOpens := fun j => OModulePresheaf.AffHom.affineChart (g ≫ i) q K' W j
  have hC : ∀ j, (aC j).1 ≤ (g ≫ i) ⁻¹ᵁ W.1 := fun j =>
    OModulePresheaf.cechPushforward.chart_le_preimage (g ≫ i) K' W.1 j

  have hcov : ⨆ j : K'.ι, t ⁻¹ᵁ (OModulePresheaf.cechPushforward.chart (g ≫ i) K' W.1 j) = ⊤ :=
    iSup_preimage_chart_eq_top i g K' W t sY
      (Spec.map (CommRingCat.ofHom (algebraMap Γ(P, W.1) R)) ≫ W.2.fromSpec)
      (by rw [Scheme.Hom.comp_preimage, W.2.fromSpec_preimage_self, Scheme.Hom.preimage_top]) hY.w
  let KYc : Y.OrderedAffineCover := KY i g K' W t (fun j => hta (aC j) (hC j)) hcov
  let aP : KYc.Idx 1 → V'.affineOpens := fun s =>
    ⟨(aC (s.1 0)).1 ⊓ (aC (s.1 1)).1,
      Scheme.OrderedAffineCover.isAffineOpen_inf_of_isSeparated ((g ≫ i) ≫ q) (aC (s.1 0)).2 (aC (s.1 1)).2⟩
  have hP : ∀ s, (aP s).1 ≤ (g ≫ i) ⁻¹ᵁ W.1 := fun s => inf_le_left.trans (hC _)

  let L0 : ℕ → Type u := fun n => ∀ j : K'.ι, (F' n).obj (aC j).1
  let L1 : ℕ → Type u := fun n => ∀ s : KYc.Idx 1, (F' n).obj (aP s).1
  let lam0 : ∀ n, G.cochain KYc 0 →+ L0 n := fun n =>
    (AddMonoidHom.pi fun j => (θ n (aC j) (hC j)).comp
      (Pi.evalAddMonoidHom (fun j : K'.ι => G.obj (KYc.U j)) j)).comp (E0 G KYc).toLinearMap.toAddMonoidHom
  let lam1 : ∀ n, G.cochain KYc 1 →+ L1 n := fun n =>
    (AddMonoidHom.pi fun s => (θ n (aP s) (hP s)).comp
      (Pi.evalAddMonoidHom (fun s : KYc.Idx 1 => G.obj (pairU KYc s)) s)).comp
        (E1 G KYc).toLinearMap.toAddMonoidHom
  let dn : ∀ n, L0 n →+ L1 n := fun n =>
    AddMonoidHom.pi fun s =>
      ((F' n).res (inf_le_right : (aP s).1 ≤ (aC (s.1 1)).1)).toAddMonoidHom.comp
          (Pi.evalAddMonoidHom (fun j : K'.ι => (F' n).obj (aC j).1) (s.1 1))
        - ((F' n).res (inf_le_left : (aP s).1 ≤ (aC (s.1 0)).1)).toAddMonoidHom.comp
          (Pi.evalAddMonoidHom (fun j : K'.ι => (F' n).obj (aC j).1) (s.1 0))
  let τ : ∀ n, L0 (n + 1) →+ L0 n := fun n =>
    AddMonoidHom.pi fun j => ((φ' n).app (aC j)).toAddMonoidHom.comp
      (Pi.evalAddMonoidHom (fun j : K'.ι => (F' (n + 1)).obj (aC j).1) j)
  have hsurj : ∀ n, Function.Surjective (lam0 n) := fun n y => by
    choose z hz using fun j => hθo n (aC j) (hC j) (y j)
    refine ⟨(E0 G KYc).symm z, funext fun j => ?_⟩
    show θ n (aC j) (hC j) (E0 G KYc ((E0 G KYc).symm z) j) = y j
    rw [LinearEquiv.apply_symm_apply, hz]
  have hker0 : ∀ n (x : G.cochain KYc 0), lam0 n x = 0 ↔ x ∈ J ^ (n + 1) • (⊤ : Submodule R _) := by
    intro n x
    constructor
    · intro h0
      have h1 : ∀ j, E0 G KYc x j ∈ J ^ (n + 1) • (⊤ : Submodule R _) := fun j =>
        (hθk n (aC j) (hC j) _).mp (congrFun h0 j)
      have h2 : E0 G KYc x ∈ J ^ (n + 1) • (⊤ : Submodule R _) := (mem_smul_top_pi_iff _ _).mpr h1
      have h3 : (E0 G KYc).symm (E0 G KYc x) ∈ J ^ (n + 1) • (⊤ : Submodule R _) :=
        smul_top_mem_map _ (E0 G KYc).symm.toLinearMap h2
      rwa [LinearEquiv.symm_apply_apply] at h3
    · intro hx
      funext j
      show θ n (aC j) (hC j) (E0 G KYc x j) = 0
      rw [hθk n (aC j) (hC j)]
      have h3 : E0 G KYc x ∈ J ^ (n + 1) • (⊤ : Submodule R _) :=
        smul_top_mem_map _ (E0 G KYc).toLinearMap hx
      exact (mem_smul_top_pi_iff _ _).mp h3 j
  have hker1 : ∀ n (x : G.cochain KYc 1), lam1 n x = 0 → x ∈ J ^ (n + 1) • (⊤ : Submodule R _) := by
    intro n x h0
    have h1 : ∀ s, E1 G KYc x s ∈ J ^ (n + 1) • (⊤ : Submodule R _) := fun s =>
      (hθk n (aP s) (hP s) _).mp (congrFun h0 s)
    have h2 : E1 G KYc x ∈ J ^ (n + 1) • (⊤ : Submodule R _) := (mem_smul_top_pi_iff _ _).mpr h1
    have h3 : (E1 G KYc).symm (E1 G KYc x) ∈ J ^ (n + 1) • (⊤ : Submodule R _) :=
      smul_top_mem_map _ (E1 G KYc).symm.toLinearMap h2
    rwa [LinearEquiv.symm_apply_apply] at h3
  have hd : ∀ n (x : G.cochain KYc 0), dn n (lam0 n x) = lam1 n (G.d KYc 0 x) := by
    intro n x
    funext s
    show (F' n).res inf_le_right (θ n (aC (s.1 1)) (hC (s.1 1)) (E0 G KYc x (s.1 1)))
        - (F' n).res inf_le_left (θ n (aC (s.1 0)) (hC (s.1 0)) (E0 G KYc x (s.1 0)))
      = θ n (aP s) (hP s) (E1 G KYc (G.d KYc 0 x) s)
    rw [hθr n (aP s) (aC (s.1 1)) (hP s) (hC (s.1 1)) inf_le_right,
      hθr n (aP s) (aC (s.1 0)) (hP s) (hC (s.1 0)) inf_le_left, E1_d0]
    exact (map_sub (θ n (aP s) (hP s)) _ _).symm
  have hτ : ∀ n (x : G.cochain KYc 0), τ n (lam0 (n + 1) x) = lam0 n x := by
    intro n x
    funext j
    exact hθφ n (aC j) (hC j) _
  have H : ∀ tt : ℕ → G.cochain KYc 0, (∀ n, G.d KYc 0 (tt n) ∈ J ^ (n + 1) • (⊤ : Submodule R _)) →
      (∀ n, tt (n + 1) - tt n ∈ J ^ (n + 1) • (⊤ : Submodule R _)) →
      ∃! a : G.cochain KYc 0, G.d KYc 0 a = 0 ∧ ∀ n, a - tt n ∈ J ^ (n + 1) • (⊤ : Submodule R _) :=
    fun tt hd' ht' =>
      AlgebraicGeometry.OModulePresheaf.existsUnique_d_eq_zero_forall_sub_mem_pow_smul_of_isAdicComplete_of_isProper
        J sY G hGc hGq KYc tt hd' ht'
  obtain ⟨hinj, hsur⟩ := core J (G.d KYc 0) L0 L1 lam0 lam1 hsurj hker0 hker1 dn hd τ hτ H
  refine ⟨?_, ?_, ?_⟩
  ·
    intro ℓ hℓ
    obtain ⟨a, hda, hla⟩ := hsur (fun n => (ℓ n).1)
      (fun n => funext fun s => by
        show (F' n).res inf_le_right ((ℓ n).1 (s.1 1)) - (F' n).res inf_le_left ((ℓ n).1 (s.1 0)) = 0
        rw [sub_eq_zero]
        exact ((OModulePresheaf.cechPushforward.mem_cocycles_iff (g ≫ i) q K' (F' n) W.1 (ℓ n).1).mp
          (ℓ n).2 (s.1 0) (s.1 1)).symm)
      (fun n => funext fun j => congrArg (fun z => z.1 j) (hℓ n))
    refine ⟨E0 G KYc a, (d0_eq_zero_iff G KYc a).mp hda, fun n j => ?_⟩
    exact congrFun (hla n) j
  ·
    intro c hc h0
    have hda : G.d KYc 0 ((E0 G KYc).symm c) = 0 := by
      rw [d0_eq_zero_iff]
      intro j j'
      rw [LinearEquiv.apply_symm_apply]
      exact hc j j'
    have hz := hinj ((E0 G KYc).symm c) hda (fun n => funext fun j => by
      show θ n (aC j) (hC j) (E0 G KYc ((E0 G KYc).symm c) j) = 0
      rw [LinearEquiv.apply_symm_apply]
      exact h0 n j)
    have : c = E0 G KYc ((E0 G KYc).symm c) := ((E0 G KYc).apply_symm_apply c).symm
    rw [this, hz]
    exact map_zero (E0 G KYc)
  ·
    have hfin : Module.Finite R (G.H0 KYc) :=
      (AlgebraicGeometry.OModulePresheaf.cechFinite_of_isProper G hGc hGq KYc).1
    let Φ : G.H0 KYc →ₗ[R] (∀ j : KYc.ι, G.obj (KYc.U j)) :=
      (E0 G KYc).toLinearMap.comp (G.H0 KYc).subtype
    have hfg : (LinearMap.range Φ).FG := by
      rw [LinearMap.range_eq_map]
      exact Module.Finite.fg_top.map Φ
    obtain ⟨s, hs⟩ := hfg
    have hrange : ∀ c : ∀ j : KYc.ι, G.obj (KYc.U j), c ∈ LinearMap.range Φ ↔
        ∀ j j' : KYc.ι, G.res (inf_le_left : KYc.U j ⊓ KYc.U j' ≤ KYc.U j) (c j)
          = G.res (inf_le_right : KYc.U j ⊓ KYc.U j' ≤ KYc.U j') (c j') := by
      intro c
      constructor
      · rintro ⟨⟨a, ha⟩, rfl⟩
        exact (mem_H0_iff G KYc a).mp ha
      · intro hc
        refine ⟨⟨(E0 G KYc).symm c, (mem_H0_iff G KYc _).mpr fun j j' => ?_⟩, ?_⟩
        · rw [LinearEquiv.apply_symm_apply]; exact hc j j'
        · exact (E0 G KYc).apply_symm_apply c
    refine ⟨s, fun c hcs => (hrange c).mp (hs ▸ Submodule.subset_span hcs), fun c hc => ?_⟩
    have hc' := (hrange c).mpr hc
    rw [← hs] at hc'
    exact hc'

end S_AlgebraicGeometry_OModulePresheaf_exists_forall_eq_thread_and_eq_zero_of_forall_eq_zero_of_isAdicComplete_of_isProper
end P2MW
export P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_forall_eq_thread_and_eq_zero_of_forall_eq_zero_of_isAdicComplete_of_isProper (solution)
