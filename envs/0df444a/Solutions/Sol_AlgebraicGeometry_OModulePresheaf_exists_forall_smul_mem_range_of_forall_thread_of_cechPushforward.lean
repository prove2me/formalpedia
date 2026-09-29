-- Prove2me | solution 1 for AlgebraicGeometry.OModulePresheaf.exists_forall_smul_mem_range_of_forall_thread_of_cechPushforward
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/2703c7d1-540d-5d32-b901-8ff130e3ac2c

import Mathlib
import Definitions.Def_AlgebraicGeometry_OModulePresheafHom
import Definitions.Def_AlgebraicGeometry_OModulePresheafIdealFiltration
import Definitions.Def_AlgebraicGeometry_OModulePresheafCechPushforward
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_kernel_cokernel_adicSystem_of_affHom_of_forall_ker_eq_pow_smul_top
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_forall_smul_mem_range_of_forall_thread_of_cechPushforward

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

universe u

noncomputable section

p2m_open "CategoryTheory AlgebraicGeometry P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_forall_smul_mem_range_of_forall_thread_of_cechPushforward.AlgebraicGeometry TopologicalSpace"

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Surjective IsProper LocallyOfFiniteType Spec Scheme Scheme.IdealSheafData.vanishingIdeal IsClosedImmersion Scheme.IdealSheafData OModulePresheaf.AffHom OModulePresheaf Scheme.TwoAffineOpenCover Scheme.TwoAffineOpenCover.algebraOfHom OModulePresheaf.IdealAnnihilates OModulePresheaf.cechPushforward.chart_le_preimage OModulePresheaf.cechPushforward OModulePresheaf.AffHom.affineChart OModulePresheaf.exists_kernel_cokernel_adicSystem_of_affHom_of_forall_ker_eq_pow_smul_top"
namespace OModulePresheaf
p2m_export "AlgebraicGeometry.OModulePresheaf" "AffHom IsCoherent IsQuasicoherent unit res obj rec IdealAnnihilates zero ker im cechPushforward.chart_le_preimage cechPushforward AffHom.affineChart exists_kernel_cokernel_adicSystem_of_affHom_of_forall_ker_eq_pow_smul_top"
namespace C3Asm
p2m_open "AlgebraicGeometry.OModulePresheaf AlgebraicGeometry"

variable {A : Type u} [CommRing A] {P : Scheme.{u}} {q : P ⟶ Spec (CommRingCat.of A)}

section Threads

variable (F : ℕ → OModulePresheaf q) (φ : ∀ k, AffHom (F (k + 1)) (F k))

def IsThread (U : P.affineOpens) (s : ∀ n, (F n).obj U.1) : Prop := ∀ n, (φ n).app U (s (n + 1)) = s n

def seq0 (hφs : ∀ (k : ℕ) (U : P.affineOpens), Function.Surjective ((φ k).app U))
    (U : P.affineOpens) (y : (F 0).obj U.1) : ∀ m, (F m).obj U.1 :=
  fun m => @Nat.rec (fun m => (F m).obj U.1) y (fun m prev => Classical.choose (hφs m U prev)) m

def seqMod (hφs : ∀ (k : ℕ) (U : P.affineOpens), Function.Surjective ((φ k).app U))
    (U : P.affineOpens) (n : ℕ) (x : ∀ m, (F m).obj U.1) (y : (F (n + 1)).obj U.1) : ∀ m, (F m).obj U.1 :=
  fun m => @Nat.rec (fun m => (F m).obj U.1) (x 0)
    (fun m prev => if m + 1 ≤ n then x (m + 1) else
      if h : m = n then (by subst h; exact y) else Classical.choose (hφs m U prev)) m

theorem seqMod_succ (hφs : ∀ (k : ℕ) (U : P.affineOpens), Function.Surjective ((φ k).app U))
    (U : P.affineOpens) (n : ℕ) (x : ∀ m, (F m).obj U.1) (y : (F (n + 1)).obj U.1) (m : ℕ) :
    seqMod F φ hφs U n x y (m + 1) = (if m + 1 ≤ n then x (m + 1) else
      if h : m = n then (by subst h; exact y) else
        Classical.choose (hφs m U (seqMod F φ hφs U n x y m))) := rfl

theorem seqMod_of_le (hφs : ∀ (k : ℕ) (U : P.affineOpens), Function.Surjective ((φ k).app U))
    (U : P.affineOpens) (n : ℕ) (x : ∀ m, (F m).obj U.1) (y : (F (n + 1)).obj U.1) :
    ∀ m, m ≤ n → seqMod F φ hφs U n x y m = x m
  | 0, _ => rfl
  | m + 1, hm => by rw [seqMod_succ, if_pos hm]

theorem seqMod_at (hφs : ∀ (k : ℕ) (U : P.affineOpens), Function.Surjective ((φ k).app U))
    (U : P.affineOpens) (n : ℕ) (x : ∀ m, (F m).obj U.1) (y : (F (n + 1)).obj U.1) :
    seqMod F φ hφs U n x y (n + 1) = y := by
  rw [seqMod_succ, if_neg (Nat.not_succ_le_self n), dif_pos rfl]

theorem exists_isThread (hφs : ∀ (k : ℕ) (U : P.affineOpens), Function.Surjective ((φ k).app U))
    (U : P.affineOpens) : ∀ (k : ℕ) (y : (F k).obj U.1), ∃ s : ∀ n, (F n).obj U.1, IsThread F φ U s ∧ s k = y := by
  intro k
  induction k with
  | zero =>
    intro y
    exact ⟨seq0 F φ hφs U y, fun m => Classical.choose_spec (hφs m U (seq0 F φ hφs U y m)), rfl⟩
  | succ n ih =>
    intro y
    obtain ⟨x, hx, hxn⟩ := ih ((φ n).app U y)
    refine ⟨seqMod F φ hφs U n x y, fun m => ?_, seqMod_at F φ hφs U n x y⟩
    rw [seqMod_succ]
    split_ifs with h1 h2
    · rw [seqMod_of_le F φ hφs U n x y m (Nat.le_of_succ_le h1)]
      exact hx m
    · subst h2
      rw [seqMod_of_le F φ hφs U m x y m le_rfl, ← hxn]
    · exact Classical.choose_spec (hφs m U (seqMod F φ hφs U n x y m))

theorem IsThread.sub_mem (I : Ideal A)
    (hφs : ∀ (k : ℕ) (U : P.affineOpens), Function.Surjective ((φ k).app U))
    (hφk : ∀ (k : ℕ) (U : P.affineOpens),
      LinearMap.ker ((φ k).app U) = I ^ (k + 1) • (⊤ : Submodule A ((F (k + 1)).obj U.1)))
    {U : P.affineOpens} {s s' : ∀ n, (F n).obj U.1} (hs : IsThread F φ U s) (hs' : IsThread F φ U s')
    {k : ℕ} (h : s k = s' k) : ∀ n, k ≤ n → s n - s' n ∈ I ^ (k + 1) • (⊤ : Submodule A ((F n).obj U.1)) := by
  intro n hn
  induction n, hn using Nat.le_induction with
  | base => rw [h, sub_self]; exact Submodule.zero_mem _
  | succ n hn ih =>

    have himg : (φ n).app U (s (n + 1) - s' (n + 1)) ∈
        Submodule.map ((φ n).app U) (I ^ (k + 1) • (⊤ : Submodule A ((F (n + 1)).obj U.1))) := by
      rw [Submodule.map_smul'', Submodule.map_top, LinearMap.range_eq_top.mpr (hφs n U), map_sub, hs n, hs' n]
      exact ih
    obtain ⟨w, hw, hφw⟩ := himg
    have hker : s (n + 1) - s' (n + 1) - w ∈ LinearMap.ker ((φ n).app U) := by
      rw [LinearMap.mem_ker, map_sub, hφw, sub_self]
    rw [hφk] at hker
    have hle : I ^ (n + 1) • (⊤ : Submodule A ((F (n + 1)).obj U.1)) ≤ I ^ (k + 1) • ⊤ :=
      Submodule.smul_mono_left (Ideal.pow_le_pow_right (by omega))
    have := Submodule.add_mem _ (hle hker) hw
    rwa [sub_add_cancel] at this

end Threads

section Levels

variable (F : ℕ → OModulePresheaf q) (φ : ∀ k, AffHom (F (k + 1)) (F k))

theorem smul_top_mem_map {R : Type*} [CommSemiring R] {M N : Type*} [AddCommMonoid M] [AddCommMonoid N]
    [Module R M] [Module R N] (J : Ideal R) (f : M →ₗ[R] N) {x : M} (hx : x ∈ J • (⊤ : Submodule R M)) :
    f x ∈ J • (⊤ : Submodule R N) := by
  have h := Submodule.mem_map_of_mem (f := f) hx
  rw [Submodule.map_smul''] at h
  exact Submodule.smul_mono le_rfl le_top h

theorem eq_zero_of_mem_smul_top {R : Type*} [CommRing R] {M N : Type*} [AddCommGroup M] [AddCommGroup N]
    [Module R M] [Module R N] (J : Ideal R) (f : M →ₗ[R] N) (hf : Function.Surjective f)
    (hker : LinearMap.ker f = J • (⊤ : Submodule R M)) {z : N} (hz : z ∈ J • (⊤ : Submodule R N)) : z = 0 := by
  have htop : (⊤ : Submodule R N) = (⊤ : Submodule R M).map f := by
    rw [Submodule.map_top, LinearMap.range_eq_top.2 hf]
  rw [htop, ← Submodule.map_smul'', ← hker] at hz
  obtain ⟨b, hb, rfl⟩ := hz
  exact LinearMap.mem_ker.1 hb

theorem thread_mem_down (U : P.affineOpens) (J : Ideal A) (s : ∀ n, (F n).obj U.1) (hs : IsThread F φ U s) (c : ℕ) :
    ∀ k : ℕ, s (k + c) ∈ J • (⊤ : Submodule A ((F (k + c)).obj U.1)) → s k ∈ J • (⊤ : Submodule A ((F k).obj U.1)) := by
  induction c with
  | zero => intro k h; exact h
  | succ c ih =>
    intro k h
    apply ih
    rw [← hs (k + c)]
    exact smul_top_mem_map J ((φ (k + c)).app U) h

end Levels

end AlgebraicGeometry.OModulePresheaf.C3Asm

end

p2m_open "CategoryTheory AlgebraicGeometry P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_forall_smul_mem_range_of_forall_thread_of_cechPushforward.AlgebraicGeometry TopologicalSpace"
open scoped TensorProduct
open AlgebraicGeometry.OModulePresheaf.C3Asm

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
    (hνu : ∀ (k : ℕ) (W : P.affineOpens), (ν k).app W ∘ₗ (u k).app W = (v k).app W)

    (hunif : ∃ N : ℕ, ∀ W : P.affineOpens,
      (∀ (ℓ : ∀ n, (OModulePresheaf.cechPushforward (g ≫ i) q K' (F' n)).obj W.1),
        (∀ n, ((φ' n).cechPushforward (g ≫ i) q K').app W (ℓ (n + 1)) = ℓ n) →
        ∀ a : Γ(P, W.1), a ∈ (Scheme.IdealSheafData.vanishingIdeal T').ideal W ^ N →
          ∃ m : ∀ n, (F n).obj W.1,
            (∀ n, (φ n).app W (m (n + 1)) = m n) ∧ ∀ n, (v n).app W (m n) = a • ℓ n) ∧
      (∀ (m : ∀ n, (F n).obj W.1), (∀ n, (φ n).app W (m (n + 1)) = m n) →
        (∀ n, (v n).app W (m n) = 0) →
        ∀ a : Γ(P, W.1), a ∈ (Scheme.IdealSheafData.vanishingIdeal T').ideal W ^ N →
          ∀ n, a • m n = 0)) :
    ∃ N : ℕ,
      (∀ (k : ℕ) (W : P.affineOpens) (a : Γ(P, W.1)),
        a ∈ (Scheme.IdealSheafData.vanishingIdeal T').ideal W ^ N →
        ∀ y : (Ps k).obj W.1, ∃ x : (F k).obj W.1, (u k).app W x = a • y) ∧
      (∀ W : P.affineOpens, ∃ c : ℕ, ∀ (k : ℕ) (x : (F (k + c)).obj W.1), (u (k + c)).app W x = 0 →
        ∀ a : Γ(P, W.1), a ∈ (Scheme.IdealSheafData.vanishingIdeal T').ideal W ^ N →
          a • x ∈ I ^ (k + 1) • (⊤ : Submodule A ((F (k + c)).obj W.1))) := by
  classical
  haveI : LocallyOfFiniteType q := inferInstance
  obtain ⟨N, hN⟩ := hunif
  refine ⟨N, ?_, ?_⟩
  ·
    intro k W a ha y
    obtain ⟨yy, hyy, hyyk⟩ := exists_isThread Ps π hπs W k y

    have hℓ : ∀ n, ((φ' n).cechPushforward (g ≫ i) q K').app W ((ν (n + 1)).app W (yy (n + 1))) = (ν n).app W (yy n) :=
      fun n => by rw [← LinearMap.comp_apply, hνc n W, LinearMap.comp_apply, hyy n]
    obtain ⟨m, hm, hvm⟩ := (hN W).1 (fun n => (ν n).app W (yy n)) hℓ a ha

    set δ : ∀ n, (Ps n).obj W.1 := fun n => (u n).app W (m n) - a • yy n with hδ
    have hδt : IsThread Ps π W δ := fun n => by
      simp only [hδ]
      rw [map_sub, (π n).app_smul, hyy n, ← LinearMap.comp_apply, huc n W, LinearMap.comp_apply, hm n]
    have hδν : ∀ n, (ν n).app W (δ n) = 0 := fun n => by
      simp only [hδ]
      rw [map_sub, (ν n).app_smul, ← LinearMap.comp_apply, hνu n W, hvm n, sub_self]
    obtain ⟨c, hc⟩ := hνi W k
    have h1 : δ (k + c) ∈ I ^ (k + 1) • (⊤ : Submodule A ((Ps (k + c)).obj W.1)) :=
      hc (LinearMap.mem_ker.2 (hδν (k + c)))
    have h2 : δ k ∈ I ^ (k + 1) • (⊤ : Submodule A ((Ps k).obj W.1)) :=
      thread_mem_down Ps π W (I ^ (k + 1)) δ hδt c k h1
    have h3 : δ k = 0 := eq_zero_of_mem_smul_top (I ^ (k + 1)) ((ψP k).app W) (hψPs k W) (hψPk k W) h2
    refine ⟨m k, ?_⟩
    have : (u k).app W (m k) - a • yy k = 0 := h3
    rw [sub_eq_zero, hyyk] at this
    exact this
  ·
    intro W
    obtain ⟨Ks, κ, j, Cs, γ, θ, hKc, hKq, hκs, hκk, hjφ, huj, hAR, -, -⟩ :=
      AlgebraicGeometry.OModulePresheaf.exists_kernel_cokernel_adicSystem_of_affHom_of_forall_ker_eq_pow_smul_top
        I F hFc hFq φ hφs hφk Ps hPsc hPsq π hπs hπk u huc
    obtain ⟨c, hcW⟩ := hAR W
    refine ⟨c, fun k x hx a ha => ?_⟩
    obtain ⟨y0, hy0, x₁, hx₁, rfl⟩ := Submodule.mem_sup.1 ((hcW k).1 (LinearMap.mem_ker.2 hx))
    obtain ⟨y, rfl⟩ := LinearMap.mem_range.1 hy0

    obtain ⟨yy, hyy, hyyk⟩ := exists_isThread Ks κ hκs W (k + c) y
    have hm : IsThread F φ W (fun n => (j n).app W (yy n)) := fun n => by
      show (φ n).app W ((j (n + 1)).app W (yy (n + 1))) = (j n).app W (yy n)
      rw [← LinearMap.comp_apply, hjφ n W, LinearMap.comp_apply, hyy n]
    have hv0 : ∀ n, (v n).app W ((j n).app W (yy n)) = 0 := fun n => by
      rw [← hνu n W, LinearMap.comp_apply, ← LinearMap.comp_apply (f := (u n).app W), huj n W, LinearMap.zero_apply,
        map_zero]
    have hkill : ∀ n, a • (j n).app W (yy n) = 0 := (hN W).2 (fun n => (j n).app W (yy n)) (fun n => hm n) hv0 a ha

    have hayy : IsThread Ks κ W (fun n => a • yy n) := fun n => by
      show (κ n).app W (a • yy (n + 1)) = a • yy n
      rw [(κ n).app_smul, hyy n]
    have htop : a • yy ((k + c) + c) ∈ I ^ ((k + c) + 1) • (⊤ : Submodule A ((Ks ((k + c) + c)).obj W.1)) := by
      refine (hcW (k + c)).2 (LinearMap.mem_ker.2 ?_)
      rw [(j _).app_smul]
      exact hkill _
    have hbot : a • yy (k + c) ∈ I ^ ((k + c) + 1) • (⊤ : Submodule A ((Ks (k + c)).obj W.1)) :=
      thread_mem_down Ks κ W (I ^ ((k + c) + 1)) (fun n => a • yy n) hayy c (k + c) htop
    have hzero : a • yy (k + c) = 0 :=
      eq_zero_of_mem_smul_top (I ^ ((k + c) + 1)) ((κ (k + c)).app W) (hκs (k + c) W) (hκk (k + c) W) hbot
    rw [hyyk] at hzero

    letI := Scheme.TwoAffineOpenCover.algebraOfHom q W.1
    rw [smul_add, ← (j (k + c)).app_smul, hzero, map_zero, zero_add]

    let La : (F (k + c)).obj W.1 →ₗ[A] (F (k + c)).obj W.1 :=
      { toFun := fun z => a • z
        map_add' := fun z z' => smul_add a z z'
        map_smul' := fun r z => by
          simp only [RingHom.id_apply]
          exact smul_algebra_smul_comm r a z }
    exact smul_top_mem_map (I ^ (k + 1)) La hx₁

end S_AlgebraicGeometry_OModulePresheaf_exists_forall_smul_mem_range_of_forall_thread_of_cechPushforward
end P2MW
export P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_forall_smul_mem_range_of_forall_thread_of_cechPushforward (solution)
