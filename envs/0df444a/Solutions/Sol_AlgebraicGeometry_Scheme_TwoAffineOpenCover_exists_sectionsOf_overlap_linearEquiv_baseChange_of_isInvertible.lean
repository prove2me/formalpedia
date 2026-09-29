-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.TwoAffineOpenCover.exists_sectionsOf_overlap_linearEquiv_baseChange_of_isInvertible
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/707a96c5-b0a7-5caa-902c-22c75fe8c9cf

import Mathlib
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_isLocalization_basicOpen_of_locallyTrivial
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_sectionsOf_overlap_linearEquiv_baseChange_of_isInvertible

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry Opposite

namespace P2mWs11Span

variable {Y : Scheme.{u}}

theorem op_hom_eq {U V : Y.Opens} (i j : op U ⟶ op V) : i = j :=
  Quiver.Hom.unop_inj (Subsingleton.elim _ _)

theorem map_map (M : Y.Modules) {U V W : Y.Opens} (i : op U ⟶ op V) (j : op V ⟶ op W) (x : Γ(M, U)) :
    M.presheaf.map j (M.presheaf.map i x) = M.presheaf.map (i ≫ j) x := by
  rw [Functor.map_comp]; rfl

theorem map_irrel (M : Y.Modules) {U V : Y.Opens} (i j : op U ⟶ op V) (x : Γ(M, U)) :
    M.presheaf.map i x = M.presheaf.map j x := by rw [op_hom_eq i j]

theorem ring_map_map {U V W : Y.Opens} (i : op U ⟶ op V) (j : op V ⟶ op W) (x : Y.presheaf.obj (op U)) :
    Y.presheaf.map j (Y.presheaf.map i x) = Y.presheaf.map (i ≫ j) x := by
  rw [Functor.map_comp]; rfl

theorem ring_map_irrel {U V : Y.Opens} (i j : op U ⟶ op V) (x : Y.presheaf.obj (op U)) :
    Y.presheaf.map i x = Y.presheaf.map j x := by rw [op_hom_eq i j]

end P2mWs11Span

open P2mWs11Span in

theorem P2mWs11Span.span_res_eq_top
    {X : Scheme.{u}} (M : X.Modules)
    (htriv : ∀ x : X, ∃ (W : X.Opens), x ∈ W ∧
      Nonempty ((Scheme.Modules.pullback W.ι).obj M ≅ SheafOfModules.unit W.toScheme.ringCatSheaf))
    {U V : X.Opens} (hU : IsAffineOpen U) (hV : IsAffineOpen V) (hVU : V ≤ U) :
    Submodule.span Γ(X, V) (Set.range (fun y : Γ(M, U) => M.presheaf.map (homOfLE hVU).op y)) = ⊤ := by
  classical
  set S : Submodule Γ(X, V) Γ(M, V) :=
    Submodule.span Γ(X, V) (Set.range (fun y : Γ(M, U) => M.presheaf.map (homOfLE hVU).op y)) with hS
  rw [Submodule.eq_top_iff']
  intro s

  have key : ∀ f : Γ(X, U), X.basicOpen f ≤ V →
      ∃ N : ℕ, (X.presheaf.map (homOfLE hVU).op f) ^ N • s ∈ S := by
    intro f hfV
    set g : Γ(X, V) := X.presheaf.map (homOfLE hVU).op f with hg

    obtain ⟨n, y, hy⟩ :=
      (Scheme.Modules.isLocalization_basicOpen_of_locallyTrivial M htriv ⟨U, hU⟩ f).1
        (M.presheaf.map (homOfLE hfV).op s)
    have hgf : X.basicOpen g ≤ X.basicOpen f := by
      rw [hg, Scheme.basicOpen_res]; exact inf_le_right

    set t : Γ(M, V) := g ^ n • s - M.presheaf.map (homOfLE hVU).op y with ht
    have htf : M.presheaf.map (homOfLE hfV).op t = 0 := by
      rw [ht, map_sub, Scheme.Modules.map_smul, map_pow, map_map, hg, ring_map_map, sub_eq_zero,
        ring_map_irrel ((homOfLE hVU).op ≫ (homOfLE hfV).op) (homOfLE (X.basicOpen_le f)).op,
        map_irrel M ((homOfLE hVU).op ≫ (homOfLE hfV).op) (homOfLE (X.basicOpen_le f)).op, hy, map_pow]
    have htg : M.presheaf.map (homOfLE (X.basicOpen_le g)).op t = 0 := by
      rw [map_irrel M (homOfLE (X.basicOpen_le g)).op ((homOfLE hfV).op ≫ (homOfLE hgf).op),
        ← map_map, htf, map_zero]

    obtain ⟨m, hm⟩ :=
      (Scheme.Modules.isLocalization_basicOpen_of_locallyTrivial M htriv ⟨V, hV⟩ g).2 t htg
    refine ⟨m + n, ?_⟩
    have : g ^ (m + n) • s = g ^ m • M.presheaf.map (homOfLE hVU).op y := by
      rw [pow_add, mul_smul, ← sub_eq_zero, ← smul_sub, ← ht]; exact hm
    rw [this]
    exact S.smul_mem _ (Submodule.subset_span ⟨y, rfl⟩)

  suffices h1 : (1 : Γ(X, V)) ∈ S.colon {s} by
    simpa using Submodule.mem_colon_singleton.mp h1
  by_contra h1
  have hI : S.colon {s} ≠ ⊤ := fun h => h1 (h ▸ Submodule.mem_top)
  obtain ⟨𝔪, h𝔪, hI𝔪⟩ := Ideal.exists_le_maximal _ hI

  let p : PrimeSpectrum Γ(X, V) := ⟨𝔪, h𝔪.isPrime⟩
  have hxV : hV.fromSpec p ∈ V := by
    have h : hV.fromSpec p ∈ Set.range (hV.fromSpec : _ → X) := ⟨p, rfl⟩
    rw [hV.range_fromSpec] at h
    exact h

  obtain ⟨f, hfV, hxf⟩ := hU.exists_basicOpen_le ⟨_, hxV⟩ (hVU hxV)
  obtain ⟨N, hN⟩ := key f hfV
  set g : Γ(X, V) := X.presheaf.map (homOfLE hVU).op f with hg
  have hgI : g ^ N ∈ S.colon {s} := Submodule.mem_colon_singleton.mpr hN
  have hg𝔪 : g ∈ 𝔪 := h𝔪.isPrime.mem_of_pow_mem N (hI𝔪 hgI)

  have hxg : hV.fromSpec p ∈ X.basicOpen g := by
    rw [hg, Scheme.basicOpen_res]; exact ⟨hxV, hxf⟩
  have : p ∈ hV.fromSpec ⁻¹ᵁ X.basicOpen g := hxg
  rw [hV.fromSpec_preimage_basicOpen] at this
  exact (PrimeSpectrum.mem_basicOpen g p).mp this hg𝔪

namespace P2mWs11Span

open TensorProduct

variable {X : Scheme.{u}}

theorem algebraMap_basicOpen_apply {U : X.Opens} (f : Γ(X, U)) (x : Γ(X, U)) :
    algebraMap Γ(X, U) Γ(X, X.basicOpen f) x = X.presheaf.map (homOfLE (X.basicOpen_le f)).op x := rfl

theorem exists_pow_mul_eq_algebraMap {U V : X.Opens} (hU : IsAffineOpen U) (hV : IsAffineOpen V)
    (hVU : V ≤ U) [Algebra Γ(X, U) Γ(X, V)]
    (halg : ∀ a, algebraMap Γ(X, U) Γ(X, V) a = X.presheaf.map (homOfLE hVU).op a)
    (h : Γ(X, U)) (hDV : X.basicOpen h ≤ V) (b : Γ(X, V)) :
    ∃ (n : ℕ) (a : Γ(X, U)), algebraMap Γ(X, U) Γ(X, V) h ^ n * b = algebraMap Γ(X, U) Γ(X, V) a := by
  set k : Γ(X, V) := algebraMap Γ(X, U) Γ(X, V) h with hk
  have hk' : k = X.presheaf.map (homOfLE hVU).op h := halg h

  haveI := hU.isLocalization_basicOpen h
  obtain ⟨⟨a, ⟨_, n, rfl⟩⟩, hab⟩ :=
    IsLocalization.surj (Submonoid.powers h) (X.presheaf.map (homOfLE hDV).op b)

  simp only [algebraMap_basicOpen_apply, map_pow] at hab

  set w : Γ(X, V) := k ^ n * b - algebraMap Γ(X, U) Γ(X, V) a with hw
  have hwD : X.presheaf.map (homOfLE hDV).op w = 0 := by
    rw [hw, map_sub, map_mul, map_pow, hk', halg, ring_map_map, ring_map_map, sub_eq_zero,
      ring_map_irrel ((homOfLE hVU).op ≫ (homOfLE hDV).op) (homOfLE (X.basicOpen_le h)).op,
      ring_map_irrel ((homOfLE hVU).op ≫ (homOfLE hDV).op) (homOfLE (X.basicOpen_le h)).op, mul_comm]
    exact hab

  have hkh : X.basicOpen k ≤ X.basicOpen h := by
    rw [hk', Scheme.basicOpen_res]; exact inf_le_right
  have hwD' : X.presheaf.map (homOfLE (X.basicOpen_le k)).op w = 0 := by
    rw [ring_map_irrel (homOfLE (X.basicOpen_le k)).op ((homOfLE hDV).op ≫ (homOfLE hkh).op),
      ← ring_map_map, hwD, map_zero]
  haveI := hV.isLocalization_basicOpen k
  obtain ⟨⟨_, m, rfl⟩, hm⟩ :=
    (IsLocalization.map_eq_zero_iff (Submonoid.powers k) Γ(X, X.basicOpen k) w).mp hwD'

  simp only at hm
  refine ⟨m + n, h ^ m * a, ?_⟩
  rw [map_mul, map_pow, ← hk, pow_add, mul_assoc, ← sub_eq_zero, ← mul_sub]
  convert hm using 2

end P2mWs11Span

namespace P2mWs11Span

open TensorProduct

variable {X : Scheme.{u}}

theorem algebraMap_tmul_eq_one_tmul_smul {A B P : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [AddCommGroup P] [Module A P] (a : A) (p : P) :
    (algebraMap A B a) ⊗ₜ[A] p = (1 : B) ⊗ₜ[A] (a • p) := by
  rw [Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]

theorem algebraMap_pow_smul_one_tmul {A B P : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [AddCommGroup P] [Module A P] (a : A) (n : ℕ) (p : P) :
    (algebraMap A B a) ^ n • ((1 : B) ⊗ₜ[A] p) = (1 : B) ⊗ₜ[A] (a ^ n • p) := by
  rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one, ← map_pow, algebraMap_tmul_eq_one_tmul_smul]

theorem exists_baseChange_equiv (M : X.Modules)
    (htriv : ∀ x : X, ∃ (W : X.Opens), x ∈ W ∧
      Nonempty ((Scheme.Modules.pullback W.ι).obj M ≅ SheafOfModules.unit W.toScheme.ringCatSheaf))
    {U V : X.Opens} (hU : IsAffineOpen U) (hV : IsAffineOpen V) (hVU : V ≤ U)
    [alg : Algebra Γ(X, U) Γ(X, V)]
    (halg : ∀ a, algebraMap Γ(X, U) Γ(X, V) a = X.presheaf.map (homOfLE hVU).op a) :
    ∃ e : Γ(X, V) ⊗[Γ(X, U)] Γ(M, U) ≃ₗ[Γ(X, V)] Γ(M, V),
      ∀ m : Γ(M, U), e ((1 : Γ(X, V)) ⊗ₜ[Γ(X, U)] m) = M.presheaf.map (homOfLE hVU).op m := by
  classical

  letI : Module Γ(X, U) Γ(M, V) := Module.compHom Γ(M, V) (algebraMap Γ(X, U) Γ(X, V))
  haveI : IsScalarTower Γ(X, U) Γ(X, V) Γ(M, V) := IsScalarTower.of_algebraMap_smul fun _ _ => rfl

  let res : Γ(M, U) →ₗ[Γ(X, U)] Γ(M, V) :=
    { toFun := fun m => M.presheaf.map (homOfLE hVU).op m
      map_add' := fun x y => map_add _ x y
      map_smul' := fun a m => by
        simp only [RingHom.id_apply]
        rw [Scheme.Modules.map_smul]
        change _ = (algebraMap Γ(X, U) Γ(X, V) a) • (M.presheaf.map (homOfLE hVU).op m : Γ(M, V))
        rw [halg] }
  have res_apply : ∀ m, res m = M.presheaf.map (homOfLE hVU).op m := fun _ => rfl
  let Φ : Γ(X, V) ⊗[Γ(X, U)] Γ(M, U) →ₗ[Γ(X, V)] Γ(M, V) := res.liftBaseChange Γ(X, V)
  have Φ_tmul : ∀ (b : Γ(X, V)) (m : Γ(M, U)), Φ (b ⊗ₜ m) = b • M.presheaf.map (homOfLE hVU).op m :=
    fun b m => LinearMap.liftBaseChange_tmul _ _ _ _

  have hsurj : Function.Surjective Φ := by
    rw [← LinearMap.range_eq_top, eq_top_iff, ← span_res_eq_top M htriv hU hV hVU, Submodule.span_le]
    rintro _ ⟨m, rfl⟩
    exact ⟨1 ⊗ₜ m, by rw [Φ_tmul, one_smul]⟩

  have hZ : ∀ (h : Γ(X, U)), X.basicOpen h ≤ V → ∀ z : Γ(X, V) ⊗[Γ(X, U)] Γ(M, U),
      ∃ (N : ℕ) (p : Γ(M, U)), (algebraMap Γ(X, U) Γ(X, V) h) ^ N • z = (1 : Γ(X, V)) ⊗ₜ p := by
    intro h hDV z
    induction z using TensorProduct.induction_on with
    | zero => exact ⟨0, 0, by rw [pow_zero, one_smul, tmul_zero]⟩
    | tmul b m =>
      obtain ⟨n, a, hna⟩ := exists_pow_mul_eq_algebraMap hU hV hVU halg h hDV b
      refine ⟨n, a • m, ?_⟩
      rw [TensorProduct.smul_tmul', smul_eq_mul, hna, algebraMap_tmul_eq_one_tmul_smul]
    | add z₁ z₂ ih₁ ih₂ =>
      obtain ⟨N₁, p₁, h₁⟩ := ih₁
      obtain ⟨N₂, p₂, h₂⟩ := ih₂
      refine ⟨N₁ + N₂, h ^ N₂ • p₁ + h ^ N₁ • p₂, ?_⟩
      rw [smul_add, pow_add, mul_smul, mul_smul, h₂, smul_smul, mul_comm, mul_smul, h₁,
        algebraMap_pow_smul_one_tmul, algebraMap_pow_smul_one_tmul, tmul_add]

  have hP : ∀ (h : Γ(X, U)), X.basicOpen h ≤ V → ∀ p : Γ(M, U),
      M.presheaf.map (homOfLE hVU).op p = 0 → ∃ n : ℕ, h ^ n • p = 0 := by
    intro h hDV p hp
    refine (Scheme.Modules.isLocalization_basicOpen_of_locallyTrivial M htriv ⟨U, hU⟩ h).2 p ?_
    rw [map_irrel M (homOfLE (X.basicOpen_le h)).op ((homOfLE hVU).op ≫ (homOfLE hDV).op),
      ← map_map, hp, map_zero]

  have hinj : Function.Injective Φ := by
    rw [injective_iff_map_eq_zero]
    intro z hz
    suffices h1 : (1 : Γ(X, V)) ∈ (⊥ : Submodule Γ(X, V) (Γ(X, V) ⊗[Γ(X, U)] Γ(M, U))).colon {z} by
      simpa using Submodule.mem_colon_singleton.mp h1
    by_contra h1
    have hI : (⊥ : Submodule Γ(X, V) (Γ(X, V) ⊗[Γ(X, U)] Γ(M, U))).colon {z} ≠ ⊤ :=
      fun h => h1 (h ▸ Submodule.mem_top)
    obtain ⟨𝔪, h𝔪, hI𝔪⟩ := Ideal.exists_le_maximal _ hI
    let pt : PrimeSpectrum Γ(X, V) := ⟨𝔪, h𝔪.isPrime⟩
    have hxV : hV.fromSpec pt ∈ V := by
      have h : hV.fromSpec pt ∈ Set.range (hV.fromSpec : _ → X) := ⟨pt, rfl⟩
      rw [hV.range_fromSpec] at h
      exact h
    obtain ⟨h, hDV, hxh⟩ := hU.exists_basicOpen_le ⟨_, hxV⟩ (hVU hxV)
    obtain ⟨N, p, hNp⟩ := hZ h hDV z
    have hp0 : M.presheaf.map (homOfLE hVU).op p = 0 := by
      have := congrArg Φ hNp
      simp only [map_smul, hz, smul_zero] at this
      rw [Φ_tmul, one_smul] at this
      exact this.symm
    obtain ⟨n, hn⟩ := hP h hDV p hp0
    have hkz : (algebraMap Γ(X, U) Γ(X, V) h) ^ (n + N) • z = 0 := by
      rw [pow_add, mul_smul, hNp, algebraMap_pow_smul_one_tmul, hn, tmul_zero]
    have hkI : (algebraMap Γ(X, U) Γ(X, V) h) ^ (n + N) ∈
        (⊥ : Submodule Γ(X, V) (Γ(X, V) ⊗[Γ(X, U)] Γ(M, U))).colon {z} :=
      Submodule.mem_colon_singleton.mpr (by rw [hkz]; exact Submodule.zero_mem _)
    have hk𝔪 : algebraMap Γ(X, U) Γ(X, V) h ∈ 𝔪 := h𝔪.isPrime.mem_of_pow_mem _ (hI𝔪 hkI)
    have hxk : hV.fromSpec pt ∈ X.basicOpen (algebraMap Γ(X, U) Γ(X, V) h) := by
      rw [halg, Scheme.basicOpen_res]; exact ⟨hxV, hxh⟩
    have : pt ∈ hV.fromSpec ⁻¹ᵁ X.basicOpen (algebraMap Γ(X, U) Γ(X, V) h) := hxk
    rw [hV.fromSpec_preimage_basicOpen] at this
    exact (PrimeSpectrum.mem_basicOpen _ pt).mp this hk𝔪
  exact ⟨LinearEquiv.ofBijective Φ ⟨hinj, hsurj⟩, fun m => by
    rw [LinearEquiv.ofBijective_apply, Φ_tmul, one_smul]⟩

end P2mWs11Span

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct in
theorem solution
    {R : Type u} [CommRing R] {X : Scheme.{u}} (𝒱 : X.TwoAffineOpenCover) (c : X ⟶ Spec (.of R))
    (M : X.Modules) (hM : Scheme.Modules.IsInvertible M) :
    letI : Algebra (𝒱.cover c).A0 (𝒱.cover c).A01 := (𝒱.cover c).ρ0.toRingHom.toAlgebra
    letI : Algebra (𝒱.cover c).A1 (𝒱.cover c).A01 := (𝒱.cover c).ρ1.toRingHom.toAlgebra
    ∃ (rbc0 : (𝒱.cover c).A01 ⊗[(𝒱.cover c).A0] (𝒱.sectionsOf c M).M0 ≃ₗ[(𝒱.cover c).A01]
                (𝒱.sectionsOf c M).M01)
      (rbc1 : (𝒱.cover c).A01 ⊗[(𝒱.cover c).A1] (𝒱.sectionsOf c M).M1 ≃ₗ[(𝒱.cover c).A01]
                (𝒱.sectionsOf c M).M01),
      (∀ m, rbc0 ((1 : (𝒱.cover c).A01) ⊗ₜ[(𝒱.cover c).A0] m) = (𝒱.sectionsOf c M).r0 m) ∧
      (∀ m, rbc1 ((1 : (𝒱.cover c).A01) ⊗ₜ[(𝒱.cover c).A1] m) = (𝒱.sectionsOf c M).r1 m) := by
  letI alg0 : Algebra (𝒱.cover c).A0 (𝒱.cover c).A01 := (𝒱.cover c).ρ0.toRingHom.toAlgebra
  letI alg1 : Algebra (𝒱.cover c).A1 (𝒱.cover c).A01 := (𝒱.cover c).ρ1.toRingHom.toAlgebra
  obtain ⟨e0, he0⟩ := P2mWs11Span.exists_baseChange_equiv (alg := alg0) M hM.exists_trivialization
    𝒱.isAffineOpen_U0 𝒱.isAffineOpen_inf inf_le_left (fun _ => rfl)
  obtain ⟨e1, he1⟩ := P2mWs11Span.exists_baseChange_equiv (alg := alg1) M hM.exists_trivialization
    𝒱.isAffineOpen_U1 𝒱.isAffineOpen_inf inf_le_right (fun _ => rfl)
  exact ⟨e0, e1, he0, he1⟩

end S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_sectionsOf_overlap_linearEquiv_baseChange_of_isInvertible
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_sectionsOf_overlap_linearEquiv_baseChange_of_isInvertible (solution)
