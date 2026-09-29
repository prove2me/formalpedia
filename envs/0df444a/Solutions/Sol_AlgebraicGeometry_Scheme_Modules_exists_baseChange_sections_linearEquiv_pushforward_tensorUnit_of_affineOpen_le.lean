-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.Modules.exists_baseChange_sections_linearEquiv_pushforward_tensorUnit_of_affineOpen_le
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/90766d58-28a7-5920-a604-4fb83c538101

import Mathlib
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_baseChange_sections_linearEquiv_pushforward_tensorUnit_of_affineOpen_le

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 80000

universe u

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace

namespace P2mWs11RBC

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

end P2mWs11RBC

open P2mWs11RBC in

theorem P2mWs11RBC.span_res_eq_top
    {X : Scheme.{u}} (M : X.Modules)
    (hloc : ∀ (W : X.affineOpens) (f : Γ(X, W.1)),
      (∀ x : Γ(M, X.basicOpen f), ∃ (n : ℕ) (y : Γ(M, W.1)),
          M.presheaf.map (homOfLE (X.basicOpen_le f)).op y
            = X.presheaf.map (homOfLE (X.basicOpen_le f)).op (f ^ n) • x)
        ∧ (∀ y : Γ(M, W.1), M.presheaf.map (homOfLE (X.basicOpen_le f)).op y = 0 →
            ∃ n : ℕ, (f ^ n : Γ(X, W.1)) • y = 0))
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
      (hloc ⟨U, hU⟩ f).1
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
      (hloc ⟨V, hV⟩ g).2 t htg
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

namespace P2mWs11RBC

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

end P2mWs11RBC

namespace P2mWs11RBC

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
    (hloc : ∀ (W : X.affineOpens) (f : Γ(X, W.1)),
      (∀ x : Γ(M, X.basicOpen f), ∃ (n : ℕ) (y : Γ(M, W.1)),
          M.presheaf.map (homOfLE (X.basicOpen_le f)).op y
            = X.presheaf.map (homOfLE (X.basicOpen_le f)).op (f ^ n) • x)
        ∧ (∀ y : Γ(M, W.1), M.presheaf.map (homOfLE (X.basicOpen_le f)).op y = 0 →
            ∃ n : ℕ, (f ^ n : Γ(X, W.1)) • y = 0))
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
    rw [← LinearMap.range_eq_top, eq_top_iff, ← span_res_eq_top M hloc hU hV hVU, Submodule.span_le]
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
    refine (hloc ⟨U, hU⟩ h).2 p ?_
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

end P2mWs11RBC

namespace P2mWs11RBC

variable {X Y : Scheme.{u}}

noncomputable abbrev Mu (π : Y ⟶ X) : X.Modules :=
  (Scheme.Modules.pushforward π).obj (SheafOfModules.unit Y.ringCatSheaf)

theorem ring_map_endo {U : Y.Opens} (i : op U ⟶ op U) (x : Γ(Y, U)) : Y.presheaf.map i x = x := by
  rw [op_hom_eq i (𝟙 _), CategoryTheory.Functor.map_id]; rfl

theorem app_res_apply (π : Y ⟶ X) {U V : X.Opens} (i : U ⟶ V) (r : Γ(X, V)) :
    (π.app U).hom ((X.presheaf.map i.op).hom r) =
      (Y.presheaf.map ((Opens.map π.base).map i).op).hom ((π.app V).hom r) := by
  have h := π.naturality i.op
  have := congrArg (fun φ => φ.hom r) h
  simpa [CommRingCat.hom_comp] using this

theorem pushforwardUnit_loc (π : Y ⟶ X) (W : X.affineOpens) (hW' : IsAffineOpen (π ⁻¹ᵁ W.1))
    (f : Γ(X, W.1)) :
    ((∀ x : Γ(Mu π, X.basicOpen f), ∃ (n : ℕ) (y : Γ(Mu π, W.1)),
          (Mu π).presheaf.map (homOfLE (X.basicOpen_le f)).op y
            = X.presheaf.map (homOfLE (X.basicOpen_le f)).op (f ^ n) • x)
        ∧ (∀ y : Γ(Mu π, W.1), (Mu π).presheaf.map (homOfLE (X.basicOpen_le f)).op y = 0 →
            ∃ n : ℕ, (f ^ n : Γ(X, W.1)) • y = 0)) := by

  set g : Γ(Y, π ⁻¹ᵁ W.1) := (π.app W.1).hom f with hg
  have hEq : π ⁻¹ᵁ X.basicOpen f = Y.basicOpen g := Scheme.preimage_basicOpen π f
  haveI hloc := hW'.isLocalization_basicOpen g

  have halg : ∀ z : Γ(Y, π ⁻¹ᵁ W.1), algebraMap Γ(Y, π ⁻¹ᵁ W.1) Γ(Y, Y.basicOpen g) z =
      Y.presheaf.map (homOfLE (Y.basicOpen_le g)).op z := fun _ => rfl
  set j : π ⁻¹ᵁ X.basicOpen f ⟶ π ⁻¹ᵁ W.1 := (Opens.map π.base).map (homOfLE (X.basicOpen_le f)) with hj
  refine ⟨fun x => ?_, fun y hy => ?_⟩
  ·
    set xr : Γ(Y, π ⁻¹ᵁ X.basicOpen f) := x with hxr
    set x' : Γ(Y, Y.basicOpen g) := Y.presheaf.map (homOfLE hEq.ge).op xr with hx'
    obtain ⟨⟨y, ⟨_, n, rfl⟩⟩, hy⟩ := IsLocalization.surj (Submonoid.powers g) x'
    refine ⟨n, y, ?_⟩

    simp only [] at hy
    rw [halg, halg] at hy

    have hy' := congrArg (fun z => Y.presheaf.map (homOfLE hEq.le).op z) hy
    simp only [map_mul, ring_map_map] at hy'
    rw [hx', ring_map_map, ring_map_endo] at hy'

    change (Y.presheaf.map j.op).hom y =
      (π.app (X.basicOpen f)).hom ((X.presheaf.map (homOfLE (X.basicOpen_le f)).op).hom (f ^ n)) * xr
    rw [app_res_apply, map_pow, ← hg, mul_comm, ← hj]
    rw [ring_map_irrel ((homOfLE (Y.basicOpen_le g)).op ≫ (homOfLE hEq.le).op) j.op,
      ring_map_irrel ((homOfLE (Y.basicOpen_le g)).op ≫ (homOfLE hEq.le).op) j.op] at hy'
    exact hy'.symm
  ·
    have hy0 : (Y.presheaf.map j.op).hom (show Γ(Y, π ⁻¹ᵁ W.1) from y) = 0 := hy
    have hy1 : algebraMap Γ(Y, π ⁻¹ᵁ W.1) Γ(Y, Y.basicOpen g) (show Γ(Y, π ⁻¹ᵁ W.1) from y) = 0 := by
      rw [halg, ring_map_irrel (homOfLE (Y.basicOpen_le g)).op (j.op ≫ (homOfLE hEq.ge).op),
        ← ring_map_map]
      change (Y.presheaf.map (homOfLE hEq.ge).op).hom ((Y.presheaf.map j.op).hom _) = 0
      rw [hy0, map_zero]
    obtain ⟨⟨_, n, rfl⟩, hn⟩ := (IsLocalization.map_eq_zero_iff (Submonoid.powers g) _ _).mp hy1
    refine ⟨n, ?_⟩
    change (π.app W.1).hom (f ^ n) * (show Γ(Y, π ⁻¹ᵁ W.1) from y) = 0
    rw [map_pow, ← hg]
    exact hn

open TensorProduct in

theorem mainU {X Y : Scheme.{u}} (π : Y ⟶ X) [IsAffineHom π]
    {U V : X.Opens} (hU : IsAffineOpen U) (hV : IsAffineOpen V) (hVU : V ≤ U) :
    letI : Algebra Γ(X, U) Γ(X, V) := (X.presheaf.map (homOfLE hVU).op).hom.toAlgebra
    ∃ e : Γ(X, V) ⊗[Γ(X, U)] Γ(Mu π, U) ≃ₗ[Γ(X, V)] Γ(Mu π, V),
      ∀ m : Γ(Mu π, U), e ((1 : Γ(X, V)) ⊗ₜ[Γ(X, U)] m) = (Mu π).presheaf.map (homOfLE hVU).op m := by
  letI alg : Algebra Γ(X, U) Γ(X, V) := (X.presheaf.map (homOfLE hVU).op).hom.toAlgebra
  exact exists_baseChange_equiv (alg := alg) (Mu π)
    (fun W f => pushforwardUnit_loc π W (W.2.preimage π) f) hU hV hVU (fun _ => rfl)

end P2mWs11RBC

open CategoryTheory _root_.CategoryTheory.MonoidalCategory AlgebraicGeometry TensorProduct in
theorem solution
    {X Y : Scheme.{u}} (π : Y ⟶ X) [IsAffineHom π]
    {U V : X.Opens} (hU : IsAffineOpen U) (hV : IsAffineOpen V) (hVU : V ≤ U) :
    letI : Algebra Γ(X, U) Γ(X, V) := (X.presheaf.map (homOfLE hVU).op).hom.toAlgebra
    ∃ e : Γ(X, V) ⊗[Γ(X, U)] Γ((Scheme.Modules.pushforward π).obj (𝟙_ Y.Modules), U) ≃ₗ[Γ(X, V)]
        Γ((Scheme.Modules.pushforward π).obj (𝟙_ Y.Modules), V),
      ∀ m : Γ((Scheme.Modules.pushforward π).obj (𝟙_ Y.Modules), U),
        e ((1 : Γ(X, V)) ⊗ₜ[Γ(X, U)] m) =
          ((Scheme.Modules.pushforward π).obj (𝟙_ Y.Modules)).presheaf.map (homOfLE hVU).op m := by
  exact P2mWs11RBC.mainU π hU hV hVU

end S_AlgebraicGeometry_Scheme_Modules_exists_baseChange_sections_linearEquiv_pushforward_tensorUnit_of_affineOpen_le
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_baseChange_sections_linearEquiv_pushforward_tensorUnit_of_affineOpen_le (solution)
