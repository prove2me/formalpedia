-- Prove2me | solution 1 for AlgebraicGeometry.OModulePresheaf.exists_affHom_apply_eq_smul_comm_iSup_range_eq_top_of_forall_ker_eq_pow_smul_top
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/89dc9aab-8016-561d-82ec-cc4285478b73

import Mathlib
import Definitions.Def_AlgebraicGeometry_OModulePresheafHom
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_affHom_apply_eq_smul_comm_iSup_range_eq_top_of_forall_ker_eq_pow_smul_top

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry

universe u

namespace P2mGrStruct

p2m_open "AlgebraicGeometry.OModulePresheaf"

section Generic

variable {A : Type*} [CommRing A]

theorem pow_smul_top_eq_bot {M M' : Type*} [AddCommGroup M] [Module A M] [AddCommGroup M'] [Module A M']
    (J : Ideal A) (f : M →ₗ[A] M') (hf : Function.Surjective f)
    (hk : LinearMap.ker f = J • (⊤ : Submodule A M)) : J • (⊤ : Submodule A M') = ⊥ := by
  have hmap : (J • (⊤ : Submodule A M)).map f = J • (⊤ : Submodule A M') := by
    rw [Submodule.map_smul'', Submodule.map_top, LinearMap.range_eq_top.mpr hf]
  rw [← hmap, ← hk]
  exact le_bot_iff.mp (Submodule.map_le_iff_le_comap.mpr (by rw [Submodule.comap_bot]))

theorem map_mem_smul_top {M M' : Type*} [AddCommGroup M] [Module A M] [AddCommGroup M'] [Module A M']
    (J : Ideal A) (f : M →ₗ[A] M') {x : M} (hx : x ∈ J • (⊤ : Submodule A M)) :
    f x ∈ J • (⊤ : Submodule A M') := by
  have h := Submodule.mem_map_of_mem (f := f) hx
  rw [Submodule.map_smul''] at h
  exact Submodule.smul_mono le_rfl le_top h

theorem smul_mem_pow_succ_smul_top {M : Type*} [AddCommGroup M] [Module A M] (J : Ideal A) (n : ℕ)
    {a : A} (ha : a ∈ J) {x : M} (hx : x ∈ J ^ n • (⊤ : Submodule A M)) :
    a • x ∈ J ^ (n + 1) • (⊤ : Submodule A M) := by
  rw [pow_succ', Submodule.mul_smul]
  exact Submodule.smul_mem_smul ha hx

end Generic

structure Sys (A : Type u) [CommRing A] {V : Scheme.{u}} (π : V ⟶ Spec (.of A)) where

  I : Ideal A

  s : ℕ

  g : Fin s → A
  hg : Ideal.span (Set.range g) = I

  F : ℕ → OModulePresheaf π

  φ : ∀ k, AffHom (F (k + 1)) (F k)
  hφs : ∀ (k : ℕ) (U : V.affineOpens), Function.Surjective ((φ k).app U)
  hφk : ∀ (k : ℕ) (U : V.affineOpens),
    LinearMap.ker ((φ k).app U) = I ^ (k + 1) • (⊤ : Submodule A ((F (k + 1)).obj U.1))

  K : ℕ → OModulePresheaf π

  j : ∀ k, AffHom (K k) (F (k + 1))
  hji : ∀ (k : ℕ) (U : V.affineOpens), Function.Injective ((j k).app U)
  hjr : ∀ (k : ℕ) (U : V.affineOpens), LinearMap.range ((j k).app U) = LinearMap.ker ((φ k).app U)

variable {A : Type u} [CommRing A] {V : Scheme.{u}} {π : V ⟶ Spec (.of A)} (S : Sys A π)

namespace Sys

theorem pow_smul_top (n : ℕ) (U : V.affineOpens) :
    S.I ^ (n + 1) • (⊤ : Submodule A ((S.F n).obj U.1)) = ⊥ :=
  pow_smul_top_eq_bot _ ((S.φ n).app U) (S.hφs n U) (S.hφk n U)

theorem smul_eq_zero_of_mem {n : ℕ} {U : V.affineOpens} {a : A} (ha : a ∈ S.I) {x : (S.F n).obj U.1}
    (hx : x ∈ S.I ^ n • (⊤ : Submodule A ((S.F n).obj U.1))) : a • x = 0 := by
  have h := smul_mem_pow_succ_smul_top S.I n ha hx
  rw [S.pow_smul_top n U, Submodule.mem_bot] at h
  exact h

theorem g_mem (m : Fin S.s) : S.g m ∈ S.I := by
  rw [← S.hg]; exact Ideal.subset_span ⟨m, rfl⟩

theorem j_mem_pow (k : ℕ) (U : V.affineOpens) (x : (S.K k).obj U.1) :
    (S.j k).app U x ∈ S.I ^ (k + 1) • (⊤ : Submodule A ((S.F (k + 1)).obj U.1)) := by
  rw [← S.hφk k U, ← S.hjr k U]; exact LinearMap.mem_range_self _ x

theorem sections_smul_comm (G : OModulePresheaf π) (U : V.Opens) (a : A) (f : Γ(V, U)) (x : G.obj U) :
    f • (a • x) = a • (f • x) := by
  letI := Scheme.TwoAffineOpenCover.algebraOfHom π U
  haveI : IsScalarTower A Γ(V, U) (G.obj U) := G.isScalarTower U
  exact smul_algebra_smul_comm a f x

theorem smul_lift_mem_range (m : Fin S.s) (k : ℕ) (U : V.affineOpens) (x : (S.K k).obj U.1)
    {y : (S.F (k + 1 + 1)).obj U.1} (hy : (S.φ (k + 1)).app U y = (S.j k).app U x) :
    S.g m • y ∈ LinearMap.range ((S.j (k + 1)).app U) := by
  rw [S.hjr (k + 1) U, LinearMap.mem_ker, LinearMap.map_smul, hy]
  exact S.smul_eq_zero_of_mem (S.g_mem m) (S.j_mem_pow k U x)

theorem smul_lift_eq (m : Fin S.s) (k : ℕ) (U : V.affineOpens) (x : (S.K k).obj U.1)
    {y y' : (S.F (k + 1 + 1)).obj U.1} (hy : (S.φ (k + 1)).app U y = (S.j k).app U x)
    (hy' : (S.φ (k + 1)).app U y' = (S.j k).app U x) : S.g m • y = S.g m • y' := by
  rw [← sub_eq_zero, ← smul_sub]
  refine S.smul_eq_zero_of_mem (S.g_mem m) ?_
  rw [← S.hφk (k + 1) U, LinearMap.mem_ker, map_sub, hy, hy', sub_self]

theorem exists_lift (k : ℕ) (U : V.affineOpens) (x : (S.K k).obj U.1) :
    ∃ y : (S.F (k + 1 + 1)).obj U.1, (S.φ (k + 1)).app U y = (S.j k).app U x :=
  S.hφs (k + 1) U _

noncomputable def thetaFun (m : Fin S.s) (k : ℕ) (U : V.affineOpens) (x : (S.K k).obj U.1) : (S.K (k + 1)).obj U.1 :=
  Classical.choose (LinearMap.mem_range.mp
    (S.smul_lift_mem_range m k U x (Classical.choose_spec (S.exists_lift k U x))))

theorem j_thetaFun (m : Fin S.s) (k : ℕ) (U : V.affineOpens) (x : (S.K k).obj U.1)
    {y : (S.F (k + 1 + 1)).obj U.1} (hy : (S.φ (k + 1)).app U y = (S.j k).app U x) :
    (S.j (k + 1)).app U (S.thetaFun m k U x) = S.g m • y := by
  rw [thetaFun, Classical.choose_spec (LinearMap.mem_range.mp
    (S.smul_lift_mem_range m k U x (Classical.choose_spec (S.exists_lift k U x))))]
  exact S.smul_lift_eq m k U x (Classical.choose_spec (S.exists_lift k U x)) hy

theorem thetaFun_add (m : Fin S.s) (k : ℕ) (U : V.affineOpens) (x x' : (S.K k).obj U.1) :
    S.thetaFun m k U (x + x') = S.thetaFun m k U x + S.thetaFun m k U x' := by
  obtain ⟨y, hy⟩ := S.exists_lift k U x
  obtain ⟨y', hy'⟩ := S.exists_lift k U x'
  apply S.hji (k + 1) U
  rw [map_add, S.j_thetaFun m k U x hy, S.j_thetaFun m k U x' hy',
    S.j_thetaFun m k U (x + x') (y := y + y') (by rw [map_add, map_add, hy, hy']), smul_add]

theorem thetaFun_smul (m : Fin S.s) (k : ℕ) (U : V.affineOpens) (a : A) (x : (S.K k).obj U.1) :
    S.thetaFun m k U (a • x) = a • S.thetaFun m k U x := by
  obtain ⟨y, hy⟩ := S.exists_lift k U x
  apply S.hji (k + 1) U
  rw [LinearMap.map_smul, S.j_thetaFun m k U x hy,
    S.j_thetaFun m k U (a • x) (y := a • y) (by rw [LinearMap.map_smul, LinearMap.map_smul, hy]), smul_comm]

theorem thetaFun_sectionSmul (m : Fin S.s) (k : ℕ) (U : V.affineOpens) (f : Γ(V, U.1)) (x : (S.K k).obj U.1) :
    S.thetaFun m k U (f • x) = f • S.thetaFun m k U x := by
  obtain ⟨y, hy⟩ := S.exists_lift k U x
  apply S.hji (k + 1) U
  rw [(S.j (k + 1)).app_smul, S.j_thetaFun m k U x hy,
    S.j_thetaFun m k U (f • x) (y := f • y) (by rw [(S.φ (k + 1)).app_smul, (S.j k).app_smul, hy]),
    sections_smul_comm]

theorem thetaFun_res (m : Fin S.s) (k : ℕ) {U U' : V.affineOpens} (h : U.1 ≤ U'.1) (x : (S.K k).obj U'.1) :
    S.thetaFun m k U ((S.K k).res h x) = (S.K (k + 1)).res h (S.thetaFun m k U' x) := by
  obtain ⟨y, hy⟩ := S.exists_lift k U' x
  apply S.hji (k + 1) U
  rw [(S.j (k + 1)).naturality_apply h, S.j_thetaFun m k U' x hy, LinearMap.map_smul,
    S.j_thetaFun m k U ((S.K k).res h x) (y := (S.F (k + 1 + 1)).res h y)
      (by rw [(S.φ (k + 1)).naturality_apply h, hy, (S.j k).naturality_apply h])]

noncomputable def theta (m : Fin S.s) (k : ℕ) : AffHom (S.K k) (S.K (k + 1)) where
  app U :=
    { toFun := S.thetaFun m k U
      map_add' := S.thetaFun_add m k U
      map_smul' := S.thetaFun_smul m k U }
  app_smul U f x := S.thetaFun_sectionSmul m k U f x
  naturality h := LinearMap.ext fun x => S.thetaFun_res m k h x

theorem theta_app (m : Fin S.s) (k : ℕ) (U : V.affineOpens) (x : (S.K k).obj U.1) :
    (S.theta m k).app U x = S.thetaFun m k U x := rfl

theorem j_theta (m : Fin S.s) (k : ℕ) (U : V.affineOpens) (x : (S.K k).obj U.1)
    {y : (S.F (k + 1 + 1)).obj U.1} (hy : (S.φ (k + 1)).app U y = (S.j k).app U x) :
    (S.j (k + 1)).app U ((S.theta m k).app U x) = S.g m • y :=
  S.j_thetaFun m k U x hy

theorem theta_comm (m m' : Fin S.s) (k : ℕ) (U : V.affineOpens) (x : (S.K k).obj U.1) :
    (S.theta m (k + 1)).app U ((S.theta m' k).app U x) = (S.theta m' (k + 1)).app U ((S.theta m k).app U x) := by
  obtain ⟨y, hy⟩ := S.exists_lift k U x
  obtain ⟨w, hw⟩ := S.hφs (k + 1 + 1) U y

  have h1 : (S.φ (k + 1 + 1)).app U (S.g m' • w) = (S.j (k + 1)).app U ((S.theta m' k).app U x) := by
    rw [LinearMap.map_smul, hw, S.j_theta m' k U x hy]
  have h2 : (S.φ (k + 1 + 1)).app U (S.g m • w) = (S.j (k + 1)).app U ((S.theta m k).app U x) := by
    rw [LinearMap.map_smul, hw, S.j_theta m k U x hy]
  apply S.hji (k + 1 + 1) U
  rw [S.j_theta m (k + 1) U _ h1, S.j_theta m' (k + 1) U _ h2, smul_comm]

theorem smul_mem_map_range (m : Fin S.s) (k : ℕ) (U : V.affineOpens) {n : (S.F (k + 1 + 1)).obj U.1}
    (hn : n ∈ S.I ^ (k + 1) • (⊤ : Submodule A ((S.F (k + 1 + 1)).obj U.1))) :
    S.g m • n ∈ (LinearMap.range ((S.theta m k).app U)).map ((S.j (k + 1)).app U) := by

  have h1 : (S.φ (k + 1)).app U n ∈ LinearMap.range ((S.j k).app U) := by
    rw [S.hjr k U, S.hφk k U]
    exact map_mem_smul_top _ ((S.φ (k + 1)).app U) hn
  obtain ⟨x, hx⟩ := LinearMap.mem_range.mp h1
  exact ⟨(S.theta m k).app U x, LinearMap.mem_range_self _ x, S.j_theta m k U x hx.symm⟩

theorem pow_smul_top_le_map_iSup (k : ℕ) (U : V.affineOpens) :
    S.I ^ (k + 1 + 1) • (⊤ : Submodule A ((S.F (k + 1 + 1)).obj U.1)) ≤
      (⨆ m : Fin S.s, LinearMap.range ((S.theta m k).app U)).map ((S.j (k + 1)).app U) := by
  rw [pow_succ', Submodule.mul_smul, Submodule.smul_le]
  intro a ha n hn
  rw [← S.hg] at ha
  induction ha using Submodule.span_induction generalizing n with
  | mem b hb =>
    obtain ⟨m, rfl⟩ := hb
    exact Submodule.map_mono (le_iSup (fun m' : Fin S.s => LinearMap.range ((S.theta m' k).app U)) m)
      (S.smul_mem_map_range m k U hn)
  | zero => rw [zero_smul]; exact Submodule.zero_mem _
  | add b b' _ _ hb hb' => rw [add_smul]; exact Submodule.add_mem _ (hb n hn) (hb' n hn)
  | smul c b _ hb => rw [smul_eq_mul, mul_smul]; exact Submodule.smul_mem _ c (hb n hn)

theorem iSup_range_theta (k : ℕ) (U : V.affineOpens) :
    (⨆ m : Fin S.s, LinearMap.range ((S.theta m k).app U)) = ⊤ := by
  refine eq_top_iff.mpr fun z _ => ?_
  have hz : (S.j (k + 1)).app U z ∈
      (⨆ m : Fin S.s, LinearMap.range ((S.theta m k).app U)).map ((S.j (k + 1)).app U) :=
    S.pow_smul_top_le_map_iSup k U (S.j_mem_pow (k + 1) U z)
  obtain ⟨z', hz', hzz'⟩ := hz
  rwa [← S.hji (k + 1) U hzz']

end Sys

end P2mGrStruct

open _root_.AlgebraicGeometry.OModulePresheaf in
theorem solution
    {A : Type u} [CommRing A] (I : Ideal A) {s : ℕ} (g : Fin s → A) (hg : Ideal.span (Set.range g) = I)
    {V : Scheme.{u}} {π : V ⟶ Spec (CommRingCat.of A)}
    (F : ℕ → OModulePresheaf π) (φ : ∀ k, OModulePresheaf.AffHom (F (k + 1)) (F k))
    (hφs : ∀ (k : ℕ) (U : V.affineOpens), Function.Surjective ((φ k).app U))
    (hφk : ∀ (k : ℕ) (U : V.affineOpens),
      LinearMap.ker ((φ k).app U) = I ^ (k + 1) • (⊤ : Submodule A ((F (k + 1)).obj U.1)))
    (K : ℕ → OModulePresheaf π) (j : ∀ k, OModulePresheaf.AffHom (K k) (F (k + 1)))
    (hji : ∀ (k : ℕ) (U : V.affineOpens), Function.Injective ((j k).app U))
    (hjr : ∀ (k : ℕ) (U : V.affineOpens), LinearMap.range ((j k).app U) = LinearMap.ker ((φ k).app U)) :
    ∃ θ : Fin s → ∀ k : ℕ, OModulePresheaf.AffHom (K k) (K (k + 1)),
      (∀ (m : Fin s) (k : ℕ) (U : V.affineOpens) (x : (K k).obj U.1) (y : (F (k + 1 + 1)).obj U.1),
          (φ (k + 1)).app U y = (j k).app U x → (j (k + 1)).app U ((θ m k).app U x) = g m • y) ∧
      (∀ (m m' : Fin s) (k : ℕ) (U : V.affineOpens) (x : (K k).obj U.1),
          (θ m (k + 1)).app U ((θ m' k).app U x) = (θ m' (k + 1)).app U ((θ m k).app U x)) ∧
      (∀ (k : ℕ) (U : V.affineOpens), (⨆ m : Fin s, LinearMap.range ((θ m k).app U)) = ⊤) := by
  let S : P2mGrStruct.Sys A π :=
    { I := I, s := s, g := g, hg := hg, F := F, φ := φ, hφs := hφs, hφk := hφk, K := K, j := j, hji := hji, hjr := hjr }
  exact ⟨fun m k => S.theta m k, fun m k U x y hy => S.j_theta m k U x hy, fun m m' k U x => S.theta_comm m m' k U x,
    fun k U => S.iSup_range_theta k U⟩

end S_AlgebraicGeometry_OModulePresheaf_exists_affHom_apply_eq_smul_comm_iSup_range_eq_top_of_forall_ker_eq_pow_smul_top
end P2MW
export P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_affHom_apply_eq_smul_comm_iSup_range_eq_top_of_forall_ker_eq_pow_smul_top (solution)
