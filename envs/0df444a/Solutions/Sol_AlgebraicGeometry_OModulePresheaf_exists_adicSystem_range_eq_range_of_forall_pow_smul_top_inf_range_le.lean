-- Prove2me | solution 1 for AlgebraicGeometry.OModulePresheaf.exists_adicSystem_range_eq_range_of_forall_pow_smul_top_inf_range_le
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/59b2cee5-0ef7-5bdf-9115-8409ac157393

import Mathlib
import Definitions.Def_AlgebraicGeometry_OModulePresheafHom
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_adicSystem_range_eq_range_of_forall_pow_smul_top_inf_range_le

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

namespace AdicEnvelopeSol

p2m_open "AlgebraicGeometry.OModulePresheaf"

section Generic

variable {A : Type*} [CommRing A]

theorem map_mem_smul_top {M M' : Type*} [AddCommGroup M] [Module A M] [AddCommGroup M'] [Module A M']
    (J : Ideal A) (g : M →ₗ[A] M') {x : M} (hx : x ∈ J • (⊤ : Submodule A M)) :
    g x ∈ J • (⊤ : Submodule A M') := by
  have h := Submodule.mem_map_of_mem (f := g) hx
  rw [Submodule.map_smul''] at h
  exact Submodule.smul_mono le_rfl le_top h

theorem map_smul_top_of_surjective {M M' : Type*} [AddCommGroup M] [Module A M] [AddCommGroup M']
    [Module A M'] (J : Ideal A) (g : M →ₗ[A] M') (hg : Function.Surjective g) :
    (J • (⊤ : Submodule A M)).map g = J • (⊤ : Submodule A M') := by
  rw [Submodule.map_smul'', Submodule.map_top, LinearMap.range_eq_top.mpr hg]

theorem pow_smul_top_eq_bot {M M' : Type*} [AddCommGroup M] [Module A M] [AddCommGroup M'] [Module A M']
    (J : Ideal A) (g : M →ₗ[A] M') (hg : Function.Surjective g)
    (hk : LinearMap.ker g = J • (⊤ : Submodule A M)) : J • (⊤ : Submodule A M') = ⊥ := by
  rw [← map_smul_top_of_surjective J g hg, ← hk]
  exact le_bot_iff.mp (Submodule.map_le_iff_le_comap.mpr (by rw [Submodule.comap_bot]))

end Generic

section Trunc

variable {A : Type u} [CommRing A] (I : Ideal A) {P : Scheme.{u}} {q : P ⟶ Spec (.of A)}
variable (E : OModulePresheaf q)

def T (k : ℕ) (U : P.Opens) : Submodule A (E.obj U) := I ^ (k + 1) • ⊤

theorem T_def (k : ℕ) (U : P.Opens) : T I E k U = I ^ (k + 1) • (⊤ : Submodule A (E.obj U)) := rfl

theorem T_smul_mem (k : ℕ) (U : P.Opens) (a : Γ(P, U)) {x : E.obj U} (hx : x ∈ T I E k U) :
    a • x ∈ T I E k U := by
  letI := Scheme.TwoAffineOpenCover.algebraOfHom q U
  haveI : IsScalarTower A Γ(P, U) (E.obj U) := E.isScalarTower U
  refine Submodule.smul_induction_on hx (fun i hi y _ => ?_) (fun x y hx hy => ?_)
  · rw [T_def, smul_algebra_smul_comm i a y]
    exact Submodule.smul_mem_smul hi Submodule.mem_top
  · rw [smul_add]; exact add_mem hx hy

theorem T_res {U U' : P.Opens} (hle : U ≤ U') (k : ℕ) {x : E.obj U'} (hx : x ∈ T I E k U') :
    E.res hle x ∈ T I E k U :=
  map_mem_smul_top _ (E.res hle) hx

theorem T_anti (k : ℕ) (U : P.Opens) : T I E (k + 1) U ≤ T I E k U :=
  Submodule.smul_mono (Ideal.pow_le_pow_right (Nat.le_succ _)) le_rfl

@[reducible] noncomputable def truncModuleSections (k : ℕ) (U : P.Opens) :
    Module Γ(P, U) (E.obj U ⧸ T I E k U) :=
  letI : SMul Γ(P, U) (E.obj U ⧸ T I E k U) :=
    ⟨fun a => Quotient.map' (a • ·) fun x y hxy => (Submodule.quotientRel_def _).mpr <| by
      rw [← smul_sub]; exact T_smul_mem I E k U a ((Submodule.quotientRel_def _).mp hxy)⟩
  Function.Surjective.module Γ(P, U) ⟨⟨Submodule.Quotient.mk, rfl⟩, fun _ _ => rfl⟩
    (Submodule.Quotient.mk_surjective _) (fun _ _ => rfl)

noncomputable def trunc (k : ℕ) : OModulePresheaf q where
  obj U := E.obj U ⧸ T I E k U
  module U := inferInstance
  moduleSections U := truncModuleSections I E k U
  isScalarTower U := by
    letI := Scheme.TwoAffineOpenCover.algebraOfHom q U
    letI := truncModuleSections I E k U
    exact ⟨fun r a => Quotient.ind' fun x => congrArg Submodule.Quotient.mk (smul_assoc r a x)⟩
  res {U U'} hle := Submodule.mapQ _ _ (E.res hle) fun x hx => T_res I E hle k hx
  res_smul {U U'} hle a z := z.inductionOn' fun x => congrArg Submodule.Quotient.mk (E.res_smul hle a x)
  res_refl U := LinearMap.ext fun z => z.inductionOn' fun x =>
    congrArg Submodule.Quotient.mk (LinearMap.congr_fun (E.res_refl U) x)
  res_comp {U U' U''} hle hle' := LinearMap.ext fun z => z.inductionOn' fun x =>
    congrArg Submodule.Quotient.mk (LinearMap.congr_fun (E.res_comp hle hle') x)

theorem trunc_obj (k : ℕ) (U : P.Opens) : (trunc I E k).obj U = (E.obj U ⧸ T I E k U) := rfl

theorem trunc_res_mk (k : ℕ) {U U' : P.Opens} (hle : U ≤ U') (x : E.obj U') :
    (trunc I E k).res hle (Submodule.Quotient.mk x) = Submodule.Quotient.mk (E.res hle x) := rfl

theorem trunc_smul_mk (k : ℕ) (U : P.Opens) (a : Γ(P, U)) (x : E.obj U) :
    (a • (show (trunc I E k).obj U from Submodule.Quotient.mk x))
      = (show (trunc I E k).obj U from Submodule.Quotient.mk (a • x)) := rfl

noncomputable def truncπ (k : ℕ) : AffHom E (trunc I E k) where
  app U := (T I E k U.1).mkQ
  app_smul _ _ _ := rfl
  naturality _ := rfl

theorem truncπ_app (k : ℕ) (U : P.affineOpens) (x : E.obj U.1) :
    (truncπ I E k).app U x = (show (trunc I E k).obj U.1 from Submodule.Quotient.mk x) := rfl

theorem truncπ_surjective (k : ℕ) (U : P.affineOpens) : Function.Surjective ((truncπ I E k).app U) :=
  Submodule.mkQ_surjective _

theorem ker_truncπ (k : ℕ) (U : P.affineOpens) :
    LinearMap.ker ((truncπ I E k).app U) = I ^ (k + 1) • (⊤ : Submodule A (E.obj U.1)) :=
  Submodule.ker_mkQ _

noncomputable def truncτ (k : ℕ) : AffHom (trunc I E (k + 1)) (trunc I E k) where
  app U := Submodule.mapQ (T I E (k + 1) U.1) (T I E k U.1) LinearMap.id (T_anti I E k U.1)
  app_smul _ _ z := z.inductionOn' fun _ => rfl
  naturality _ := LinearMap.ext fun z => z.inductionOn' fun _ => rfl

theorem truncτ_app_mk (k : ℕ) (U : P.affineOpens) (x : E.obj U.1) :
    (truncτ I E k).app U (Submodule.Quotient.mk x) = (show (trunc I E k).obj U.1 from Submodule.Quotient.mk x) :=
  rfl

theorem truncτ_surjective (k : ℕ) (U : P.affineOpens) : Function.Surjective ((truncτ I E k).app U) := by
  intro z
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ z
  exact ⟨Submodule.Quotient.mk x, rfl⟩

theorem ker_truncτ (k : ℕ) (U : P.affineOpens) :
    LinearMap.ker ((truncτ I E k).app U)
      = I ^ (k + 1) • (⊤ : Submodule A ((trunc I E (k + 1)).obj U.1)) := by

  have h1 : LinearMap.ker ((truncτ I E k).app U) = (T I E k U.1).map ((truncπ I E (k + 1)).app U) := by
    ext z
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ z
    rw [LinearMap.mem_ker]
    change (Submodule.Quotient.mk x : E.obj U.1 ⧸ T I E k U.1) = 0 ↔ _
    rw [Submodule.Quotient.mk_eq_zero]
    constructor
    · intro hx; exact ⟨x, hx, rfl⟩
    · rintro ⟨y, hy, hyx⟩
      have hd : y - x ∈ T I E (k + 1) U.1 := (Submodule.Quotient.eq _).mp hyx
      have : x = y - (y - x) := by abel
      rw [this]
      exact sub_mem hy (T_anti I E k U.1 hd)
  rw [h1, T_def, map_smul_top_of_surjective _ _ (truncπ_surjective I E (k + 1) U)]

theorem isCoherent_trunc (hEc : E.IsCoherent) (k : ℕ) : (trunc I E k).IsCoherent := by
  intro U
  haveI := hEc U
  let f : E.obj U.1 →ₗ[Γ(P, U.1)] (trunc I E k).obj U.1 :=
    { toFun := Submodule.Quotient.mk
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  exact Module.Finite.of_surjective f (Submodule.Quotient.mk_surjective _)

theorem isQuasicoherent_trunc (hEq : E.IsQuasicoherent) (k : ℕ) : (trunc I E k).IsQuasicoherent := by
  intro U f
  obtain ⟨hE1, hE2⟩ := hEq U f
  have hDf : IsAffineOpen (P.basicOpen f) := U.2.basicOpen f
  set D : P.affineOpens := ⟨P.basicOpen f, hDf⟩ with hD

  set fD : ℕ → Γ(P, P.basicOpen f) := fun n => (P.presheaf.map (homOfLE (P.basicOpen_le f)).op).hom (f ^ n)
    with hfD
  have hfD_add : ∀ a b, fD (a + b) = fD a * fD b := fun a b => by
    simp only [hfD, pow_add, map_mul]
  have hres_pow : ∀ (n : ℕ) (y : E.obj U.1),
      E.res (P.basicOpen_le f) ((f ^ n : Γ(P, U.1)) • y) = fD n • E.res (P.basicOpen_le f) y :=
    fun n y => E.res_smul _ _ _
  refine ⟨?_, ?_⟩
  · intro z
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ z
    obtain ⟨n, y, hy⟩ := hE1 x
    refine ⟨n, Submodule.Quotient.mk y, ?_⟩
    show Submodule.Quotient.mk (E.res _ y) = Submodule.Quotient.mk (_ • x)
    rw [hy]
  · intro z hz
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ z
    have hmem : E.res (P.basicOpen_le f) y ∈ T I E k (P.basicOpen f) :=
      (Submodule.Quotient.mk_eq_zero _).mp hz

    have key : ∀ x ∈ T I E k (P.basicOpen f),
        ∃ (n : ℕ) (w : E.obj U.1), w ∈ T I E k U.1 ∧ E.res (P.basicOpen_le f) w = fD n • x := by
      intro x hx
      refine Submodule.smul_induction_on hx (fun i hi x _ => ?_) (fun x x' hx hx' => ?_)
      · obtain ⟨n, w, hw⟩ := hE1 x
        refine ⟨n, i • w, Submodule.smul_mem_smul hi Submodule.mem_top, ?_⟩
        letI := Scheme.TwoAffineOpenCover.algebraOfHom q (P.basicOpen f)
        haveI : IsScalarTower A Γ(P, P.basicOpen f) (E.obj (P.basicOpen f)) := E.isScalarTower _
        rw [LinearMap.map_smul, hw]
        exact (smul_algebra_smul_comm i (fD n) x).symm
      · obtain ⟨n, w, hw, hwx⟩ := hx
        obtain ⟨n', w', hw', hwx'⟩ := hx'
        refine ⟨n + n', (f ^ n' : Γ(P, U.1)) • w + (f ^ n : Γ(P, U.1)) • w',
          add_mem (T_smul_mem I E k U.1 _ hw) (T_smul_mem I E k U.1 _ hw'), ?_⟩
        rw [map_add, hres_pow, hres_pow, hwx, hwx', smul_smul, smul_smul, ← hfD_add, ← hfD_add,
          Nat.add_comm n' n, smul_add]
    obtain ⟨n, w, hw, hwy⟩ := key _ hmem
    have h0 : E.res (P.basicOpen_le f) ((f ^ n : Γ(P, U.1)) • y - w) = 0 := by
      rw [map_sub, hres_pow, hwy, sub_self]
    obtain ⟨m, hm⟩ := hE2 _ h0
    refine ⟨m + n, ?_⟩
    show Submodule.Quotient.mk ((f ^ (m + n) : Γ(P, U.1)) • y) = 0
    rw [Submodule.Quotient.mk_eq_zero]
    rw [smul_sub, sub_eq_zero, smul_smul, ← pow_add] at hm
    rw [hm]
    exact T_smul_mem I E k U.1 _ hw

end Trunc

section Setup

variable {A : Type u} [CommRing A] (I : Ideal A) {P : Scheme.{u}} (q : P ⟶ Spec (.of A))

structure Sys where

  G : ℕ → OModulePresheaf q

  L : ℕ → OModulePresheaf q

  γ : ∀ n, AffHom (G (n + 1)) (G n)

  ι : ∀ n, AffHom (L n) (G n)

  lam : ∀ n, AffHom (L (n + 1)) (L n)
  hγs : ∀ (n : ℕ) (U : P.affineOpens), Function.Surjective ((γ n).app U)
  hγk : ∀ (n : ℕ) (U : P.affineOpens),
    LinearMap.ker ((γ n).app U) = I ^ (n + 1) • (⊤ : Submodule A ((G (n + 1)).obj U.1))
  hιi : ∀ (n : ℕ) (U : P.affineOpens), Function.Injective ((ι n).app U)
  hls : ∀ (n : ℕ) (U : P.affineOpens), Function.Surjective ((lam n).app U)
  hlc : ∀ (n : ℕ) (U : P.affineOpens), (ι n).app U ∘ₗ (lam n).app U = (γ n).app U ∘ₗ (ι (n + 1)).app U

end Setup

variable {A : Type u} [CommRing A] {I : Ideal A} {P : Scheme.{u}} {q : P ⟶ Spec (.of A)} (S : Sys I q)

namespace Sys

theorem ι_lam (n : ℕ) (U : P.affineOpens) (x : (S.L (n + 1)).obj U.1) :
    (S.ι n).app U ((S.lam n).app U x) = (S.γ n).app U ((S.ι (n + 1)).app U x) :=
  LinearMap.congr_fun (S.hlc n U) x

theorem lam_surjective (n : ℕ) (U : P.affineOpens) : Function.Surjective ((S.lam n).app U) := S.hls n U

theorem pow_smul_top_G (n : ℕ) (U : P.affineOpens) :
    I ^ (n + 1) • (⊤ : Submodule A ((S.G n).obj U.1)) = ⊥ :=
  pow_smul_top_eq_bot _ ((S.γ n).app U) (S.hγs n U) (S.hγk n U)

def AR (U : P.affineOpens) (c : ℕ) : Prop :=
  ∀ k n : ℕ, k + c ≤ n →
    (I ^ n • (⊤ : Submodule A ((S.G n).obj U.1))) ⊓ LinearMap.range ((S.ι n).app U)
      ≤ I ^ k • LinearMap.range ((S.ι n).app U)

variable {S}

theorem ker_lam_le {U : P.affineOpens} {c : ℕ} (hc : S.AR U c) {k n : ℕ} (hkn : k + c ≤ n) :
    LinearMap.ker ((S.lam n).app U) ≤ I ^ (k + 1) • (⊤ : Submodule A ((S.L (n + 1)).obj U.1)) := by
  intro x hx
  rw [LinearMap.mem_ker] at hx
  have h1 : (S.ι (n + 1)).app U x ∈
      (I ^ (n + 1) • (⊤ : Submodule A ((S.G (n + 1)).obj U.1))) ⊓ LinearMap.range ((S.ι (n + 1)).app U) := by
    refine Submodule.mem_inf.mpr ⟨?_, LinearMap.mem_range_self _ x⟩
    rw [← S.hγk n U, LinearMap.mem_ker, ← ι_lam, hx, map_zero]
  have h2 := hc (k + 1) (n + 1) (by omega) h1
  rw [LinearMap.range_eq_map, ← Submodule.map_smul''] at h2
  obtain ⟨w, hw, hwx⟩ := h2
  rw [← S.hιi (n + 1) U hwx]
  exact hw

variable (S)

noncomputable abbrev Q (n k : ℕ) : OModulePresheaf q := trunc I (S.L n) k

noncomputable def t (n k : ℕ) : AffHom (S.Q (n + 1) k) (S.Q n k) where
  app U := Submodule.mapQ (T I (S.L (n + 1)) k U.1) (T I (S.L n) k U.1) ((S.lam n).app U)
    (fun _ hx => map_mem_smul_top _ _ hx)
  app_smul U a z := z.inductionOn' fun x => congrArg Submodule.Quotient.mk ((S.lam n).app_smul U a x)
  naturality h := LinearMap.ext fun z => z.inductionOn' fun x =>
    congrArg Submodule.Quotient.mk ((S.lam n).naturality_apply h x)

theorem t_mk (n k : ℕ) (U : P.affineOpens) (x : (S.L (n + 1)).obj U.1) :
    (S.t n k).app U (Submodule.Quotient.mk x)
      = (show (S.Q n k).obj U.1 from Submodule.Quotient.mk ((S.lam n).app U x)) := rfl

noncomputable abbrev r (n k : ℕ) : AffHom (S.Q n (k + 1)) (S.Q n k) := truncτ I (S.L n) k

theorem t_r_comm (n k : ℕ) (U : P.affineOpens) (z : (S.Q (n + 1) (k + 1)).obj U.1) :
    (S.t n k).app U ((S.r (n + 1) k).app U z) = (S.r n k).app U ((S.t n (k + 1)).app U z) :=
  z.inductionOn' fun _ => rfl

theorem t_surjective (n k : ℕ) (U : P.affineOpens) : Function.Surjective ((S.t n k).app U) := by
  intro z
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ z
  obtain ⟨x, rfl⟩ := S.lam_surjective n U y
  exact ⟨Submodule.Quotient.mk x, rfl⟩

variable {S}

theorem t_injective {U : P.affineOpens} {c : ℕ} (hc : S.AR U c) {k n : ℕ} (hkn : k + c ≤ n) :
    Function.Injective ((S.t n k).app U) := by
  rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
  intro z hz
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ z
  rw [LinearMap.mem_ker, t_mk] at hz
  have hz' : (S.lam n).app U x ∈ T I (S.L n) k U.1 := (Submodule.Quotient.mk_eq_zero _).mp hz
  rw [T_def, ← map_smul_top_of_surjective _ ((S.lam n).app U) (S.lam_surjective n U)] at hz'
  obtain ⟨w, hw, hwx⟩ := hz'
  have hxw : x - w ∈ LinearMap.ker ((S.lam n).app U) := by
    rw [LinearMap.mem_ker, map_sub, hwx, sub_self]
  have := ker_lam_le hc hkn hxw
  change (Submodule.Quotient.mk x : (S.L (n + 1)).obj U.1 ⧸ T I (S.L (n + 1)) k U.1) = 0
  rw [Submodule.Quotient.mk_eq_zero, show x = (x - w) + w by abel]
  exact add_mem this hw

variable (S)

def Kmod (k : ℕ) (U : P.Opens) : Submodule A (∀ n, (S.Q n k).obj U) where
  carrier := {x | ∀ (n : ℕ) (W : P.affineOpens) (hW : W.1 ≤ U),
    (S.t n k).app W ((S.Q (n + 1) k).res hW (x (n + 1))) = (S.Q n k).res hW (x n)}
  add_mem' {x y} hx hy n W hW := by
    rw [Set.mem_setOf_eq] at hx hy
    rw [Pi.add_apply, Pi.add_apply, map_add, map_add, map_add, hx n W hW, hy n W hW]
  zero_mem' n W hW := by rw [Pi.zero_apply, Pi.zero_apply, map_zero, map_zero, map_zero]
  smul_mem' a x hx n W hW := by
    rw [Set.mem_setOf_eq] at hx
    rw [Pi.smul_apply, Pi.smul_apply, map_smul, map_smul, map_smul, hx n W hW]

theorem mem_Kmod {k : ℕ} {U : P.Opens} {x : ∀ n, (S.Q n k).obj U} :
    x ∈ S.Kmod k U ↔ ∀ (n : ℕ) (W : P.affineOpens) (hW : W.1 ≤ U),
      (S.t n k).app W ((S.Q (n + 1) k).res hW (x (n + 1))) = (S.Q n k).res hW (x n) :=
  Iff.rfl

theorem Kmod_smul_mem (k : ℕ) (U : P.Opens) (a : Γ(P, U)) {x : ∀ n, (S.Q n k).obj U}
    (hx : x ∈ S.Kmod k U) : a • x ∈ S.Kmod k U := by
  intro n W hW
  rw [Pi.smul_apply, Pi.smul_apply, (S.Q (n + 1) k).res_smul, (S.Q n k).res_smul, (S.t n k).app_smul,
    hx n W hW]

theorem Kmod_res {k : ℕ} {U U' : P.Opens} (hle : U ≤ U') {x : ∀ n, (S.Q n k).obj U'} (hx : x ∈ S.Kmod k U') :
    (fun n => (S.Q n k).res hle (x n)) ∈ S.Kmod k U := by
  intro n W hW
  simp only [OModulePresheaf.res_res]
  exact hx n W (hW.trans hle)

theorem compat_of_mem {k : ℕ} {U : P.affineOpens} {x : ∀ n, (S.Q n k).obj U.1} (hx : x ∈ S.Kmod k U.1)
    (n : ℕ) : (S.t n k).app U (x (n + 1)) = x n := by
  have := hx n U le_rfl
  rwa [OModulePresheaf.res_refl_apply, OModulePresheaf.res_refl_apply] at this

theorem mem_Kmod_of_compat {k : ℕ} (U : P.affineOpens) {x : ∀ n, (S.Q n k).obj U.1}
    (h : ∀ n, (S.t n k).app U (x (n + 1)) = x n) : x ∈ S.Kmod k U.1 := by
  intro n W hW
  rw [(S.t n k).naturality_apply hW, h n]

noncomputable def piRes (k : ℕ) {U U' : P.Opens} (hle : U ≤ U') :
    (∀ n, (S.Q n k).obj U') →ₗ[A] (∀ n, (S.Q n k).obj U) :=
  LinearMap.pi fun n => (S.Q n k).res hle ∘ₗ LinearMap.proj n

theorem piRes_apply (k : ℕ) {U U' : P.Opens} (hle : U ≤ U') (x : ∀ n, (S.Q n k).obj U') (n : ℕ) :
    S.piRes k hle x n = (S.Q n k).res hle (x n) := rfl

@[reducible] noncomputable def kModuleSections (k : ℕ) (U : P.Opens) : Module Γ(P, U) ↥(S.Kmod k U) :=
  letI : SMul Γ(P, U) ↥(S.Kmod k U) := ⟨fun a x => ⟨a • x.1, S.Kmod_smul_mem k U a x.2⟩⟩
  Function.Injective.module Γ(P, U) ⟨⟨Subtype.val, rfl⟩, fun _ _ => rfl⟩ Subtype.val_injective (fun _ _ => rfl)

noncomputable def K (k : ℕ) : OModulePresheaf q where
  obj U := ↥(S.Kmod k U)
  module U := inferInstance
  moduleSections U := S.kModuleSections k U
  isScalarTower U := by
    letI := Scheme.TwoAffineOpenCover.algebraOfHom q U
    letI := S.kModuleSections k U
    haveI : ∀ n, IsScalarTower A Γ(P, U) ((S.Q n k).obj U) := fun n => (S.Q n k).isScalarTower U
    exact ⟨fun r a x => Subtype.ext (smul_assoc r a x.1)⟩
  res {U U'} hle := (S.piRes k hle).restrict fun x hx => S.Kmod_res hle hx
  res_smul {U U'} hle a x := Subtype.ext (funext fun n => (S.Q n k).res_smul hle a (x.1 n))
  res_refl U := LinearMap.ext fun x => Subtype.ext (funext fun n =>
    LinearMap.congr_fun ((S.Q n k).res_refl U) (x.1 n))
  res_comp {U U' U''} hle hle' := LinearMap.ext fun x => Subtype.ext (funext fun n =>
    LinearMap.congr_fun ((S.Q n k).res_comp hle hle') (x.1 n))

theorem K_obj (k : ℕ) (U : P.Opens) : (S.K k).obj U = ↥(S.Kmod k U) := rfl

theorem K_res_val (k : ℕ) {U U' : P.Opens} (hle : U ≤ U') (x : (S.K k).obj U') (n : ℕ) :
    ((S.K k).res hle x).1 n = (S.Q n k).res hle (x.1 n) := rfl

theorem K_smul_val (k : ℕ) (U : P.Opens) (a : Γ(P, U)) (x : (S.K k).obj U) : (a • x).1 = a • x.1 := rfl

noncomputable def ev (n k : ℕ) (U : P.Opens) : (S.K k).obj U →ₗ[A] (S.Q n k).obj U :=
  LinearMap.proj n ∘ₗ (S.Kmod k U).subtype

theorem ev_apply (n k : ℕ) (U : P.Opens) (x : (S.K k).obj U) : S.ev n k U x = x.1 n := rfl

noncomputable def seq0 (k : ℕ) (U : P.affineOpens) (y : (S.Q 0 k).obj U.1) : ∀ m, (S.Q m k).obj U.1 :=
  fun m => @Nat.rec (fun m => (S.Q m k).obj U.1) y
    (fun m prev => Classical.choose (S.t_surjective m k U prev)) m

noncomputable def seqMod (k : ℕ) (U : P.affineOpens) (n : ℕ) (x : ∀ m, (S.Q m k).obj U.1)
    (y : (S.Q (n + 1) k).obj U.1) : ∀ m, (S.Q m k).obj U.1 :=
  fun m => @Nat.rec (fun m => (S.Q m k).obj U.1) (x 0)
    (fun m prev => if m + 1 ≤ n then x (m + 1) else
      if h : m = n then (by subst h; exact y) else Classical.choose (S.t_surjective m k U prev)) m

theorem seqMod_zero (k : ℕ) (U : P.affineOpens) (n : ℕ) (x : ∀ m, (S.Q m k).obj U.1)
    (y : (S.Q (n + 1) k).obj U.1) : S.seqMod k U n x y 0 = x 0 := rfl

theorem seqMod_succ (k : ℕ) (U : P.affineOpens) (n : ℕ) (x : ∀ m, (S.Q m k).obj U.1)
    (y : (S.Q (n + 1) k).obj U.1) (m : ℕ) :
    S.seqMod k U n x y (m + 1) = (if m + 1 ≤ n then x (m + 1) else
      if h : m = n then (by subst h; exact y) else
        Classical.choose (S.t_surjective m k U (S.seqMod k U n x y m))) := rfl

theorem seqMod_of_le (k : ℕ) (U : P.affineOpens) (n : ℕ) (x : ∀ m, (S.Q m k).obj U.1)
    (y : (S.Q (n + 1) k).obj U.1) : ∀ m, m ≤ n → S.seqMod k U n x y m = x m
  | 0, _ => rfl
  | m + 1, hm => by rw [seqMod_succ, if_pos hm]

theorem seqMod_at (k : ℕ) (U : P.affineOpens) (n : ℕ) (x : ∀ m, (S.Q m k).obj U.1)
    (y : (S.Q (n + 1) k).obj U.1) : S.seqMod k U n x y (n + 1) = y := by
  rw [seqMod_succ, if_neg (Nat.not_succ_le_self n), dif_pos rfl]

theorem ev_surjective (k : ℕ) (U : P.affineOpens) :
    ∀ (n : ℕ) (y : (S.Q n k).obj U.1), ∃ x ∈ S.Kmod k U.1, x n = y := by
  intro n
  induction n with
  | zero =>
    intro y
    refine ⟨S.seq0 k U y, S.mem_Kmod_of_compat U (fun m => ?_), rfl⟩
    exact Classical.choose_spec (S.t_surjective m k U (S.seq0 k U y m))
  | succ n ih =>
    intro y
    obtain ⟨x, hx, hxn⟩ := ih ((S.t n k).app U y)
    refine ⟨S.seqMod k U n x y, S.mem_Kmod_of_compat U (fun m => ?_), S.seqMod_at k U n x y⟩
    rw [seqMod_succ]
    split_ifs with h1 h2
    · rw [S.seqMod_of_le k U n x y m (Nat.le_of_succ_le h1)]
      exact S.compat_of_mem hx m
    · subst h2
      rw [S.seqMod_of_le k U m x y m le_rfl, ← hxn]
    · exact Classical.choose_spec (S.t_surjective m k U (S.seqMod k U n x y m))

theorem ev_surjective' (n k : ℕ) (U : P.affineOpens) : Function.Surjective (S.ev n k U.1) := by
  intro y
  obtain ⟨x, hx, hxn⟩ := S.ev_surjective k U n y
  exact ⟨⟨x, hx⟩, hxn⟩

variable {S}

theorem ev_injective {U : P.affineOpens} {c : ℕ} (hc : S.AR U c) {k n : ℕ} (hkn : k + c ≤ n) :
    Function.Injective (S.ev n k U.1) := by
  rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
  intro x hx
  rw [LinearMap.mem_ker, ev_apply] at hx
  have hcompat := S.compat_of_mem x.2

  have hdown : ∀ m, x.1 m = 0 → ∀ i, i ≤ m → x.1 i = 0 := by
    intro m
    induction m with
    | zero => intro h i hi; rw [Nat.le_zero.mp hi]; exact h
    | succ m ih =>
      intro h i hi
      rcases Nat.lt_or_eq_of_le hi with hi | rfl
      · have hm : x.1 m = 0 := by rw [← hcompat m, h, map_zero]
        exact ih hm i (Nat.lt_succ_iff.mp hi)
      · exact h

  have hup : ∀ m, n ≤ m → x.1 m = 0 := by
    intro m hm
    induction m, hm using Nat.le_induction with
    | base => exact hx
    | succ m hm ih =>
      apply t_injective hc (show k + c ≤ m by omega)
      rw [hcompat m, ih, map_zero]
  refine Subtype.ext (funext fun i => ?_)
  rcases le_total i n with hi | hi
  · exact hdown n hx i hi
  · exact hup i hi

variable (S)

noncomputable def piRed (k : ℕ) (U : P.affineOpens) :
    (∀ n, (S.Q n (k + 1)).obj U.1) →ₗ[A] (∀ n, (S.Q n k).obj U.1) :=
  LinearMap.pi fun n => (S.r n k).app U ∘ₗ LinearMap.proj n

theorem piRed_mem (k : ℕ) (U : P.affineOpens) (x : (S.K (k + 1)).obj U.1) :
    S.piRed k U x.1 ∈ S.Kmod k U.1 := by
  intro n W hW
  show (S.t n k).app W ((S.Q (n + 1) k).res hW ((S.r (n + 1) k).app U (x.1 (n + 1))))
    = (S.Q n k).res hW ((S.r n k).app U (x.1 n))
  rw [← (S.r (n + 1) k).naturality_apply hW, t_r_comm, x.2 n W hW, (S.r n k).naturality_apply hW]

noncomputable def κ (k : ℕ) : AffHom (S.K (k + 1)) (S.K k) where
  app U := LinearMap.codRestrict (S.Kmod k U.1) (S.piRed k U ∘ₗ (S.Kmod (k + 1) U.1).subtype)
    (S.piRed_mem k U)
  app_smul U a x := Subtype.ext (funext fun n => (S.r n k).app_smul U a (x.1 n))
  naturality h := LinearMap.ext fun x => Subtype.ext (funext fun n => (S.r n k).naturality_apply h (x.1 n))

theorem κ_val (k : ℕ) (U : P.affineOpens) (x : (S.K (k + 1)).obj U.1) (n : ℕ) :
    ((S.κ k).app U x).1 n = (S.r n k).app U (x.1 n) := rfl

theorem T_le_ker_ι (k : ℕ) (U : P.affineOpens) :
    T I (S.L k) k U.1 ≤ LinearMap.ker ((S.ι k).app U) := by
  intro x hx
  rw [LinearMap.mem_ker, ← Submodule.mem_bot A, ← S.pow_smul_top_G k U]
  exact map_mem_smul_top _ _ hx

noncomputable def e (k : ℕ) (U : P.affineOpens) : (S.Q k k).obj U.1 →ₗ[A] (S.G k).obj U.1 :=
  (T I (S.L k) k U.1).liftQ ((S.ι k).app U) (S.T_le_ker_ι k U)

theorem e_mk (k : ℕ) (U : P.affineOpens) (z : (S.L k).obj U.1) :
    S.e k U (Submodule.Quotient.mk z) = (S.ι k).app U z := rfl

noncomputable def j (k : ℕ) : AffHom (S.K k) (S.G k) where
  app U := S.e k U ∘ₗ S.ev k k U.1
  app_smul U a x := by
    show S.e k U ((a • x).1 k) = a • S.e k U (x.1 k)
    rw [K_smul_val, Pi.smul_apply]
    obtain ⟨z, hz⟩ := Submodule.Quotient.mk_surjective _ (x.1 k)
    rw [← hz]
    exact (S.ι k).app_smul U a z
  naturality {U U'} h := LinearMap.ext fun x => by
    show S.e k U (((S.K k).res h x).1 k) = (S.G k).res h (S.e k U' (x.1 k))
    rw [K_res_val]
    obtain ⟨z, hz⟩ := Submodule.Quotient.mk_surjective _ (x.1 k)
    rw [← hz]
    exact (S.ι k).naturality_apply h z

theorem j_app (k : ℕ) (U : P.affineOpens) (x : (S.K k).obj U.1) :
    (S.j k).app U x = S.e k U (x.1 k) := rfl

theorem range_j (k : ℕ) (U : P.affineOpens) :
    LinearMap.range ((S.j k).app U) = LinearMap.range ((S.ι k).app U) := by
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩
    rw [j_app]
    obtain ⟨z, hz⟩ := Submodule.Quotient.mk_surjective _ (x.1 k)
    rw [← hz, e_mk]
    exact LinearMap.mem_range_self _ z
  · rintro _ ⟨z, rfl⟩
    obtain ⟨x, hx⟩ := S.ev_surjective' k k U (Submodule.Quotient.mk z)
    refine ⟨x, ?_⟩
    rw [j_app, ← ev_apply, hx, e_mk]

theorem j_comp_κ (k : ℕ) (U : P.affineOpens) :
    (S.γ k).app U ∘ₗ (S.j (k + 1)).app U = (S.j k).app U ∘ₗ (S.κ k).app U := by
  refine LinearMap.ext fun x => ?_
  show (S.γ k).app U (S.e (k + 1) U (x.1 (k + 1))) = S.e k U ((S.r k k).app U (x.1 k))
  rw [← S.compat_of_mem x.2 k]
  obtain ⟨z, hz⟩ := Submodule.Quotient.mk_surjective _ (x.1 (k + 1))
  rw [← hz]
  exact (S.ι_lam k U z).symm

variable {S}

theorem κ_surjective {U : P.affineOpens} {c : ℕ} (hc : S.AR U c) (k : ℕ) :
    Function.Surjective ((S.κ k).app U) := by
  intro y
  obtain ⟨w, hw⟩ := truncτ_surjective I (S.L (k + 1 + c)) k U (S.ev (k + 1 + c) k U.1 y)
  obtain ⟨x, hx⟩ := S.ev_surjective' (k + 1 + c) (k + 1) U w
  refine ⟨x, ev_injective hc (show k + c ≤ k + 1 + c by omega) ?_⟩
  rw [ev_apply, κ_val, ← ev_apply, hx, hw, ev_apply]

theorem ker_κ {U : P.affineOpens} {c : ℕ} (hc : S.AR U c) (k : ℕ) :
    LinearMap.ker ((S.κ k).app U) = I ^ (k + 1) • (⊤ : Submodule A ((S.K (k + 1)).obj U.1)) := by
  have h1 : Function.Injective (S.ev (k + 1 + c) (k + 1) U.1) := ev_injective hc le_rfl
  have h1s := S.ev_surjective' (k + 1 + c) (k + 1) U
  have h0 : Function.Injective (S.ev (k + 1 + c) k U.1) :=
    ev_injective hc (show k + c ≤ k + 1 + c by omega)
  have hcomm : S.ev (k + 1 + c) k U.1 ∘ₗ (S.κ k).app U
      = (S.r (k + 1 + c) k).app U ∘ₗ S.ev (k + 1 + c) (k + 1) U.1 :=
    LinearMap.ext fun _ => rfl
  calc LinearMap.ker ((S.κ k).app U)
      = LinearMap.ker (S.ev (k + 1 + c) k U.1 ∘ₗ (S.κ k).app U) := by
        rw [LinearMap.ker_comp, LinearMap.ker_eq_bot.mpr h0, Submodule.comap_bot]
    _ = LinearMap.ker ((S.r (k + 1 + c) k).app U ∘ₗ S.ev (k + 1 + c) (k + 1) U.1) := by rw [hcomm]
    _ = (I ^ (k + 1) • (⊤ : Submodule A ((S.Q (k + 1 + c) (k + 1)).obj U.1))).comap
          (S.ev (k + 1 + c) (k + 1) U.1) := by
        rw [LinearMap.ker_comp, ker_truncτ]
    _ = ((I ^ (k + 1) • (⊤ : Submodule A ((S.K (k + 1)).obj U.1))).map
          (S.ev (k + 1 + c) (k + 1) U.1)).comap (S.ev (k + 1 + c) (k + 1) U.1) := by
        rw [map_smul_top_of_surjective _ _ h1s]
    _ = I ^ (k + 1) • ⊤ := Submodule.comap_map_eq_of_injective h1 _

theorem isCoherent_K (hLc : ∀ n, (S.L n).IsCoherent) (hAR : ∀ U : P.affineOpens, ∃ c, S.AR U c) (k : ℕ) :
    (S.K k).IsCoherent := by
  intro U
  obtain ⟨c, hc⟩ := hAR U
  haveI := isCoherent_trunc I (S.L (k + c)) (hLc (k + c)) k U
  let ω : (S.K k).obj U.1 →ₗ[Γ(P, U.1)] (S.Q (k + c) k).obj U.1 :=
    { toFun := fun x => x.1 (k + c)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hb : Function.Bijective ω := ⟨ev_injective hc le_rfl, S.ev_surjective' (k + c) k U⟩
  exact Module.Finite.equiv (LinearEquiv.ofBijective ω hb).symm

theorem isQuasicoherent_K (hLq : ∀ n, (S.L n).IsQuasicoherent) (hAR : ∀ U : P.affineOpens, ∃ c, S.AR U c)
    (k : ℕ) : (S.K k).IsQuasicoherent := by
  intro U f
  have hDf : IsAffineOpen (P.basicOpen f) := U.2.basicOpen f
  set D : P.affineOpens := ⟨P.basicOpen f, hDf⟩ with hD
  obtain ⟨cU, hcU⟩ := hAR U
  obtain ⟨cD, hcD⟩ := hAR D
  have hU : Function.Injective (S.ev (k + (cU + cD)) k U.1) := ev_injective hcU (by omega)
  have hDi : Function.Injective (S.ev (k + (cU + cD)) k D.1) := ev_injective hcD (by omega)
  obtain ⟨hQ1, hQ2⟩ := isQuasicoherent_trunc I (S.L (k + (cU + cD))) (hLq _) k U f
  refine ⟨fun x => ?_, fun y hy => ?_⟩
  · obtain ⟨m, w, hw⟩ := hQ1 (S.ev (k + (cU + cD)) k D.1 x)
    obtain ⟨y, hy⟩ := S.ev_surjective' (k + (cU + cD)) k U w
    refine ⟨m, y, hDi ?_⟩
    rw [ev_apply, ev_apply, K_res_val, ← ev_apply, hy, hw]
    rfl
  · have h0 : (S.Q (k + (cU + cD)) k).res (P.basicOpen_le f) (y.1 (k + (cU + cD))) = 0 :=
      congrArg (fun z : (S.K k).obj (P.basicOpen f) => z.1 (k + (cU + cD))) hy
    obtain ⟨m, hm⟩ := hQ2 _ h0
    exact ⟨m, hU hm⟩

theorem ker_t_le {U : P.affineOpens} {c : ℕ} (hc : S.AR U c) {k m : ℕ} (hkm : k + c ≤ m) (k' : ℕ) :
    LinearMap.ker ((S.t m k').app U) ≤ I ^ (k + 1) • (⊤ : Submodule A ((S.Q (m + 1) k').obj U.1)) := by
  intro z hz
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ z
  rw [LinearMap.mem_ker, t_mk] at hz
  have hz' : (S.lam m).app U x ∈ T I (S.L m) k' U.1 := (Submodule.Quotient.mk_eq_zero _).mp hz
  rw [T_def, ← map_smul_top_of_surjective _ ((S.lam m).app U) (S.lam_surjective m U)] at hz'
  obtain ⟨w, hw, hwx⟩ := hz'
  have hxw : x - w ∈ LinearMap.ker ((S.lam m).app U) := by
    rw [LinearMap.mem_ker, map_sub, hwx, sub_self]
  have h1 := ker_lam_le hc hkm hxw
  have h2 : (Submodule.Quotient.mk w : (S.L (m + 1)).obj U.1 ⧸ T I (S.L (m + 1)) k' U.1) = 0 :=
    (Submodule.Quotient.mk_eq_zero _).mpr hw
  have h3 : (Submodule.Quotient.mk x : (S.L (m + 1)).obj U.1 ⧸ T I (S.L (m + 1)) k' U.1)
      = (T I (S.L (m + 1)) k' U.1).mkQ (x - w) := by
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_sub, h2, sub_zero]
  rw [h3]
  exact map_mem_smul_top _ _ h1

theorem apply_mem_pow_smul_top_of_apply_eq_zero {U : P.affineOpens} {c : ℕ} (hc : S.AR U c) {k k' n : ℕ}
    (hkn : k + c ≤ n) (x : (S.K k').obj U.1) (hx : x.1 n = 0) :
    ∀ m, n ≤ m → x.1 m ∈ I ^ (k + 1) • (⊤ : Submodule A ((S.Q m k').obj U.1)) := by
  intro m hm
  induction m, hm using Nat.le_induction with
  | base => rw [hx]; exact Submodule.zero_mem _
  | succ m hm ih =>
    have hcompat := S.compat_of_mem x.2 m

    rw [← map_smul_top_of_surjective _ ((S.t m k').app U) (S.t_surjective m k' U)] at ih
    obtain ⟨w, hw, hwx⟩ := ih
    have hker : x.1 (m + 1) - w ∈ LinearMap.ker ((S.t m k').app U) := by
      rw [LinearMap.mem_ker, map_sub, hcompat, hwx, sub_self]
    have := ker_t_le hc (show k + c ≤ m by omega) k' hker
    rw [show x.1 (m + 1) = (x.1 (m + 1) - w) + w by abel]
    exact add_mem this hw

theorem ker_j_le {U : P.affineOpens} {c : ℕ} (hc : S.AR U c) {k n : ℕ} (hkn : k + c ≤ n) :
    LinearMap.ker ((S.j n).app U) ≤ I ^ (k + 1) • (⊤ : Submodule A ((S.K n).obj U.1)) := by
  intro x hx
  rw [LinearMap.mem_ker, j_app] at hx

  have hxn : x.1 n = 0 := by
    obtain ⟨z, hz⟩ := Submodule.Quotient.mk_surjective _ (x.1 n)
    rw [← hz, e_mk] at hx
    have hz0 : z = 0 := S.hιi n U (by rw [hx, map_zero])
    rw [← hz, hz0, Submodule.Quotient.mk_zero]
    rfl
  have hm := apply_mem_pow_smul_top_of_apply_eq_zero hc hkn x hxn (n + c) (Nat.le_add_right n c)
  have hinj : Function.Injective (S.ev (n + c) n U.1) := ev_injective hc le_rfl
  have hsurj := S.ev_surjective' (n + c) n U
  have : x ∈ ((I ^ (k + 1) • (⊤ : Submodule A ((S.K n).obj U.1))).map (S.ev (n + c) n U.1)).comap
      (S.ev (n + c) n U.1) := by
    rw [map_smul_top_of_surjective _ _ hsurj]
    exact hm
  rwa [Submodule.comap_map_eq_of_injective hinj] at this

end Sys

end AdicEnvelopeSol

open AdicEnvelopeSol in
theorem solution
    {A : Type u} [CommRing A] (I : Ideal A)
    {P : Scheme.{u}} {q : P ⟶ Spec (CommRingCat.of A)}
    (F : ℕ → OModulePresheaf q)
    (φ : ∀ n, OModulePresheaf.AffHom (F (n + 1)) (F n))
    (hφs : ∀ (n : ℕ) (U : P.affineOpens), Function.Surjective ((φ n).app U))
    (hφk : ∀ (n : ℕ) (U : P.affineOpens),
      LinearMap.ker ((φ n).app U) = I ^ (n + 1) • (⊤ : Submodule A ((F (n + 1)).obj U.1)))
    (L : ℕ → OModulePresheaf q) (hLc : ∀ n, (L n).IsCoherent) (hLq : ∀ n, (L n).IsQuasicoherent)
    (ι : ∀ n, OModulePresheaf.AffHom (L n) (F n))
    (hιi : ∀ (n : ℕ) (U : P.affineOpens), Function.Injective ((ι n).app U))
    (lam : ∀ n, OModulePresheaf.AffHom (L (n + 1)) (L n))
    (hls : ∀ (n : ℕ) (U : P.affineOpens), Function.Surjective ((lam n).app U))
    (hlc : ∀ (n : ℕ) (U : P.affineOpens), (ι n).app U ∘ₗ (lam n).app U = (φ n).app U ∘ₗ (ι (n + 1)).app U)
    (hAR : ∀ U : P.affineOpens, ∃ c : ℕ, ∀ k n : ℕ, k + c ≤ n →
      I ^ n • (⊤ : Submodule A ((F n).obj U.1)) ⊓ LinearMap.range ((ι n).app U) ≤ I ^ k • LinearMap.range ((ι n).app U)) :
    ∃ (Ks : ℕ → OModulePresheaf q) (κ : ∀ k, OModulePresheaf.AffHom (Ks (k + 1)) (Ks k))
      (j : ∀ k, OModulePresheaf.AffHom (Ks k) (F k)),
      (∀ k, (Ks k).IsCoherent) ∧ (∀ k, (Ks k).IsQuasicoherent) ∧
      (∀ (k : ℕ) (U : P.affineOpens), Function.Surjective ((κ k).app U)) ∧
      (∀ (k : ℕ) (U : P.affineOpens),
        LinearMap.ker ((κ k).app U) = I ^ (k + 1) • (⊤ : Submodule A ((Ks (k + 1)).obj U.1))) ∧
      (∀ (k : ℕ) (U : P.affineOpens), (φ k).app U ∘ₗ (j (k + 1)).app U = (j k).app U ∘ₗ (κ k).app U) ∧
      (∀ (k : ℕ) (U : P.affineOpens), LinearMap.range ((j k).app U) = LinearMap.range ((ι k).app U)) ∧
      (∀ U : P.affineOpens, ∃ c : ℕ, ∀ k n : ℕ, k + c ≤ n →
        LinearMap.ker ((j n).app U) ≤ I ^ (k + 1) • (⊤ : Submodule A ((Ks n).obj U.1))) := by
  let S : Sys I q :=
    { G := F, L := L, γ := φ, ι := ι, lam := lam, hγs := hφs, hγk := hφk, hιi := hιi, hls := hls, hlc := hlc }
  have hAR' : ∀ U : P.affineOpens, ∃ c, S.AR U c := hAR
  refine ⟨S.K, S.κ, S.j, Sys.isCoherent_K (S := S) hLc hAR', Sys.isQuasicoherent_K (S := S) hLq hAR',
    fun k U => ?_, fun k U => ?_, fun k U => S.j_comp_κ k U, fun k U => S.range_j k U, fun U => ?_⟩
  · obtain ⟨c, hc⟩ := hAR' U
    exact Sys.κ_surjective hc k
  · obtain ⟨c, hc⟩ := hAR' U
    exact Sys.ker_κ hc k
  · obtain ⟨c, hc⟩ := hAR' U
    exact ⟨c, fun k n hkn => Sys.ker_j_le hc hkn⟩

end S_AlgebraicGeometry_OModulePresheaf_exists_adicSystem_range_eq_range_of_forall_pow_smul_top_inf_range_le
end P2MW
export P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_adicSystem_range_eq_range_of_forall_pow_smul_top_inf_range_le (solution)
