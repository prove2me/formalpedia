-- Prove2me | Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_AffineVanishing
-- name    : GroundTheory_ArithmeticGeometry_SchemeCohomology_AffineVanishing
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:32:18.255865+00:00
-- url     : https://prove2.me/theorems/92e41552-beff-4819-b699-f06a7b211c01
-- title:
--   Affine Vanishing
-- statement:
--   Definitions and structural lemmas for Affine Vanishing, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/AffineVanishing.lean

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_LocalizingCech
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_CechToDerived
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Arith.SchemeCoh
open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry PrimeSpectrum
universe w u
variable {R : CommRingCat.{u}} (M : ModuleCat.{u} R)
noncomputable abbrev tildeAb :
    Sheaf (Opens.grothendieckTopology (Spec R).toTopCat) AddCommGrpCat.{u} :=
  (SheafOfModules.toSheaf (Spec R).ringCatSheaf).obj (tilde M)
noncomputable instance (W : Opens (Spec R).toTopCat) : Module R ((tildeAb M).obj.obj (op W)) :=
  inferInstanceAs (Module R Γ(tilde M, W))
lemma res_toOpen {V W : Opens (Spec R).toTopCat} (h : V ≤ W) (m : M) :
    res (X := (Spec R).toTopCat) (tildeAb M).obj h ((tilde.toOpen M W).hom m) =
      (tilde.toOpen M V).hom m :=
  congrArg (fun f => f.hom m) (tilde.toOpen_res M W V (homOfLE h))
lemma res_smul {V W : Opens (Spec R).toTopCat} (h : V ≤ W) (r : R)
    (x : (tildeAb M).obj.obj (op W)) :
    res (X := (Spec R).toTopCat) (tildeAb M).obj h (r • x) =
      r • res (X := (Spec R).toTopCat) (tildeAb M).obj h x :=
  Scheme.Modules.map_smul_Spec (M := tilde M) (homOfLE h).op r x
lemma bijective_smul_tilde (g : R) (W : Opens (Spec R).toTopCat) (hW : W ≤ basicOpen g) (k : ℕ) :
    Function.Bijective (fun x : (tildeAb M).obj.obj (op W) => g ^ k • x) := by
  have := (Module.End.isUnit_iff _).1
    ((Scheme.Modules.isUnit_algebraMap_end_of_le_basicOpen (M := tilde M) g hW).pow k)
  rw [← map_pow] at this
  exact this
lemma exists_cover_eq (g : R) {ι : Type*} [Fintype ι] (h : ι → R) (N : ℕ)
    (hle : basicOpen g ≤ ⨆ i, basicOpen (h i)) :
    ∃ (L : ℕ) (c : ι → R), g ^ L = ∑ i, c i * h i ^ N := by
  have hrad : g ∈ (Ideal.span (Set.range fun i => h i ^ N)).radical := by
    rw [Ideal.radical_eq_sInf, Ideal.mem_sInf]
    rintro p ⟨hIp, hp⟩
    by_contra hg
    have hx : (⟨p, hp⟩ : PrimeSpectrum R) ∈ basicOpen g := (mem_basicOpen _ _).2 hg
    obtain ⟨i, hi⟩ := Opens.mem_iSup.1 (hle hx)
    apply (mem_basicOpen _ _).1 hi
    exact hp.mem_of_pow_mem N (hIp (Ideal.subset_span ⟨i, rfl⟩))
  obtain ⟨L, hL⟩ := hrad
  obtain ⟨c, hc⟩ := Ideal.mem_span_range_iff_exists_fun.1 hL
  exact ⟨L, c, hc.symm⟩
noncomputable def tildeAction :
    LocalizingAction (X := (Spec R).toTopCat) (tildeAb M).obj (fun r : R => basicOpen r) where
  act r W := DistribSMul.toAddMonoidHom ((tildeAb M).obj.obj (op W)) r
  res_act r V W h x := res_smul M h r x
  act_mul a b W x := mul_smul a b x
  act_add a b W x := add_smul a b x
  act_one W x := one_smul R x
  bijective g W hW := by
    have := bijective_smul_tilde M g W hW 1
    simp only [pow_one] at this
    exact this
  kill s t W W' hW hW' hle x hx := by
    have hlocW : IsLocalizedModule (Submonoid.powers s) (tilde.toOpen M W).hom := by
      rw [hW]; infer_instance
    have hlocW' : IsLocalizedModule (Submonoid.powers (s * t)) (tilde.toOpen M W').hom := by
      rw [hW']; infer_instance
    have hWs : W ≤ basicOpen s := hW.le
    obtain ⟨⟨m, c⟩, hmc⟩ := IsLocalizedModule.surj (Submonoid.powers s) (tilde.toOpen M W).hom x
    obtain ⟨k, hk⟩ := c.2
    have hk' : s ^ k = (c : R) := hk
    have hmc' : s ^ k • x = (tilde.toOpen M W).hom m := by
      rw [hk']; exact hmc
    have h1 : (tilde.toOpen M W').hom m = 0 := by
      rw [← res_toOpen M hle, ← hmc', res_smul M hle]
      change s ^ k • res (X := (Spec R).toTopCat) (tildeAb M).obj hle x = 0
      rw [hx, smul_zero]
    obtain ⟨c', hc'⟩ := IsLocalizedModule.exists_of_eq (S := Submonoid.powers (s * t))
      (f := (tilde.toOpen M W').hom) (h1.trans (map_zero _).symm)
    obtain ⟨N, hN⟩ := c'.2
    have hN' : (s * t) ^ N = (c' : R) := hN
    rw [smul_zero] at hc'
    have hc'' : (s * t) ^ N • m = 0 := by rw [hN']; exact hc'
    refine ⟨N, ?_⟩
    have h2 : ((s * t) ^ N * s ^ k) • x = 0 := by
      rw [mul_smul, hmc']
      exact (map_smul (tilde.toOpen M W).hom ((s * t) ^ N) m).symm.trans (by rw [hc'']; exact map_zero _)
    have h3 : (s ^ (N + k)) • ((t ^ N) • x) = (s ^ (N + k)) • (0 : (tildeAb M).obj.obj (op W)) := by
      rw [← mul_smul, smul_zero, ← h2]
      congr 1
      ring
    exact (bijective_smul_tilde M s W hWs (N + k)).1 h3
  lift s t W W' hW hW' hle y := by
    have hlocW : IsLocalizedModule (Submonoid.powers s) (tilde.toOpen M W).hom := by
      rw [hW]; infer_instance
    have hlocW' : IsLocalizedModule (Submonoid.powers (s * t)) (tilde.toOpen M W').hom := by
      rw [hW']; infer_instance
    have hWs : W ≤ basicOpen s := hW.le
    have hW's : W' ≤ basicOpen s := hW'.le.trans (basicOpen_mul_le_left s t)
    obtain ⟨⟨m, c⟩, hmc⟩ := IsLocalizedModule.surj (Submonoid.powers (s * t))
      (tilde.toOpen M W').hom y
    obtain ⟨k, hk⟩ := c.2
    have hk' : (s * t) ^ k = (c : R) := hk
    have hmc' : (s * t) ^ k • y = (tilde.toOpen M W').hom m := by
      rw [hk']; exact hmc
    obtain ⟨x, hx⟩ := (bijective_smul_tilde M s W hWs k).2 ((tilde.toOpen M W).hom m)
    have hx' : s ^ k • x = (tilde.toOpen M W).hom m := hx
    refine ⟨k, x, ?_⟩
    apply (bijective_smul_tilde M s W' hW's k).1
    change s ^ k • res (X := (Spec R).toTopCat) (tildeAb M).obj hle x = s ^ k • t ^ k • y
    rw [← res_smul M hle]
    rw [hx', res_toOpen M hle, ← hmc', ← mul_smul, mul_pow]
  D_mul s t := basicOpen_mul s t
  cover g _ _ h N hle := exists_cover_eq g h N hle
def IsBasicOpen (V : Opens (Spec R).toTopCat) : Prop := ∃ g : R, V = basicOpen g
end GroundTheory.Arith.SchemeCoh


