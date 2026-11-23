-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_CubeComplexExactAtOfIsLocalizedModuleRes
-- name    : Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_CubeComplexExactAtOfIsLocalizedModuleRes
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T03:55:06.62073+00:00
-- url     : https://prove2.me/theorems/aa95299d-b200-4e0b-a5f8-c989a572cc02
-- title:
--   Cube Complex Exact At Of Is Localized Module Res
-- statement:
--   Definitions and structural lemmas for Cube Complex Exact At Of Is Localized Module Res, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/CubeComplexExactAtOfIsLocalizedModuleRes.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_IsIsoTermComparisonRestrictScalars
import Theorems.Thm_GlobalTheory_Cube_extend_apply_of_ne
import Theorems.Thm_GlobalTheory_cubeComplex_exactAt_one_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits
universe v u
namespace GlobalTheory
section General
variable {ι : Type} [LinearOrder ι] {R : Type u} [CommRing R]
namespace Cube
omit [LinearOrder ι] in

theorem exists_smul_eq_zero_of_forall [Finite ι] (A : Cube.{v} ι R) (S : Submonoid R) {p : ℕ}
    (x : Term A p) (h : ∀ s, ∃ c ∈ S, c • x s = 0) : ∃ c ∈ S, c • x = 0 := by
  classical
  have := Fintype.ofFinite {s : Finset ι // s.card = p}
  choose c hcS hc using h
  refine ⟨∏ s, c s, S.prod_mem fun s _ => hcS s, funext fun s => ?_⟩
  rw [Pi.smul_apply, ← Finset.prod_erase_mul _ _ (Finset.mem_univ s), mul_smul, hc, smul_zero,
    Pi.zero_apply]
theorem exists_smul_eq_zero_of_d_eq_zero [Finite ι] (A : Cube.{v} ι R) (S : Submonoid R) (i : ι)
    (hA : ∀ s : Finset ι, i ∉ s → ∀ y, res A (Finset.subset_insert i s) y = 0 → ∃ c ∈ S, c • y = 0)
    {p : ℕ} (x : Term A p) (hx : d A p x = 0)
    (h0 : ∀ s : {s : Finset ι // s.card = p}, i ∈ s.1 → x s = 0) : ∃ c ∈ S, c • x = 0 := by
  refine exists_smul_eq_zero_of_forall A S x fun s => ?_
  by_cases hs : i ∈ s.1
  · exact ⟨1, S.one_mem, by rw [h0 s hs, smul_zero]⟩
  have h := congrFun hx ⟨insert i s.1, by rw [Finset.card_insert_of_notMem hs, s.2]⟩
  rw [d_apply_extend, Finset.sum_eq_single i, Pi.zero_apply, cubeSign_smul_eq_zero,
    res_congr A _ (Finset.erase_insert hs) _ (Finset.subset_insert i s.1),
    extend_apply_of_eq A x s.2] at h
  · exact hA s.1 hs _ h
  · intro j _ hji
    by_cases hc : ((insert i s.1).erase j).card = p
    · rw [extend_apply_of_eq A x hc, h0 _ (by simp [hji.symm]), map_zero, smul_zero]
    · rw [extend_apply_of_ne A x hc, map_zero, smul_zero]
  · simp
theorem exists_smul_eq_d [Finite ι] (A : Cube.{v} ι R) (S : Submonoid R) (i : ι)
    (hA : ∀ s : Finset ι, i ∉ s → ∀ y, res A (Finset.subset_insert i s) y = 0 → ∃ c ∈ S, c • y = 0)
    (hA' : ∀ s : Finset ι, i ∉ s → ∀ z, ∃ c ∈ S, ∃ y,
      res A (Finset.subset_insert i s) y = c • z)
    {p : ℕ} (x : Term A (p + 1)) (hx : d A (p + 1) x = 0) :
    ∃ c ∈ S, ∃ y, d A p y = c • x := by
  classical
  have := Fintype.ofFinite (Finset ι)
  have hy : ∀ s : Finset ι, ∃ c ∈ S, ∃ y : A.obj s, (i ∈ s → y = 0) ∧ (i ∉ s →
      res A (Finset.subset_insert i s) y =
        c • cubeSign (insert i s) i • extend A (p + 1) x (insert i s)) := by
    intro s
    by_cases hs : i ∈ s
    · exact ⟨1, S.one_mem, 0, fun _ => rfl, fun h => absurd hs h⟩
    · obtain ⟨c, hc, y, hy⟩ :=
        hA' s hs (cubeSign (insert i s) i • extend A (p + 1) x (insert i s))
      exact ⟨c, hc, y, fun h => absurd h hs, fun _ => hy⟩
  choose c hcS y hy0 hy1 using hy
  let y' : ∀ s, A.obj s := fun s => (∏ t ∈ Finset.univ.erase s, c t) • y s
  obtain ⟨e, heS, he⟩ := exists_smul_eq_zero_of_d_eq_zero A S i hA
    (d A p (fun s => y' s.1) - (∏ t, c t) • x) (by rw [map_sub, d_d, map_smul, hx]; simp) (by
      rintro ⟨t, ht⟩ hi
      obtain ⟨s, hs, rfl⟩ : ∃ s, i ∉ s ∧ t = insert i s :=
        ⟨t.erase i, by simp, (Finset.insert_erase hi).symm⟩
      rw [Pi.sub_apply, d_apply_eq_totalD A _ y' (fun _ => rfl), totalD_apply,
        Finset.sum_eq_single i,
        res_congr A _ (Finset.erase_insert hs) _ (Finset.subset_insert i s)]
      · simp only [y', map_smul]
        rw [hy1 s hs, smul_smul _ (c s), Finset.prod_erase_mul _ _ (Finset.mem_univ s), smul_comm,
          cubeSign_smul_smul, extend_apply_of_eq A x ht, Pi.smul_apply, sub_self]
      · intro j _ hji
        simp only [y']
        rw [hy0 _ (by simp [hji.symm]), smul_zero, map_zero, smul_zero]
      · simp)
  refine ⟨e * ∏ t, c t, S.mul_mem heS (S.prod_mem fun t _ => hcS t), e • (fun s => y' s.1 : Term A p), ?_⟩
  rw [smul_sub, sub_eq_zero] at he
  rw [map_smul, he, mul_smul]
end Cube
theorem smul_homologyπ_eq_zero (K : CochainComplex (ModuleCat.{v} R) ℕ) (q p : ℕ)
    (z : K.cycles p) (c : R) (y : K.X q) (h : (K.d q p).hom y = c • (K.iCycles p).hom z) :
    c • (K.homologyπ p).hom z = 0 := by
  have h1 : (K.toCycles q p).hom y = c • z := by
    apply (ModuleCat.mono_iff_injective (K.iCycles p)).1 inferInstance
    have := congr(($(K.toCycles_i q p)).hom y)
    exact this.trans (h.trans (map_smul _ _ _).symm)
  rw [← map_smul, ← h1]
  exact congr(($(K.toCycles_comp_homologyπ q p)).hom y)
theorem cubeComplex_exists_smul_homology_eq_zero [Finite ι] (A : Cube.{v} ι R) (S : Submonoid R)
    (i : ι)
    (hA : ∀ s : Finset ι, i ∉ s → ∀ y,
      Cube.res A (Finset.subset_insert i s) y = 0 → ∃ c ∈ S, c • y = 0)
    (hA' : ∀ s : Finset ι, i ∉ s → ∀ z, ∃ c ∈ S, ∃ y,
      Cube.res A (Finset.subset_insert i s) y = c • z)
    (p : ℕ) (x : (cubeComplex A).homology p) : ∃ c ∈ S, c • x = 0 := by
  obtain ⟨z, rfl⟩ :=
    (ModuleCat.epi_iff_surjective ((cubeComplex A).homologyπ p)).1 inferInstance x
  have hz : Cube.d A p (((cubeComplex A).iCycles p).hom z) = 0 := by
    have := (cubeComplex A).iCycles_d p (p + 1)
    rw [cubeComplex_d] at this
    exact congr(($this).hom z)
  cases p with
  | zero =>
    obtain ⟨c, hc, h⟩ := Cube.exists_smul_eq_zero_of_d_eq_zero A S i hA _ hz fun s hs => by
      rw [Finset.card_eq_zero.1 s.2] at hs
      simp at hs
    exact ⟨c, hc, smul_homologyπ_eq_zero _ 0 0 z c 0 ((map_zero _).trans h.symm)⟩
  | succ p =>
    obtain ⟨c, hc, y, h⟩ := Cube.exists_smul_eq_d A S i hA hA' _ hz
    refine ⟨c, hc, smul_homologyπ_eq_zero _ p (p + 1) z c y ?_⟩
    rw [cubeComplex_d]
    exact h
theorem cubeComplex_exists_smul_homology_eq_zero_of_isLocalizedModule [Finite ι]
    (A : Cube.{v} ι R) (S : Submonoid R) (i : ι)
    (hA : ∀ s : Finset ι, i ∉ s → IsLocalizedModule S (Cube.res A (Finset.subset_insert i s)))
    (p : ℕ) (x : (cubeComplex A).homology p) : ∃ c ∈ S, c • x = 0 := by
  refine cubeComplex_exists_smul_homology_eq_zero A S i (fun s hs y hy => ?_) (fun s hs z => ?_) p x
  · have := hA s hs
    obtain ⟨c, hc⟩ := (IsLocalizedModule.eq_zero_iff S _).1 hy
    exact ⟨c, c.2, hc⟩
  · obtain ⟨⟨y, c⟩, h⟩ := (hA s hs).surj z
    exact ⟨c, c.2, y, h.symm⟩
theorem cubeComplex_exists_pow_smul_homology_eq_zero [Finite ι] (A : Cube.{v} ι R) (a : R) (i : ι)
    (hA : ∀ s : Finset ι, i ∉ s →
      IsLocalizedModule.Away a (Cube.res A (Finset.subset_insert i s)))
    (p : ℕ) (x : (cubeComplex A).homology p) : ∃ n : ℕ, a ^ n • x = 0 := by
  obtain ⟨_, ⟨n, rfl⟩, h⟩ :=
    cubeComplex_exists_smul_homology_eq_zero_of_isLocalizedModule A (.powers a) i hA p x
  exact ⟨n, h⟩
theorem cubeComplex_exactAt_of_isLocalizedModule_res [Finite ι] (A : Cube.{v} ι R) (f : ι → R)
    (hA : ∀ (i : ι) (s : Finset ι), i ∉ s →
      IsLocalizedModule.Away (f i) (Cube.res A (Finset.subset_insert i s)))
    (hf : Ideal.span (Set.range f) = ⊤) (p : ℕ) : (cubeComplex A).ExactAt p := by
  rw [HomologicalComplex.exactAt_iff_isZero_homology, ModuleCat.isZero_iff_subsingleton]
  refine subsingleton_of_forall_eq 0 fun x => ?_
  refine (Submodule.mem_bot R).1
    (Submodule.mem_of_span_eq_top_of_smul_pow_mem ⊥ _ hf x ?_)
  rintro ⟨_, i, rfl⟩
  exact cubeComplex_exists_pow_smul_homology_eq_zero A (f i) i (hA i) p x
end General
section Away
variable {R : Type*} [CommRing R] {M N P : Type*} [AddCommGroup M] [AddCommGroup N]
  [AddCommGroup P] [Module R M] [Module R N] [Module R P]
theorem isUnit_algebraMap_end_of_dvd {a b : R} (h : a ∣ b)
    (hb : IsUnit (algebraMap R (Module.End R N) b)) :
    IsUnit (algebraMap R (Module.End R N) a) := by
  obtain ⟨c, rfl⟩ := h
  rw [map_mul] at hb
  exact ((Commute.isUnit_mul_iff (Algebra.commutes a _)).1 hb).1
theorem isUnit_powers_of_dvd {a b : R} (h : a ∣ b) (g : M →ₗ[R] N) [IsLocalizedModule.Away b g]
    (x : Submonoid.powers a) : IsUnit (algebraMap R (Module.End R N) x) := by
  obtain ⟨_, n, rfl⟩ := x
  rw [map_pow]
  exact (isUnit_algebraMap_end_of_dvd h (IsLocalizedModule.Away.isUnit_algebraMap g b)).pow n
theorem isLocalizedModule_away_of_comp {a b : R} (g : M →ₗ[R] N) (h : N →ₗ[R] P)
    [IsLocalizedModule.Away b g] [IsLocalizedModule.Away (a * b) (h ∘ₗ g)] :
    IsLocalizedModule.Away a h := by
  have hb := isUnit_powers_of_dvd (dvd_mul_left b a) (h ∘ₗ g)
  refine IsLocalizedModule.Away.mk_of_addCommGroup
    (isUnit_algebraMap_end_of_dvd (dvd_mul_right a b)
      (IsLocalizedModule.Away.isUnit_algebraMap (h ∘ₗ g) _)) (fun z => ?_) (fun y hy => ?_)
  · obtain ⟨n, m, hm⟩ := IsLocalizedModule.Away.surj (h ∘ₗ g) (a * b) z
    refine ⟨n, IsLocalizedModule.mk' g m (⟨b ^ n, n, rfl⟩ : Submonoid.powers b), ?_⟩
    apply ((Module.End.isUnit_iff _).1 (hb ⟨b ^ n, n, rfl⟩)).1
    simp only [Module.algebraMap_end_apply]
    rw [← map_smul, smul_smul, mul_comm, ← mul_pow, hm]
    exact congrArg h (IsLocalizedModule.mk'_cancel' g m (⟨b ^ n, n, rfl⟩ : Submonoid.powers b)).symm
  · obtain ⟨k, m, hm⟩ := IsLocalizedModule.Away.surj g b y
    have h0 : (h ∘ₗ g) m = (h ∘ₗ g) 0 := by
      rw [LinearMap.comp_apply, ← hm, map_smul, hy, smul_zero, map_zero]
    obtain ⟨n, hn⟩ := IsLocalizedModule.Away.exists_of_eq (a * b) h0
    refine ⟨n, ?_⟩
    apply IsLocalizedModule.smul_injective g (⟨b ^ (n + k), n + k, rfl⟩ : Submonoid.powers b)
    have := congrArg g hn
    rw [smul_zero, map_zero, map_smul, ← hm, smul_smul] at this
    change b ^ (n + k) • a ^ n • y = b ^ (n + k) • (0 : N)
    rw [smul_zero, smul_smul, show b ^ (n + k) * a ^ n = (a * b) ^ n * b ^ k by ring]
    exact this
end Away
section Loc
variable {ι : Type} {R : Type u} [CommRing R]
theorem Cube.isLocalizedModule_res_insert [DecidableEq ι] (A : Cube.{v} ι R) (f : ι → R)
    {M : Type*} [AddCommGroup M] [Module R M] (g : ∀ s, M →ₗ[R] A.obj s)
    (hg : ∀ s, IsLocalizedModule.Away (∏ i ∈ s, f i) (g s))
    (hres : ∀ {s t : Finset ι} (h : s ⊆ t) (m : M), Cube.res A h (g s m) = g t m)
    (i : ι) (s : Finset ι) (hi : i ∉ s) :
    IsLocalizedModule.Away (f i) (Cube.res A (Finset.subset_insert i s)) := by
  have h1 := hg s
  have h2 : IsLocalizedModule.Away (f i * ∏ j ∈ s, f j)
      (Cube.res A (Finset.subset_insert i s) ∘ₗ g s) := by
    rw [show Cube.res A (Finset.subset_insert i s) ∘ₗ g s = g (insert i s) from
      LinearMap.ext (hres _), ← Finset.prod_insert hi]
    exact hg _
  exact isLocalizedModule_away_of_comp (b := ∏ j ∈ s, f j) (g s) _
variable (f : ι → R) (M : Type v) [AddCommGroup M] [Module R M]
noncomputable def locRes {s t : Finset ι} (h : s ⊆ t) :
    LocalizedModule (.powers (∏ i ∈ s, f i)) M →ₗ[R] LocalizedModule (.powers (∏ i ∈ t, f i)) M :=
  LocalizedModule.lift _ (LocalizedModule.mkLinearMap _ M)
    (isUnit_powers_of_dvd (Finset.prod_dvd_prod_of_subset s t f h) (LocalizedModule.mkLinearMap _ M))
@[simp]
theorem locRes_mk_one {s t : Finset ι} (h : s ⊆ t) (m : M) :
    locRes f M h (LocalizedModule.mk m 1) = LocalizedModule.mk m 1 :=
  LocalizedModule.lift_mk_one _ _ _ m
theorem locRes_comp_mkLinearMap {s t : Finset ι} (h : s ⊆ t) :
    locRes f M h ∘ₗ LocalizedModule.mkLinearMap _ M = LocalizedModule.mkLinearMap _ M :=
  LocalizedModule.lift_comp _ _ _
theorem locRes_self (s : Finset ι) : locRes f M (subset_refl s) = LinearMap.id :=
  LocalizedModule.lift_unique _ _ _ _ rfl
theorem locRes_comp {s t w : Finset ι} (h : s ⊆ t) (h' : t ⊆ w) :
    locRes f M h' ∘ₗ locRes f M h = locRes f M (h.trans h') :=
  (LocalizedModule.lift_unique _ _ _ _ (by
    rw [LinearMap.comp_assoc, locRes_comp_mkLinearMap, locRes_comp_mkLinearMap])).symm
noncomputable def locCube : Cube.{max u v} ι R :=
  Cube.mk (fun s => ModuleCat.of R (LocalizedModule (.powers (∏ i ∈ s, f i)) M))
    (fun h => locRes f M h) (fun s x => congr($(locRes_self f M s) x))
    (fun h h' x => congr($(locRes_comp f M h h') x))
noncomputable def toLocCube (s : Finset ι) : M →ₗ[R] (locCube f M).obj s :=
  LocalizedModule.mkLinearMap _ M
instance isLocalizedModule_toLocCube (s : Finset ι) :
    IsLocalizedModule.Away (∏ i ∈ s, f i) (toLocCube f M s) :=
  localizedModuleIsLocalizedModule _
@[simp]
theorem res_toLocCube {s t : Finset ι} (h : s ⊆ t) (m : M) :
    Cube.res (locCube f M) h (toLocCube f M s m) = toLocCube f M t m :=
  locRes_mk_one f M h m
theorem isLocalizedModule_res_locCube [DecidableEq ι] (i : ι) (s : Finset ι) (hi : i ∉ s) :
    IsLocalizedModule.Away (f i) (Cube.res (locCube f M) (Finset.subset_insert i s)) :=
  Cube.isLocalizedModule_res_insert _ f (toLocCube f M) inferInstance (res_toLocCube f M) i s hi
theorem toLocCube_empty_bijective : Function.Bijective (toLocCube f M ∅) := by
  constructor
  · intro x y h
    obtain ⟨n, hn⟩ := IsLocalizedModule.Away.exists_of_eq (∏ i ∈ (∅ : Finset ι), f i) h
    simpa using hn
  · intro y
    obtain ⟨n, x, hx⟩ := IsLocalizedModule.Away.surj (toLocCube f M ∅) (∏ i ∈ (∅ : Finset ι), f i) y
    exact ⟨x, by simpa using hx.symm⟩
noncomputable def locCubeEmptyEquiv : M ≃ₗ[R] (locCube f M).obj ∅ :=
  LinearEquiv.ofBijective _ (toLocCube_empty_bijective f M)
@[simp]
theorem locCubeEmptyEquiv_apply (m : M) : locCubeEmptyEquiv f M m = toLocCube f M ∅ m := rfl
theorem isLocalizedModule_toLocCube_singleton (i : ι) :
    IsLocalizedModule.Away (f i) (toLocCube f M {i}) := by
  have := isLocalizedModule_toLocCube f M {i}
  rwa [Finset.prod_singleton] at this
noncomputable def locCubeIso (A : Cube.{max u v} ι R) (g : ∀ s, M →ₗ[R] A.obj s)
    [hg : ∀ s, IsLocalizedModule.Away (∏ i ∈ s, f i) (g s)]
    (hres : ∀ {s t : Finset ι} (h : s ⊆ t) (m : M), Cube.res A h (g s m) = g t m) :
    locCube f M ≅ A :=
  Cube.isoMk (fun s => IsLocalizedModule.linearEquiv (.powers (∏ i ∈ s, f i)) (toLocCube f M s) (g s))
    fun {s t} h x => by
      have := IsLocalizedModule.ext (.powers (∏ i ∈ s, f i)) (toLocCube f M s)
        (isUnit_powers_of_dvd (Finset.prod_dvd_prod_of_subset s t f h) (g t))
        (j := (IsLocalizedModule.linearEquiv (.powers (∏ i ∈ t, f i))
          (toLocCube f M t) (g t)).toLinearMap ∘ₗ Cube.res _ h)
        (k := Cube.res A h ∘ₗ (IsLocalizedModule.linearEquiv (.powers (∏ i ∈ s, f i))
          (toLocCube f M s) (g s)).toLinearMap) (by ext m; simp [hres])
      exact congr($this x)
variable {M} in

noncomputable def locCubeMap {N : Type v} [AddCommGroup N] [Module R N] (φ : M →ₗ[R] N) :
    locCube f M ⟶ locCube f N :=
  Cube.homMk (fun s => IsLocalizedModule.map (.powers (∏ i ∈ s, f i)) (toLocCube f M s)
      (toLocCube f N s) φ)
    fun {s t} h x => by
      have := IsLocalizedModule.ext (.powers (∏ i ∈ s, f i)) (toLocCube f M s)
        (isUnit_powers_of_dvd (Finset.prod_dvd_prod_of_subset s t f h) (toLocCube f N t))
        (j := IsLocalizedModule.map (.powers (∏ i ∈ t, f i)) (toLocCube f M t)
          (toLocCube f N t) φ ∘ₗ Cube.res _ h)
        (k := Cube.res _ h ∘ₗ IsLocalizedModule.map (.powers (∏ i ∈ s, f i)) (toLocCube f M s)
          (toLocCube f N s) φ) (by ext m; simp)
      exact congr($this x)
variable [LinearOrder ι] [Finite ι]
variable {f}
theorem locCube_exactAt (hf : Ideal.span (Set.range f) = ⊤) (p : ℕ) :
    (cubeComplex (locCube f M)).ExactAt p :=
  cubeComplex_exactAt_of_isLocalizedModule_res _ f (isLocalizedModule_res_locCube f M) hf p
variable (f) in

noncomputable def locCubeAug : M →ₗ[R] Cube.Term (locCube f M) 1 :=
  LinearMap.pi fun s => toLocCube f M s.1
end Loc
section Examples
example (p : ℕ) : (cubeComplex (locCube ![(2 : ℤ), 3] ℤ)).ExactAt p := by
  refine locCube_exactAt ℤ ((Ideal.eq_top_iff_one _).2 ?_) p
  have := Ideal.sub_mem _ (Ideal.subset_span (s := Set.range ![(2 : ℤ), 3]) ⟨1, rfl⟩)
    (Ideal.subset_span ⟨0, rfl⟩)
  exact this
example : ¬ (cubeComplex (locCube (fun _ : Fin 1 => (2 : ℤ)) ℤ)).ExactAt 1 := by
  rw [cubeComplex_exactAt_one_iff]
  intro h
  haveI := Cube.subsingleton_term (locCube (fun _ : Fin 1 => (2 : ℤ)) ℤ) (p := 2) (by simp)
  have hl := isLocalizedModule_toLocCube_singleton (fun _ : Fin 1 => (2 : ℤ)) ℤ 0
  let y := IsLocalizedModule.mk' (toLocCube (fun _ : Fin 1 => (2 : ℤ)) ℤ {0}) 1
    (⟨2, 1, pow_one 2⟩ : Submonoid.powers (2 : ℤ))
  obtain ⟨a, ha⟩ := (h (Cube.termOneEquiv _ (Fin.cases y fun i => i.elim0))).1
    (Subsingleton.elim _ _)
  obtain ⟨m, rfl⟩ := (toLocCube_empty_bijective _ ℤ).2 a
  have h1 := congrFun ha ⟨{0}, Finset.card_singleton _⟩
  rw [Cube.aug_apply, res_toLocCube, Cube.termOneEquiv_apply] at h1
  have h2 : toLocCube (fun _ : Fin 1 => (2 : ℤ)) ℤ {0} 1 =
      toLocCube (fun _ : Fin 1 => (2 : ℤ)) ℤ {0} ((2 : ℤ) • m) :=
    (IsLocalizedModule.mk'_eq_iff.1 (show y = _ from h1.symm)).trans
      ((toLocCube (fun _ : Fin 1 => (2 : ℤ)) ℤ {0}).map_smul (2 : ℤ) m).symm
  obtain ⟨n, hn⟩ := IsLocalizedModule.Away.exists_of_eq (2 : ℤ) h2
  simp only [smul_eq_mul, mul_eq_mul_left_iff] at hn
  rcases hn with hn | hn
  · omega
  · exact absurd hn (by positivity)
end Examples
end GlobalTheory


