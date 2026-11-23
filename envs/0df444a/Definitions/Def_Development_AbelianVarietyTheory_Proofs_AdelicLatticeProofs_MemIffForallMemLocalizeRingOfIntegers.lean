-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_MemIffForallMemLocalizeRingOfIntegers
-- name    : Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_MemIffForallMemLocalizeRingOfIntegers
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T03:30:59.04943+00:00
-- url     : https://prove2.me/theorems/4551edc4-539e-40e7-bdd6-596056dcebcb
-- title:
--   Mem Iff Forall Mem Localize Ring Of Integers
-- statement:
--   Definitions and structural lemmas for Mem Iff Forall Mem Localize Ring Of Integers, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/MemIffForallMemLocalizeRingOfIntegers.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_MemSaturatedOrderIsoSubspaceSpanSymmApply
import Definitions.Def_ReciprocityTheory_SemistableReduction_TorsionNonvanishStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum Matrix
open scoped nonZeroDivisors
noncomputable section
namespace GlobalTheory.LocalLattice
set_option linter.unusedSectionVars false
section Denominators
variable {O K : Type*} [CommRing O] [IsDomain O] [Field K] [Algebra O K] [IsFractionRing O K]
  {A : Type*} [CommRing A] [Algebra O A] [Algebra A K] [IsScalarTower O A K]
  {V : Type*} [AddCommGroup V] [Module K V] [Module O V] [Module A V] [IsScalarTower O K V]
  [IsScalarTower A K V] [IsScalarTower O A V]
omit [IsDomain O] [IsScalarTower O A K] [IsScalarTower A K V] [Algebra A K] in

theorem exists_smul_mem {N : Submodule A V} (hN : Submodule.span K (N : Set V) = ⊤) (x : V) :
    ∃ d ∈ O⁰, d • x ∈ N :=
  (mem_span_localization_iff K O⁰ (N.restrictScalars O) x).1 (by
    rw [Submodule.coe_restrictScalars, hN]; trivial)
omit [IsDomain O] [IsScalarTower O A K] [IsScalarTower A K V] [Algebra A K] in

theorem exists_smul_mem_of_finite {N : Submodule A V} (hN : Submodule.span K (N : Set V) = ⊤)
    {s : Set V} (hs : s.Finite) : ∃ d ∈ O⁰, ∀ x ∈ s, d • x ∈ N := by
  induction s, hs using Set.Finite.induction_on with
  | empty => exact ⟨1, one_mem _, by simp⟩
  | @insert a s _ _ ih =>
    obtain ⟨d, hd, h⟩ := ih
    obtain ⟨e, he, h'⟩ := exists_smul_mem (O := O) hN a
    refine ⟨d * e, mul_mem hd he, ?_⟩
    rintro x (rfl | hx)
    · rw [mul_smul]; exact N.smul_of_tower_mem d h'
    · rw [mul_comm, mul_smul]; exact N.smul_of_tower_mem e (h x hx)
omit [IsDomain O] [IsScalarTower O A K] [IsScalarTower A K V] [Algebra A K] in

theorem exists_smul_le {M N : Submodule A V} (hM : M.FG)
    (hN : Submodule.span K (N : Set V) = ⊤) : ∃ d ∈ O⁰, ∀ x ∈ M, d • x ∈ N := by
  obtain ⟨s, rfl⟩ := hM
  obtain ⟨d, hd, h⟩ := exists_smul_mem_of_finite (O := O) hN s.finite_toSet
  refine ⟨d, hd, fun x hx => ?_⟩
  induction hx using Submodule.span_induction with
  | mem x hx => exact h x hx
  | zero => simp
  | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
  | smul a x _ hx => rw [smul_comm]; exact N.smul_mem a hx
omit [IsScalarTower O A K] [IsScalarTower A K V] [Algebra A K] in

theorem span_eq_top_of_smul_mem {s : Set V} {N : Submodule A V} (hs : Submodule.span K s = ⊤)
    {d : O} (hd : d ∈ O⁰) (h : ∀ x ∈ s, d • x ∈ N) : Submodule.span K (N : Set V) = ⊤ := by
  rw [eq_top_iff, ← hs, Submodule.span_le]
  intro x hx
  have hd' : algebraMap O K d ≠ 0 := by simpa using nonZeroDivisors.ne_zero hd
  have : x = (algebraMap O K d)⁻¹ • d • x := by
    rw [← algebraMap_smul K d x, smul_smul, inv_mul_cancel₀ hd', one_smul]
  rw [this]
  exact Submodule.smul_mem _ _ (Submodule.subset_span (h x hx))
omit [IsScalarTower O A K] [IsScalarTower A K V] [Algebra A K] in
include K in

theorem fg_of_smul_mem [IsNoetherianRing A] {M N : Submodule A V} (hN : N.FG)
    {d : O} (hd : d ∈ O⁰) (h : ∀ x ∈ M, d • x ∈ N) : M.FG := by
  have hd' : algebraMap O K d ≠ 0 := by simpa using nonZeroDivisors.ne_zero hd
  have hinj : Function.Injective (LinearMap.lsmul A V (algebraMap O A d)) := by
    intro x y hxy
    simp only [LinearMap.lsmul_apply, algebraMap_smul] at hxy
    rw [← algebraMap_smul K d x, ← algebraMap_smul K d y] at hxy
    exact smul_right_injective V hd' hxy
  refine Submodule.fg_of_fg_map_injective _ hinj (hN.of_le ?_)
  rintro _ ⟨x, hx, rfl⟩
  simpa using h x hx
end Denominators
section Localize
variable {O : Type*} (K : Type*) [CommRing O] [IsDedekindDomain O] [Field K] [Algebra O K]
  [IsFractionRing O K]
  {V : Type*} [AddCommGroup V] [Module K V] [Module O V] [IsScalarTower O K V]
instance instIsScalarTowerLocalRing (v : HeightOneSpectrum O) :
    IsScalarTower O (v.valuationSubringAtPrime K) V :=
  IsScalarTower.to₁₂₄ O (v.valuationSubringAtPrime K) K V
def localize (v : HeightOneSpectrum O) (L : Submodule O V) :
    Submodule (v.valuationSubringAtPrime K) V :=
  Submodule.span _ (L : Set V)
variable {K}
theorem localize_def (v : HeightOneSpectrum O) (L : Submodule O V) :
    localize K v L = Submodule.span (v.valuationSubringAtPrime K) (L : Set V) := rfl
theorem mem_localRing_iff_valuation (v : HeightOneSpectrum O) (x : K) :
    x ∈ v.valuationSubringAtPrime K ↔ v.valuation K x ≤ 1 := by
  rw [valuationSubringAtPrime_eq_valuationSubring]; rfl
theorem mem_localize_iff (v : HeightOneSpectrum O) (L : Submodule O V) (x : V) :
    x ∈ localize K v L ↔ ∃ s ∉ v.asIdeal, s • x ∈ L :=
  mem_span_localization_iff _ v.asIdeal.primeCompl L x
theorem mem_localize_of_mem (v : HeightOneSpectrum O) {L : Submodule O V} {x : V} (hx : x ∈ L) :
    x ∈ localize K v L := Submodule.subset_span hx
theorem localize_restrictScalars (v : HeightOneSpectrum O)
    (M : Submodule (v.valuationSubringAtPrime K) V) :
    localize K v (M.restrictScalars O) = M := Submodule.span_eq M
theorem mem_of_smul_mem (v : HeightOneSpectrum O) {M : Submodule (v.valuationSubringAtPrime K) V}
    {s : O} (hs : s ∉ v.asIdeal) {x : V} (hx : s • x ∈ M) : x ∈ M := by
  rw [← localize_restrictScalars v M, mem_localize_iff]
  exact ⟨s, hs, hx⟩
instance isLattice_localize (v : HeightOneSpectrum O) (L : Submodule O V)
    [h : Submodule.IsLattice K L] : Submodule.IsLattice K (localize K v L) where
  fg := by
    obtain ⟨s, rfl⟩ := h.fg
    exact ⟨s, (Submodule.span_span_of_tower O _ _).symm⟩
  span_eq_top := by
    rw [localize_def, Submodule.span_span_of_tower, h.span_eq_top]
theorem mem_of_forall_mem_localize {L : Submodule O V} {x : V}
    (hx : x ∈ Submodule.span K (L : Set V)) (h : ∀ v : HeightOneSpectrum O, x ∈ localize K v L) :
    x ∈ L := by
  obtain ⟨d, hd, hdx⟩ := (mem_span_localization_iff K O⁰ L x).1 hx
  by_contra hxL
  let J : Ideal O := L.comap (LinearMap.toSpanSingleton O V x)
  have hJ : J ≠ ⊤ := fun hJ => hxL (by simpa [J] using (Ideal.eq_top_iff_one J).1 hJ)
  obtain ⟨m, hm, hJm⟩ := Ideal.exists_le_maximal J hJ
  have hm0 : m ≠ ⊥ := fun h0 => nonZeroDivisors.ne_zero hd (by
    simpa [h0] using hJm (show d ∈ J from hdx))
  obtain ⟨s, hs, hsx⟩ := (mem_localize_iff _ L x).1 (h ⟨m, hm.isPrime, hm0⟩)
  exact hs (hJm (show s ∈ J from hsx))
theorem mem_iff_forall_mem_localize {L : Submodule O V} (hL : Submodule.span K (L : Set V) = ⊤)
    (x : V) : x ∈ L ↔ ∀ v : HeightOneSpectrum O, x ∈ localize K v L :=
  ⟨fun hx v => mem_localize_of_mem v hx, mem_of_forall_mem_localize (by rw [hL]; trivial)⟩
theorem iInf_localize {L : Submodule O V} (hL : Submodule.span K (L : Set V) = ⊤) :
    ⨅ v : HeightOneSpectrum O, (localize K v L).restrictScalars O = L := by
  ext x
  simp [mem_iff_forall_mem_localize hL x]
theorem eventually_notMem {d : O} (hd : d ∈ O⁰) :
    ∀ᶠ v : HeightOneSpectrum O in Filter.cofinite, d ∉ v.asIdeal := by
  have := Ideal.finite_factors (I := Ideal.span {d}) (by simpa using nonZeroDivisors.ne_zero hd)
  simpa [Filter.eventually_cofinite, Ideal.dvd_span_singleton] using this
theorem eventually_localize_le {L L' : Submodule O V} (hL : L.FG)
    (hL' : Submodule.span K (L' : Set V) = ⊤) :
    ∀ᶠ v : HeightOneSpectrum O in Filter.cofinite, localize K v L ≤ localize K v L' := by
  obtain ⟨d, hd, h⟩ := exists_smul_le (O := O) hL hL'
  filter_upwards [eventually_notMem hd] with v hv
  exact Submodule.span_le.2 fun x hx => (mem_localize_iff v L' x).2 ⟨d, hv, h x hx⟩
theorem eventually_localize_eq (L L' : Submodule O V) [h : Submodule.IsLattice K L]
    [h' : Submodule.IsLattice K L'] :
    ∀ᶠ v : HeightOneSpectrum O in Filter.cofinite, localize K v L = localize K v L' := by
  filter_upwards [eventually_localize_le h.fg h'.span_eq_top,
    eventually_localize_le h'.fg h.span_eq_top] with v h₁ h₂ using le_antisymm h₁ h₂
omit [IsDedekindDomain O] in
theorem exists_mem_submonoid_forall {ι : Type*} {T : Set ι} (hT : T.Finite) (S : Submonoid O)
    (P : ι → O → Prop) (hP : ∀ i s t, P i s → P i (t * s)) (h : ∀ i ∈ T, ∃ s ∈ S, P i s) :
    ∃ s ∈ S, ∀ i ∈ T, P i s := by
  induction T, hT using Set.Finite.induction_on with
  | empty => exact ⟨1, one_mem _, by simp⟩
  | @insert a T _ _ ih =>
    obtain ⟨d, hd, h₁⟩ := ih fun i hi => h i (Set.mem_insert_of_mem _ hi)
    obtain ⟨e, he, h₂⟩ := h a (Set.mem_insert _ _)
    refine ⟨d * e, mul_mem hd he, ?_⟩
    rintro x (rfl | hx)
    · exact hP _ _ _ h₂
    · rw [mul_comm]; exact hP _ _ _ (h₁ x hx)
theorem exists_notMem_smul_mem {v w : HeightOneSpectrum O} (hvw : w ≠ v)
    {M : Submodule (w.valuationSubringAtPrime K) V} {d : O} (hd : d ∈ O⁰) {x : V}
    (hx : d • x ∈ M) : ∃ s ∉ v.asIdeal, s • x ∈ M := by
  have hnle : ¬ w.asIdeal ≤ v.asIdeal := fun hle => hvw (HeightOneSpectrum.ext
    (w.isMaximal.eq_of_le v.isPrime.ne_top hle))
  obtain ⟨s, hsw, hsv⟩ := SetLike.not_le_iff_exists.1 hnle
  have hd' : algebraMap O K d ≠ 0 := by simpa using nonZeroDivisors.ne_zero hd
  have hvd : w.valuation K (algebraMap O K d) ≠ 0 := by simpa using hd'
  have hs1 : w.valuation K (algebraMap O K s) < 1 := (w.valuation_lt_one_iff_mem s).2 hsw
  obtain ⟨n, hn⟩ := exists_pow_lt₀ hs1 (Units.mk0 _ hvd)
  have hmem : algebraMap O K s ^ n / algebraMap O K d ∈ w.valuationSubringAtPrime K := by
    rw [mem_localRing_iff_valuation, map_div₀, map_pow, div_le_one₀ (zero_lt_iff.2 hvd)]
    exact hn.le
  refine ⟨s ^ n, fun h => hsv (v.isPrime.mem_of_pow_mem n h), ?_⟩
  have : s ^ n • x = (⟨_, hmem⟩ : w.valuationSubringAtPrime K) • d • x := by
    change _ = (algebraMap O K s ^ n / algebraMap O K d) • d • x
    rw [← algebraMap_smul K d x, smul_smul, div_mul_cancel₀ _ hd', ← map_pow, algebraMap_smul]
  rw [this]
  exact M.smul_mem _ hx
def glue (M : ∀ v : HeightOneSpectrum O, Submodule (v.valuationSubringAtPrime K) V) :
    Submodule O V :=
  ⨅ v, (M v).restrictScalars O
theorem mem_glue {M : ∀ v : HeightOneSpectrum O, Submodule (v.valuationSubringAtPrime K) V}
    {x : V} : x ∈ glue M ↔ ∀ v, x ∈ M v := by
  simp [glue]
theorem glue_localize {L : Submodule O V} (hL : Submodule.span K (L : Set V) = ⊤) :
    glue (fun v => localize K v L) = L := iInf_localize hL
theorem localize_glue {M : ∀ v : HeightOneSpectrum O, Submodule (v.valuationSubringAtPrime K) V}
    (hM : Submodule.span K (glue M : Set V) = ⊤) (v : HeightOneSpectrum O) :
    localize K v (glue M) = M v := by
  refine le_antisymm (Submodule.span_le.2 fun x hx => mem_glue.1 hx v) fun x hx => ?_
  obtain ⟨d, hd, hdx⟩ := exists_smul_mem (O := O) hM x
  rw [mem_glue] at hdx
  have hfin : {w : HeightOneSpectrum O | d ∈ w.asIdeal}.Finite := by
    simpa [Filter.eventually_cofinite] using eventually_notMem hd
  obtain ⟨s, hs, h⟩ := exists_mem_submonoid_forall hfin v.asIdeal.primeCompl
    (fun w s => s • x ∈ M w)
    (fun w s t h => by rw [mul_smul]; exact (M w).smul_of_tower_mem t h)
    (fun w _ => by
      by_cases hwv : w = v
      · subst hwv; exact ⟨1, one_mem _, by simpa using hx⟩
      · exact exists_notMem_smul_mem hwv hd (hdx w))
  refine (mem_localize_iff v _ x).2 ⟨s, hs, mem_glue.2 fun w => ?_⟩
  by_cases hw : d ∈ w.asIdeal
  · exact h w hw
  · exact (M w).smul_of_tower_mem s (mem_of_smul_mem w hw (hdx w))
theorem isLattice_glue (L : Submodule O V) [hL : Submodule.IsLattice K L]
    (M : ∀ v : HeightOneSpectrum O, Submodule (v.valuationSubringAtPrime K) V)
    (hM : ∀ v, Submodule.IsLattice K (M v))
    (hML : ∀ᶠ v in Filter.cofinite, M v = localize K v L) : Submodule.IsLattice K (glue M) := by
  have hfin := Filter.eventually_cofinite.1 hML
  constructor
  · obtain ⟨d, hd, h⟩ := exists_mem_submonoid_forall hfin O⁰
      (fun w s => ∀ x ∈ M w, s • x ∈ localize K w L)
      (fun w s t h x hx => by rw [mul_smul]; exact Submodule.smul_of_tower_mem _ t (h x hx))
      (fun w _ => exists_smul_le (hM w).fg (isLattice_localize w L).span_eq_top)
    refine fg_of_smul_mem (K := K) hL.fg hd fun x hx => ?_
    refine (mem_iff_forall_mem_localize hL.span_eq_top _).2 fun w => ?_
    by_cases hw : M w = localize K w L
    · rw [← hw]; exact Submodule.smul_of_tower_mem _ d (mem_glue.1 hx w)
    · exact h w hw x (mem_glue.1 hx w)
  · obtain ⟨d, hd, h⟩ := exists_mem_submonoid_forall hfin O⁰
      (fun w s => ∀ x ∈ localize K w L, s • x ∈ M w)
      (fun w s t h x hx => by rw [mul_smul]; exact Submodule.smul_of_tower_mem _ t (h x hx))
      (fun w _ => exists_smul_le (isLattice_localize w L).fg (hM w).span_eq_top)
    refine span_eq_top_of_smul_mem hL.span_eq_top hd fun x hx => mem_glue.2 fun w => ?_
    by_cases hw : M w = localize K w L
    · rw [hw]; exact Submodule.smul_of_tower_mem _ d (mem_localize_of_mem w hx)
    · exact h w hw x (mem_localize_of_mem w hx)
def latticeEquivFamilies (L : Submodule O V) [Submodule.IsLattice K L] :
    {L' : Submodule O V // Submodule.IsLattice K L'} ≃
      {M : ∀ v : HeightOneSpectrum O, Submodule (v.valuationSubringAtPrime K) V //
        (∀ v, Submodule.IsLattice K (M v)) ∧ ∀ᶠ v in Filter.cofinite, M v = localize K v L} where
  toFun L' := haveI := L'.2
    ⟨fun v => localize K v L'.1, fun v => isLattice_localize v _, eventually_localize_eq _ _⟩
  invFun M := ⟨glue M.1, isLattice_glue L M.1 M.2.1 M.2.2⟩
  left_inv L' := Subtype.ext (glue_localize L'.2.span_eq_top)
  right_inv M := Subtype.ext (funext (localize_glue (isLattice_glue L M.1 M.2.1 M.2.2).span_eq_top))
end Localize
section Frame
variable (A : Type*) {K : Type*} [CommRing A] [Field K] [Algebra A K]
  {ι : Type*} [Fintype ι] [DecidableEq ι]
def frameLattice (g : GL ι K) : Submodule A (ι → K) :=
  Submodule.span A (Set.range (g : Matrix ι ι K).col)
variable {A}
theorem mem_frameLattice_iff (g : GL ι K) (x : ι → K) :
    x ∈ frameLattice A g ↔
      ∃ a : ι → A, (g : Matrix ι ι K) *ᵥ (fun i => algebraMap A K (a i)) = x := by
  rw [frameLattice, Submodule.mem_span_range_iff_exists_fun]
  refine exists_congr fun a => ?_
  have : (g : Matrix ι ι K) *ᵥ (fun i => algebraMap A K (a i)) =
      ∑ i, a i • (g : Matrix ι ι K).col i := by
    ext j
    simp [Matrix.mulVec, dotProduct, Algebra.smul_def, mul_comm]
  rw [this]
theorem mem_frameLattice_iff_inv (g : GL ι K) (x : ι → K) :
    x ∈ frameLattice A g ↔
      ∀ i, (((g⁻¹ : GL ι K) : Matrix ι ι K) *ᵥ x) i ∈ (1 : Submodule A K) := by
  rw [mem_frameLattice_iff]
  constructor
  · rintro ⟨a, rfl⟩ i
    rw [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
    exact Submodule.mem_one.2 ⟨a i, rfl⟩
  · intro h
    simp only [Submodule.mem_one] at h
    choose a ha using h
    refine ⟨a, ?_⟩
    rw [funext ha, Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
instance isLattice_frameLattice (g : GL ι K) : Submodule.IsLattice K (frameLattice A g) where
  fg := Submodule.fg_span (Set.finite_range _)
  span_eq_top := by
    rw [frameLattice, Submodule.span_span_of_tower, eq_top_iff]
    intro x _
    exact (mem_frameLattice_iff_inv (A := K) g x).2 fun i => Submodule.mem_one.2 ⟨_, rfl⟩
theorem exists_eq_frameLattice [IsDomain A] [IsPrincipalIdealRing A] [IsFractionRing A K]
    (M : Submodule A (ι → K)) [Submodule.IsLattice K M] : ∃ g : GL ι K, M = frameLattice A g := by
  have hcard : Fintype.card (Module.Free.ChooseBasisIndex A M) = Fintype.card ι := by
    rw [← Module.finrank_eq_card_chooseBasisIndex, Submodule.IsLattice.finrank_of_pi K M]
  let b : Module.Basis ι A M := (Module.Free.chooseBasis A M).reindex (Fintype.equivOfCardEq hcard)
  let c : Module.Basis ι K (ι → K) := b.extendOfIsLattice K
  let := (Pi.basisFun K ι).invertibleToMatrix c
  refine ⟨unitOfInvertible ((Pi.basisFun K ι).toMatrix c), ?_⟩
  have hc : ((Pi.basisFun K ι).toMatrix c).col = fun i => M.subtype (b i) := by
    ext i j
    simp [Module.Basis.toMatrix_apply, c]
  rw [frameLattice, val_unitOfInvertible, hc]
  change M = Submodule.span A (Set.range (M.subtype ∘ b))
  rw [Set.range_comp, ← Submodule.map_span, b.span_eq, Submodule.map_subtype_top]
end Frame
section Dual
variable (A : Type*) {K : Type*} [CommRing A] [Field K] [Algebra A K]
  {V W : Type*} [AddCommGroup V] [Module K V] [Module A V] [IsScalarTower A K V]
  [AddCommGroup W] [Module K W] {σ : K →+* K}
def sesqDual (B : V →ₗ[K] W →ₛₗ[σ] K) (s : Set W) : Submodule A V where
  carrier := {x | ∀ y ∈ s, B x y ∈ (1 : Submodule A K)}
  add_mem' hx hx' y hy := by
    rw [map_add, LinearMap.add_apply]; exact add_mem (hx y hy) (hx' y hy)
  zero_mem' y _ := by simp
  smul_mem' a x hx y hy := by
    rw [← algebraMap_smul K a x, map_smul, LinearMap.smul_apply, algebraMap_smul]
    exact Submodule.smul_mem _ a (hx y hy)
variable {A}
end Dual
section LocalDual
variable {O K : Type*} [CommRing O] [IsDedekindDomain O] [Field K] [Algebra O K]
  [IsFractionRing O K]
  {V W : Type*} [AddCommGroup V] [Module K V] [Module O V] [IsScalarTower O K V]
  [AddCommGroup W] [Module K W] [Module O W] [IsScalarTower O K W]
theorem mem_one_localRing (v : HeightOneSpectrum O) (x : K) :
    x ∈ (1 : Submodule (v.valuationSubringAtPrime K) K) ↔ x ∈ v.valuationSubringAtPrime K :=
  Submodule.mem_one.trans ⟨fun ⟨a, ha⟩ => ha ▸ a.2, fun h => ⟨⟨x, h⟩, rfl⟩⟩
end LocalDual
section Completion
variable {O K : Type*} [CommRing O] [IsDedekindDomain O] [Field K] [Algebra O K]
  [IsFractionRing O K] {ι : Type*} (v : HeightOneSpectrum O)
def toCompletion : (ι → K) →ₗ[K] (ι → v.adicCompletion K) :=
  (Algebra.linearMap K (v.adicCompletion K)).compLeft ι
@[simp] theorem toCompletion_apply (x : ι → K) (i : ι) :
    toCompletion v x i = algebraMap K (v.adicCompletion K) (x i) := rfl
theorem algebraMap_mem_adicCompletionIntegers_iff (x : K) :
    algebraMap K (v.adicCompletion K) x ∈ v.adicCompletionIntegers K ↔
      x ∈ v.valuationSubringAtPrime K := by
  rw [mem_localRing_iff_valuation, mem_adicCompletionIntegers,
    ← valuedAdicCompletion_eq_valuation' v x]
  rfl
theorem exists_sub_mem_adicCompletionIntegers (y : v.adicCompletion K) :
    ∃ x : K, y - algebraMap K (v.adicCompletion K) x ∈ v.adicCompletionIntegers K := by
  have ho : IsOpen {z : v.adicCompletion K | y - z ∈ v.adicCompletionIntegers K} :=
    (Valued.isOpen_valuationSubring (v.adicCompletion K)).preimage (by fun_prop)
  exact (denseRange_algebraMap K v).exists_mem_open ho ⟨y, by simp⟩
def complete (M : Submodule (v.valuationSubringAtPrime K) (ι → K)) :
    Submodule (v.adicCompletionIntegers K) (ι → v.adicCompletion K) :=
  Submodule.span _ (toCompletion v '' (M : Set (ι → K)))
def rationalPart (N : Submodule (v.adicCompletionIntegers K) (ι → v.adicCompletion K)) :
    Submodule (v.valuationSubringAtPrime K) (ι → K) where
  carrier := {x | toCompletion v x ∈ N}
  add_mem' hx hy := by
    simp only [Set.mem_ofPred_eq, map_add] at *; exact add_mem hx hy
  zero_mem' := by simp
  smul_mem' a x hx := by
    have := N.smul_mem ⟨_, (algebraMap_mem_adicCompletionIntegers_iff v (a : K)).2 a.2⟩ hx
    have h : toCompletion v (a • x) = (⟨_, (algebraMap_mem_adicCompletionIntegers_iff v
        (a : K)).2 a.2⟩ : v.adicCompletionIntegers K) • toCompletion v x :=
      funext fun i => map_mul (algebraMap K (v.adicCompletion K)) (a : K) (x i)
    exact (show toCompletion v (a • x) ∈ N from h ▸ this)
theorem mem_rationalPart {N : Submodule (v.adicCompletionIntegers K) (ι → v.adicCompletion K)}
    {x : ι → K} : x ∈ rationalPart v N ↔ toCompletion v x ∈ N := Iff.rfl
theorem complete_le_iff {M : Submodule (v.valuationSubringAtPrime K) (ι → K)}
    {N : Submodule (v.adicCompletionIntegers K) (ι → v.adicCompletion K)} :
    complete v M ≤ N ↔ M ≤ rationalPart v N := by
  rw [complete, Submodule.span_le, Set.image_subset_iff]; rfl
theorem complete_span (s : Set (ι → K)) :
    complete v (Submodule.span (v.valuationSubringAtPrime K) s) =
      Submodule.span _ (toCompletion v '' s) := by
  refine le_antisymm ((complete_le_iff v).2 (Submodule.span_le.2 fun x hx => ?_))
    (Submodule.span_mono (Set.image_mono Submodule.subset_span))
  exact Submodule.subset_span ⟨x, hx, rfl⟩
variable [Fintype ι] [DecidableEq ι]
theorem toCompletion_mulVec (g : Matrix ι ι K) (x : ι → K) :
    toCompletion v (g *ᵥ x) = g.map (algebraMap K (v.adicCompletion K)) *ᵥ toCompletion v x := by
  ext1 i
  exact RingHom.map_mulVec (algebraMap K (v.adicCompletion K)) g x i
theorem complete_frameLattice (g : GL ι K) :
    complete v (frameLattice (v.valuationSubringAtPrime K) g) =
      frameLattice (v.adicCompletionIntegers K)
        (Matrix.GeneralLinearGroup.map (algebraMap K (v.adicCompletion K)) g) := by
  rw [frameLattice, complete_span, ← Set.range_comp]
  rfl
theorem rationalPart_frameLattice (g : GL ι K) :
    rationalPart v (frameLattice (v.adicCompletionIntegers K)
        (Matrix.GeneralLinearGroup.map (algebraMap K (v.adicCompletion K)) g)) =
      frameLattice (v.valuationSubringAtPrime K) g := by
  ext x
  rw [mem_rationalPart, mem_frameLattice_iff_inv, mem_frameLattice_iff_inv, ← map_inv]
  refine forall_congr' fun i => ?_
  rw [mem_one_localRing, ← algebraMap_mem_adicCompletionIntegers_iff, ← toCompletion_apply,
    toCompletion_mulVec]
  exact Submodule.mem_one.trans ⟨fun ⟨a, ha⟩ => by
    have := a.2; exact ha ▸ this, fun h => ⟨⟨_, h⟩, rfl⟩⟩
instance isLattice_complete (M : Submodule (v.valuationSubringAtPrime K) (ι → K))
    [Submodule.IsLattice K M] : Submodule.IsLattice (v.adicCompletion K) (complete v M) := by
  obtain ⟨g, rfl⟩ := exists_eq_frameLattice M
  rw [complete_frameLattice]
  infer_instance
theorem rationalPart_complete (M : Submodule (v.valuationSubringAtPrime K) (ι → K))
    [Submodule.IsLattice K M] : rationalPart v (complete v M) = M := by
  obtain ⟨g, rfl⟩ := exists_eq_frameLattice M
  rw [complete_frameLattice, rationalPart_frameLattice]
omit [Fintype ι] [DecidableEq ι] in

theorem exists_smul_mem_completion
    {N : Submodule (v.adicCompletionIntegers K) (ι → v.adicCompletion K)}
    (hN : Submodule.span (v.adicCompletion K) (N : Set (ι → v.adicCompletion K)) = ⊤)
    (y : ι → v.adicCompletion K) : ∃ d ∈ O⁰, d • y ∈ N := by
  obtain ⟨c, hc, hcy⟩ := exists_smul_mem (O := v.adicCompletionIntegers K) hN y
  have hc0 : (c : v.adicCompletion K) ≠ 0 := fun h => nonZeroDivisors.ne_zero hc (Subtype.ext h)
  obtain ⟨d, hd, h⟩ := adicCompletion.mul_nonZeroDivisor_mem_adicCompletionIntegers v
    (c : v.adicCompletion K)⁻¹
  refine ⟨d, hd, ?_⟩
  have : d • y = (⟨_, h⟩ : v.adicCompletionIntegers K) • c • y := by
    change _ = ((c : v.adicCompletion K)⁻¹ * algebraMap O (v.adicCompletion K) d) •
      (c : v.adicCompletion K) • y
    rw [smul_smul, mul_right_comm, inv_mul_cancel₀ hc0, one_mul, algebraMap_smul]
  rw [this]
  exact N.smul_mem _ hcy
omit [Fintype ι] [DecidableEq ι] in
theorem exists_smul_le_completion
    {N N' : Submodule (v.adicCompletionIntegers K) (ι → v.adicCompletion K)} (hN : N.FG)
    (hN' : Submodule.span (v.adicCompletion K) (N' : Set (ι → v.adicCompletion K)) = ⊤) :
    ∃ d ∈ O⁰, ∀ y ∈ N, d • y ∈ N' := by
  obtain ⟨s, rfl⟩ := hN
  obtain ⟨d, hd, h⟩ := exists_mem_submonoid_forall s.finite_toSet O⁰ (fun y d => d • y ∈ N')
    (fun w s t h => by rw [mul_smul]; exact N'.smul_of_tower_mem t h)
    (fun y _ => exists_smul_mem_completion v hN' y)
  refine ⟨d, hd, fun x hx => ?_⟩
  induction hx using Submodule.span_induction with
  | mem x hx => exact h x hx
  | zero => simp
  | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
  | smul a x _ hx => rw [smul_comm]; exact N'.smul_mem a hx
instance isLattice_rationalPart
    (N : Submodule (v.adicCompletionIntegers K) (ι → v.adicCompletion K))
    [hN : Submodule.IsLattice (v.adicCompletion K) N] :
    Submodule.IsLattice K (rationalPart v N) := by
  let M := frameLattice (v.valuationSubringAtPrime K) (1 : GL ι K)
  have hM : Submodule.IsLattice K M := isLattice_frameLattice _
  constructor
  · obtain ⟨d, hd, h⟩ := exists_smul_le_completion v hN.fg (isLattice_complete v M).span_eq_top
    refine fg_of_smul_mem (K := K) hM.fg hd fun x hx => ?_
    rw [← rationalPart_complete v M, mem_rationalPart, LinearMap.map_smul_of_tower]
    exact h _ hx
  · obtain ⟨d, hd, h⟩ := exists_smul_le_completion v (isLattice_complete v M).fg hN.span_eq_top
    refine span_eq_top_of_smul_mem hM.span_eq_top hd fun x hx => ?_
    rw [mem_rationalPart, LinearMap.map_smul_of_tower]
    exact h _ (Submodule.subset_span ⟨x, hx, rfl⟩)
theorem complete_rationalPart_of_span_eq_top
    {N : Submodule (v.adicCompletionIntegers K) (ι → v.adicCompletion K)}
    (hN : Submodule.span (v.adicCompletion K) (N : Set (ι → v.adicCompletion K)) = ⊤) :
    complete v (rationalPart v N) = N := by
  refine le_antisymm ((complete_le_iff v).2 le_rfl) fun y hy => ?_
  let M := frameLattice (v.valuationSubringAtPrime K) (1 : GL ι K)
  have hM : Submodule.IsLattice K M := isLattice_frameLattice _
  obtain ⟨d, hd, h⟩ := exists_smul_le_completion v (isLattice_complete v M).fg hN

  have hstd : ∀ z ∈ complete v M, d • z ∈ complete v (rationalPart v N) := by
    intro z hz
    induction hz using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨x, hx, rfl⟩ := hz
      rw [← LinearMap.map_smul_of_tower]
      refine Submodule.subset_span ⟨_, ?_, rfl⟩
      rw [SetLike.mem_coe, mem_rationalPart, LinearMap.map_smul_of_tower]
      exact h _ (Submodule.subset_span ⟨x, hx, rfl⟩)
    | zero => simp
    | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
    | smul a x _ hx => rw [smul_comm]; exact Submodule.smul_mem _ a hx
  have hd' : algebraMap O K d ≠ 0 := by simpa using nonZeroDivisors.ne_zero hd
  choose x hx using fun i => exists_sub_mem_adicCompletionIntegers v
    (((algebraMap O K d)⁻¹ • y) i)
  have hz : (algebraMap O K d)⁻¹ • y - toCompletion v x ∈ complete v M := by
    rw [complete_frameLattice, mem_frameLattice_iff_inv]
    intro i
    simp only [map_one, inv_one, Units.val_one, Matrix.one_mulVec]
    exact Submodule.mem_one.2 ⟨⟨_, hx i⟩, rfl⟩
  have hy' : y = d • ((algebraMap O K d)⁻¹ • y - toCompletion v x) + toCompletion v (d • x) := by
    rw [LinearMap.map_smul_of_tower, ← smul_add, sub_add_cancel, ← algebraMap_smul K d, smul_smul,
      mul_inv_cancel₀ hd', one_smul]
  have hxN : d • x ∈ rationalPart v N := by
    rw [mem_rationalPart, ← sub_eq_iff_eq_add'.2 hy']
    exact sub_mem hy (h _ hz)
  rw [hy']
  exact add_mem (hstd _ hz) (Submodule.subset_span ⟨_, hxN, rfl⟩)
theorem complete_rationalPart
    (N : Submodule (v.adicCompletionIntegers K) (ι → v.adicCompletion K))
    [hN : Submodule.IsLattice (v.adicCompletion K) N] : complete v (rationalPart v N) = N :=
  complete_rationalPart_of_span_eq_top v hN.span_eq_top
def latticeOrderIsoCompletion :
    {M : Submodule (v.valuationSubringAtPrime K) (ι → K) // Submodule.IsLattice K M} ≃o
      {N : Submodule (v.adicCompletionIntegers K) (ι → v.adicCompletion K) //
        Submodule.IsLattice (v.adicCompletion K) N} where
  toFun M := haveI := M.2; ⟨complete v M.1, isLattice_complete v _⟩
  invFun N := haveI := N.2; ⟨rationalPart v N.1, isLattice_rationalPart v _⟩
  left_inv M := haveI := M.2; Subtype.ext (rationalPart_complete v M.1)
  right_inv N := haveI := N.2; Subtype.ext (complete_rationalPart v N.1)
  map_rel_iff' {M M'} := by
    have := M'.2
    change complete v M.1 ≤ complete v M'.1 ↔ M.1 ≤ M'.1
    rw [complete_le_iff, rationalPart_complete]
variable {v}
end Completion
section NumberField
open NumberField
open ReciprocityTheory.ChartRestriction.G.FD
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
def conjPlace (v : HeightOneSpectrum (𝓞 E)) : HeightOneSpectrum (𝓞 E) :=
  v.comap (IsCMField.ringOfIntegersComplexConj E : 𝓞 E →+* 𝓞 E)
    (IsCMField.ringOfIntegersComplexConj E).surjective
def hermPairing (G : Matrix (Fin r) (Fin r) E) :
    (Fin r → E) →ₗ[E] (Fin r → E) →ₛₗ[(IsCMField.complexConj E : E →+* E)] E :=
  LinearMap.mk₂'ₛₗ (RingHom.id E) (IsCMField.complexConj E : E →+* E) (herm G)
    (fun x y z => by simp [herm, add_mul, Finset.sum_add_distrib])
    (fun c x y => by simp [herm, Finset.mul_sum, mul_assoc])
    (fun x y z => by simp [herm, cc, mul_add, Finset.sum_add_distrib])
    (fun c x y => by simp [herm, cc, Finset.mul_sum, mul_left_comm])
end NumberField
end GlobalTheory.LocalLattice
namespace GlobalTheory
open LocalLattice
end GlobalTheory


