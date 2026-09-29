-- Prove2me | solution 1 for AutomorphicForm.IsArchTestFactor.exists_contDiff_hasCompactSupport_tsupport_subset_isUnit_det
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/e0796d6a-b189-5cb3-9661-e4891b9404da

import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_IsArchTestFactor_exists_contDiff_hasCompactSupport_tsupport_subset_isUnit_det

set_option autoImplicit false

open NumberField

namespace MixedEntryDensity

variable (F : Type) [Field F]

open scoped Classical in
private theorem continuous_ringEquiv_mixedSpace : Continuous (InfiniteAdeleRing.ringEquiv_mixedSpace F) := by
  change Continuous fun x : InfiniteAdeleRing F => InfiniteAdeleRing.ringEquiv_mixedSpace F x
  simp only [InfiniteAdeleRing.ringEquiv_mixedSpace_apply]
  refine Continuous.prodMk (continuous_pi fun v => ?_) (continuous_pi fun v => ?_)
  · exact (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal v.2).continuous.comp (continuous_apply _)
  · exact (InfinitePlace.Completion.isometry_extensionEmbedding v.1).continuous.comp (continuous_apply _)

open scoped Classical in
private theorem continuous_archEntries : Continuous (AutomorphicForm.archEntries F) := by
  have hval : Continuous fun g : GL (Fin 2) (InfiniteAdeleRing F) =>
      (g : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) := Units.continuous_val
  refine continuous_pi fun i => continuous_pi fun j => ?_
  exact (continuous_ringEquiv_mixedSpace F).comp (hval.matrix_elem i j)

open scoped Classical in
private theorem of_archEntries (g : GL (Fin 2) (InfiniteAdeleRing F)) :
    Matrix.of (AutomorphicForm.archEntries F g) =
      (InfiniteAdeleRing.ringEquiv_mixedSpace F : InfiniteAdeleRing F →+* mixedEmbedding.mixedSpace F).mapMatrix
        (g : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) :=
  Matrix.ext fun _ _ => rfl

open scoped Classical in

private theorem isUnit_det_of_archEntries (g : GL (Fin 2) (InfiniteAdeleRing F)) :
    IsUnit (Matrix.det (Matrix.of (AutomorphicForm.archEntries F g))) := by
  rw [of_archEntries, ← RingHom.map_det]
  exact ((Matrix.isUnit_iff_isUnit_det _).mp g.isUnit).map _

open scoped Classical in

private theorem exists_archEntries_eq (E : Fin 2 → Fin 2 → mixedEmbedding.mixedSpace F)
    (hE : IsUnit (Matrix.det (Matrix.of E))) :
    ∃ g : GL (Fin 2) (InfiniteAdeleRing F), AutomorphicForm.archEntries F g = E := by
  set M : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F) :=
    ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm :
      mixedEmbedding.mixedSpace F →+* InfiniteAdeleRing F).mapMatrix (Matrix.of E) with hM
  have hMdet : IsUnit M.det := by
    rw [hM, ← RingHom.map_det]
    exact hE.map _
  obtain ⟨u, hu⟩ := (Matrix.isUnit_iff_isUnit_det M).mpr hMdet
  refine ⟨u, ?_⟩
  funext i j
  rw [AutomorphicForm.archEntries_apply, hu, hM]
  exact (InfiniteAdeleRing.ringEquiv_mixedSpace F).apply_symm_apply (E i j)

private theorem finite_setOf_quadratic_eq_zero {K : Type} [Field K] (s c : K) :
    {t : K | t * t + s * t + c = 0}.Finite := by
  by_cases h : ∃ t₁ : K, t₁ * t₁ + s * t₁ + c = 0
  · obtain ⟨t₁, ht₁⟩ := h
    refine (Set.toFinite ({t₁, -t₁ - s} : Set K)).subset ?_
    intro t ht
    have ht' : t * t + s * t + c = 0 := ht
    have hfac : (t - t₁) * (t - (-t₁ - s)) = 0 := by linear_combination ht' - ht₁
    rcases mul_eq_zero.mp hfac with h0 | h0
    · exact Or.inl (sub_eq_zero.mp h0)
    · exact Or.inr (sub_eq_zero.mp h0)
  · convert Set.finite_empty
    ext t
    exact ⟨fun ht => h ⟨t, ht⟩, fun ht => ht.elim⟩

private theorem isUnit_of_coordinates_ne_zero (x : mixedEmbedding.mixedSpace F)
    (h₁ : ∀ v, x.1 v ≠ 0) (h₂ : ∀ v, x.2 v ≠ 0) : IsUnit x := by
  refine isUnit_iff_exists_inv.mpr ⟨(fun v => (x.1 v)⁻¹, fun v => (x.2 v)⁻¹), ?_⟩
  refine Prod.ext (funext fun v => ?_) (funext fun v => ?_)
  · exact mul_inv_cancel₀ (h₁ v)
  · exact mul_inv_cancel₀ (h₂ v)

private noncomputable def identityEntries : Fin 2 → Fin 2 → mixedEmbedding.mixedSpace F :=
  fun i j => if i = j then 1 else 0

open scoped Classical in
private theorem det_of_add_smul_identityEntries (E : Fin 2 → Fin 2 → mixedEmbedding.mixedSpace F) (t : ℝ) :
    Matrix.det (Matrix.of (E + t • identityEntries F)) =
      (E 0 0 + t • (1 : mixedEmbedding.mixedSpace F)) * (E 1 1 + t • (1 : mixedEmbedding.mixedSpace F)) -
        E 0 1 * E 1 0 := by
  simp [Matrix.det_fin_two, identityEntries]

open scoped Classical in

private theorem fst_det_add_smul (E : Fin 2 → Fin 2 → mixedEmbedding.mixedSpace F) (t : ℝ)
    (v : {w : InfinitePlace F // w.IsReal}) :
    (Matrix.det (Matrix.of (E + t • identityEntries F))).1 v =
      t * t + ((E 0 0).1 v + (E 1 1).1 v) * t + ((E 0 0).1 v * (E 1 1).1 v - (E 0 1).1 v * (E 1 0).1 v) := by
  rw [det_of_add_smul_identityEntries]
  simp only [Prod.fst_sub, Prod.fst_mul, Prod.fst_add, Prod.smul_fst, Prod.fst_one, Pi.sub_apply, Pi.mul_apply,
    Pi.add_apply, Pi.smul_apply, Pi.one_apply, smul_eq_mul, mul_one]
  ring

open scoped Classical in

private theorem snd_det_add_smul (E : Fin 2 → Fin 2 → mixedEmbedding.mixedSpace F) (t : ℝ)
    (v : {w : InfinitePlace F // w.IsComplex}) :
    (Matrix.det (Matrix.of (E + t • identityEntries F))).2 v =
      (t : ℂ) * t + ((E 0 0).2 v + (E 1 1).2 v) * t + ((E 0 0).2 v * (E 1 1).2 v - (E 0 1).2 v * (E 1 0).2 v) := by
  rw [det_of_add_smul_identityEntries]
  simp only [Prod.snd_sub, Prod.snd_mul, Prod.snd_add, Prod.smul_snd, Prod.snd_one, Pi.sub_apply, Pi.mul_apply,
    Pi.add_apply, Pi.smul_apply, Pi.one_apply, Complex.real_smul, mul_one]
  ring

variable [NumberField F]

open scoped Classical in

private theorem finite_badParameters (E : Fin 2 → Fin 2 → mixedEmbedding.mixedSpace F) :
    {t : ℝ | ¬ IsUnit (Matrix.det (Matrix.of (E + t • identityEntries F)))}.Finite := by
  have hreal : ∀ v : {w : InfinitePlace F // w.IsReal},
      {t : ℝ | (Matrix.det (Matrix.of (E + t • identityEntries F))).1 v = 0}.Finite := fun v => by
    refine (finite_setOf_quadratic_eq_zero ((E 0 0).1 v + (E 1 1).1 v)
      ((E 0 0).1 v * (E 1 1).1 v - (E 0 1).1 v * (E 1 0).1 v)).subset ?_
    intro t ht
    have ht' := ht
    simp only [Set.mem_setOf_eq] at ht' ⊢
    rwa [fst_det_add_smul] at ht'
  have hcomplex : ∀ v : {w : InfinitePlace F // w.IsComplex},
      {t : ℝ | (Matrix.det (Matrix.of (E + t • identityEntries F))).2 v = 0}.Finite := fun v => by
    have hfin := finite_setOf_quadratic_eq_zero ((E 0 0).2 v + (E 1 1).2 v)
      ((E 0 0).2 v * (E 1 1).2 v - (E 0 1).2 v * (E 1 0).2 v)
    refine (hfin.preimage (Complex.ofReal_injective.injOn)).subset ?_
    intro t ht
    simp only [Set.mem_setOf_eq] at ht
    simp only [Set.mem_preimage, Set.mem_setOf_eq]
    rwa [snd_det_add_smul] at ht
  refine ((Set.finite_iUnion hreal).union (Set.finite_iUnion hcomplex)).subset ?_
  intro t ht
  simp only [Set.mem_setOf_eq] at ht
  by_contra hnot
  simp only [Set.mem_union, Set.mem_iUnion, Set.mem_setOf_eq, not_or, not_exists] at hnot
  exact ht (isUnit_of_coordinates_ne_zero F _ hnot.1 hnot.2)

open scoped Classical in

private theorem dense_isUnit_det :
    Dense {E : Fin 2 → Fin 2 → mixedEmbedding.mixedSpace F | IsUnit (Matrix.det (Matrix.of E))} := by
  intro E
  rw [mem_closure_iff_seq_limit]
  have hbad := finite_badParameters F E
  have hpick : ∀ n : ℕ, ∃ t : ℝ, t ∈ Set.Ioo (0 : ℝ) (1 / ((n : ℝ) + 1)) ∧
      IsUnit (Matrix.det (Matrix.of (E + t • identityEntries F))) := fun n => by
    have hpos : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    obtain ⟨t, ht, htgood⟩ := Set.Infinite.exists_notMem_finite (Set.Ioo_infinite hpos) hbad
    exact ⟨t, ht, not_not.mp htgood⟩
  choose t ht htgood using hpick
  refine ⟨fun n => E + t n • identityEntries F, fun n => htgood n, ?_⟩
  have ht0 : Filter.Tendsto t Filter.atTop (nhds 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds tendsto_one_div_add_atTop_nhds_zero_nat
      (fun n => (ht n).1.le) (fun n => (ht n).2.le)
  have hcont : Filter.Tendsto (fun s : ℝ => E + s • identityEntries F) (nhds 0) (nhds E) := by
    have h : Continuous fun s : ℝ => E + s • identityEntries F :=
      continuous_const.add (continuous_id.smul continuous_const)
    simpa using h.tendsto 0
  exact hcont.comp ht0

end MixedEntryDensity

open scoped Classical in
open AutomorphicForm in

theorem solution
    (F : Type) [Field F] [NumberField F] {fa : GL (Fin 2) (InfiniteAdeleRing F) → ℂ}
    (hfa : IsArchTestFactor F fa) :
    ∃ Φ : (Fin 2 → Fin 2 → mixedEmbedding.mixedSpace F) → ℂ,
      ContDiff ℝ (⊤ : ℕ∞) Φ ∧ HasCompactSupport Φ ∧
        tsupport Φ ⊆ {E | IsUnit (Matrix.det (Matrix.of E))} ∧ ∀ g, fa g = Φ (archEntries F g) := by
  obtain ⟨⟨Φ, hΦ, hΦfa⟩, hc⟩ := hfa
  set S : Set (Fin 2 → Fin 2 → mixedEmbedding.mixedSpace F) := AutomorphicForm.archEntries F '' tsupport fa with hS
  have hScompact : IsCompact S := hc.image (MixedEntryDensity.continuous_archEntries F)
  have hSlocus : S ⊆ {E | IsUnit (Matrix.det (Matrix.of E))} := by
    rintro _ ⟨g, -, rfl⟩
    exact MixedEntryDensity.isUnit_det_of_archEntries F g
  have hsupp : Function.support Φ ⊆ S := by
    intro E hE
    by_contra hES
    have hopen : IsOpen (Sᶜ ∩ Function.support Φ) :=
      hScompact.isClosed.isOpen_compl.inter (hΦ.continuous.isOpen_support)
    obtain ⟨E', hE'locus, hE'S, hE'supp⟩ :=
      (MixedEntryDensity.dense_isUnit_det F).exists_mem_open hopen ⟨E, hES, hE⟩
    obtain ⟨g, rfl⟩ := MixedEntryDensity.exists_archEntries_eq F E' hE'locus
    apply hE'S
    refine ⟨g, ?_, rfl⟩
    apply subset_tsupport
    rw [Function.mem_support, hΦfa]
    exact hE'supp
  have htsupp : tsupport Φ ⊆ S := closure_minimal hsupp hScompact.isClosed
  exact ⟨Φ, hΦ, hScompact.of_isClosed_subset (isClosed_tsupport Φ) htsupp, htsupp.trans hSlocus, hΦfa⟩

end S_AutomorphicForm_IsArchTestFactor_exists_contDiff_hasCompactSupport_tsupport_subset_isUnit_det
end P2MW
export P2MW.S_AutomorphicForm_IsArchTestFactor_exists_contDiff_hasCompactSupport_tsupport_subset_isUnit_det (solution)
