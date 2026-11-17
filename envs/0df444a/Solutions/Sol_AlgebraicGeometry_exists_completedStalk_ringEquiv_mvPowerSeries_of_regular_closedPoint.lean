-- Prove2me | solution 1 for AlgebraicGeometry.exists_completedStalk_ringEquiv_mvPowerSeries_of_regular_closedPoint
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-11-16T17:16:43.879307+00:00
-- url     : https://prove2.me/submissions/cbd43707-581c-4ceb-8593-e33a60ab038b

import Mathlib

universe u v w

section

set_option autoImplicit false
set_option maxHeartbeats 900000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
noncomputable section

open IsLocalRing

namespace PhilipponCompleteLocalPowerSeriesPresentation

variable (K : Type u) [CommRing K] (A : Type v) [CommRing A] [Algebra K A]

/-- Evaluate a finite set of formal parameters in a complete adic algebra.
The coefficients may lie in a separate universe. -/
theorem exists_map (I : Ideal A) [IsAdicComplete I A]
    {σ : Type w} [Finite σ] (a : σ → A) (ha : ∀ i, a i ∈ I) :
    ∃ f : MvPowerSeries σ K →+* A,
      (∀ c : K, f (MvPowerSeries.C c) = algebraMap K A c) ∧
      (∀ i : σ, f (MvPowerSeries.X i) = a i) := by
  letI : UniformSpace K := ⊥
  letI : WithIdeal A := ⟨I⟩
  have hcomplete : CompleteSpace A ∧ T2Space A :=
    (IsAdic.isAdicComplete_iff (I := I) rfl).mp inferInstance
  letI : CompleteSpace A := hcomplete.1
  letI : T2Space A := hcomplete.2
  have hcont : Continuous (algebraMap K A) := continuous_of_discreteTopology
  have heval : MvPowerSeries.HasEval a := by
    constructor
    · intro i
      exact WithIdeal.isTopologicallyNilpotent_of_mem (ha i)
    · simp only [Filter.cofinite_eq_bot]
      exact Filter.tendsto_bot
  refine ⟨MvPowerSeries.eval₂Hom hcont heval, ?_, ?_⟩
  · intro c
    simp [MvPowerSeries.coe_eval₂Hom]
  · intro i
    simp [MvPowerSeries.coe_eval₂Hom]

/-- Parameters generating the maximal ideal give a surjection whenever
the coefficient map is surjective on the residue field. -/
theorem surjective [IsLocalRing A] [IsAdicComplete (maximalIdeal A) A]
    (hres : Function.Surjective ((residue A).comp (algebraMap K A)))
    {σ : Type w} [Finite σ] (a : σ → A)
    (ha : Ideal.span (Set.range a) = maximalIdeal A)
    (f : MvPowerSeries σ K →+* A)
    (hC : ∀ c : K, f (MvPowerSeries.C c) = algebraMap K A c)
    (hX : ∀ i : σ, f (MvPowerSeries.X i) = a i) :
    Function.Surjective f := by
  let J : Ideal (MvPowerSeries σ K) := Ideal.span (Set.range MvPowerSeries.X)
  have hmap : J.map f = maximalIdeal A := by
    change (Ideal.span (Set.range MvPowerSeries.X)).map f = _
    rw [Ideal.map_span, ← Set.range_comp]
    simpa only [Function.comp_def, hX] using ha
  letI : IsHausdorff (J.map f) A := hmap ▸ inferInstance
  apply surjective_of_mk_map_comp_surjective (I := J) f
  intro q
  obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective q
  obtain ⟨c, hc⟩ := hres (residue A z)
  refine ⟨MvPowerSeries.C c, ?_⟩
  change Ideal.Quotient.mk (J.map f) (f (MvPowerSeries.C c)) =
    Ideal.Quotient.mk (J.map f) z
  rw [hC, Ideal.Quotient.eq, hmap]
  exact Ideal.Quotient.eq.mp hc

theorem exists_surjective [IsLocalRing A] [IsAdicComplete (maximalIdeal A) A]
    (hres : Function.Surjective ((residue A).comp (algebraMap K A)))
    {σ : Type w} [Finite σ] (a : σ → A)
    (ha : Ideal.span (Set.range a) = maximalIdeal A) :
    ∃ f : MvPowerSeries σ K →ₐ[K] A,
      Function.Surjective f ∧ ∀ i : σ, f (MvPowerSeries.X i) = a i := by
  obtain ⟨f, hC, hX⟩ := exists_map K A (maximalIdeal A) a
    (fun i => ha ▸ Ideal.subset_span (Set.mem_range_self i))
  let φ : MvPowerSeries σ K →ₐ[K] A := { f with commutes' := hC }
  exact ⟨φ, surjective K A hres a ha f hC hX, hX⟩

end PhilipponCompleteLocalPowerSeriesPresentation

end
end

section

set_option autoImplicit false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false
noncomputable section

open IsLocalRing

namespace PhilipponPowerSeriesRegularity

/-- A power series variable preserves regularity of a Noetherian local ring. -/
theorem powerSeries (R : Type*) [CommRing R] [IsRegularLocalRing R] :
    IsRegularLocalRing (PowerSeries R) := by
  have hX : PowerSeries.X ∈ maximalIdeal (PowerSeries R) := by
    change ¬ IsUnit (PowerSeries.X : PowerSeries R)
    rw [PowerSeries.isUnit_iff_constantCoeff, PowerSeries.constantCoeff_X]
    exact not_isUnit_zero
  have hgen := PowerSeries.spanFinrank_le_spanFinrank_map_constantCoeff_add_one_of_X_mem hX
  have hmap : (maximalIdeal (PowerSeries R)).map (PowerSeries.constantCoeff : PowerSeries R →+* R) =
      maximalIdeal R := map_maximalIdeal_of_surjective (R := PowerSeries R) (S := R)
        (PowerSeries.constantCoeff (R := R)) PowerSeries.constantCoeff_surj
  rw [hmap] at hgen
  apply IsRegularLocalRing.of_spanFinrank_maximalIdeal_le (PowerSeries R)
  calc ((maximalIdeal (PowerSeries R)).spanFinrank : WithBot ℕ∞)
      ≤ (((maximalIdeal R).spanFinrank + 1 : ℕ) : WithBot ℕ∞) := by exact_mod_cast hgen
    _ = ringKrullDim R + 1 := by
      push_cast
      rw [IsRegularLocalRing.spanFinrank_maximalIdeal]
    _ ≤ ringKrullDim (PowerSeries R) := ringKrullDim_succ_le_ringKrullDim_powerseries

theorem fin (R : Type*) [CommRing R] [IsRegularLocalRing R] (n : ℕ) :
    IsRegularLocalRing (MvPowerSeries (Fin n) R) := by
  induction n with
  | zero =>
      exact IsRegularLocalRing.of_ringEquiv (MvPowerSeries.isEmptyEquiv (Fin 0) R).toRingEquiv.symm
  | succ n ih =>
      letI := ih
      letI := powerSeries (MvPowerSeries (Fin n) R)
      exact IsRegularLocalRing.of_ringEquiv (MvPowerSeries.finSuccEquiv R n).toRingEquiv.symm

/-- The formal regular local models needed for completed nodal charts. -/
theorem mvPowerSeries (R : Type*) [CommRing R] [IsRegularLocalRing R]
    (σ : Type*) [Finite σ] : IsRegularLocalRing (MvPowerSeries σ R) := by
  classical
  letI := Fintype.ofFinite σ
  letI := fin R (Fintype.card σ)
  exact IsRegularLocalRing.of_ringEquiv
    (MvPowerSeries.renameEquiv R (Fintype.equivFin σ)).toRingEquiv.symm

end PhilipponPowerSeriesRegularity

end
end

section

set_option autoImplicit false
set_option maxHeartbeats 900000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

namespace PhilipponMultiplicity.Chardin
open MvPowerSeries

/-- The residue ideal of a power-series ring in finitely many variables is
the ideal of its parameters. This connects constant coefficients with the
existing adic-completeness theorem. -/
theorem powerSeries_constantCoeff_ker (σ R : Type*) [Finite σ] [CommRing R] :
    RingHom.ker (constantCoeff : MvPowerSeries σ R →+* R) =
      Ideal.span (Set.range X) := by
  let I := MvPolynomial.idealOfVars σ R
  let e := toAdicCompletionAlgEquiv σ R
  have hmap : Ideal.map e.toRingEquiv (Ideal.span (Set.range X)) =
      I.map (algebraMap (MvPolynomial σ R) (AdicCompletion I (MvPolynomial σ R))) := by
    change Ideal.map e.toRingEquiv (Ideal.span (Set.range X)) =
      Ideal.map _ (Ideal.span (Set.range MvPolynomial.X))
    simp_rw [Ideal.map_span, ← Set.range_comp]
    congr 2
    ext i
    simp [e, I, AdicCompletion.algebraMap_apply, ← MvPolynomial.coe_X,
      toAdicCompletion_coe]
  have hpre : (RingHom.ker (AdicCompletion.evalOneₐ I).toRingHom).comap e.toRingEquiv =
      Ideal.span (Set.range X) := by
    rw [AdicCompletion.ker_evalOneₐ_eq_map I (MvPolynomial.idealOfVars_fg σ R), ← hmap]
    exact Ideal.comap_map_of_bijective e.toRingEquiv e.bijective
  rw [← hpre]
  ext f
  change constantCoeff f = 0 ↔ AdicCompletion.evalOneₐ I (e f) = 0
  have heval : AdicCompletion.evalOneₐ I (e f) = Ideal.Quotient.mk I (truncTotal 1 f) := rfl
  rw [heval, Ideal.Quotient.eq_zero_iff_mem]
  change constantCoeff f = 0 ↔ truncTotal 1 f ∈ MvPolynomial.idealOfVars σ R
  rw [← pow_one (MvPolynomial.idealOfVars σ R), MvPolynomial.mem_pow_idealOfVars_iff']
  constructor
  · intro hf d hd
    have hd0 : d = 0 := (Finsupp.degree_eq_zero_iff d).mp (by omega)
    subst d
    rw [coeff_truncTotal f (by simp), coeff_zero_eq_constantCoeff]
    exact hf
  · intro hf
    have h := hf 0 (by simp)
    rwa [coeff_truncTotal f (by simp), coeff_zero_eq_constantCoeff] at h

theorem powerSeries_complete_constantCoeff_ker (σ R : Type*) [Finite σ] [CommRing R] :
    IsAdicComplete (RingHom.ker (constantCoeff : MvPowerSeries σ R →+* R))
      (MvPowerSeries σ R) := by
  rw [powerSeries_constantCoeff_ker]
  infer_instance

end PhilipponMultiplicity.Chardin

end
end

section

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
noncomputable section

open IsLocalRing

namespace PhilipponCompleteRegularLocalStructure

variable (K : Type u) [Field K]

theorem maximalIdeal_eq_span_X (σ : Type w) [Finite σ] :
    maximalIdeal (MvPowerSeries σ K) = Ideal.span (Set.range MvPowerSeries.X) := by
  rw [← PhilipponMultiplicity.Chardin.powerSeries_constantCoeff_ker σ K]
  ext f
  change (¬ IsUnit f) ↔ MvPowerSeries.constantCoeff f = 0
  simp only [MvPowerSeries.isUnit_iff_constantCoeff, isUnit_iff_ne_zero, not_not]

theorem spanFinrank_maximalIdeal_le_card (σ : Type w) [Finite σ] :
    (maximalIdeal (MvPowerSeries σ K)).spanFinrank ≤ Nat.card σ := by
  rw [maximalIdeal_eq_span_X K σ]
  calc
    (Ideal.span (Set.range (MvPowerSeries.X : σ → MvPowerSeries σ K))).spanFinrank
        ≤ (Set.range (MvPowerSeries.X : σ → MvPowerSeries σ K)).ncard :=
      Submodule.spanFinrank_span_le_ncard_of_finite (Set.finite_range _)
    _ ≤ Nat.card σ := by
      simpa only [Set.image_univ, Set.ncard_univ] using
        (Set.ncard_image_le (s := Set.univ) (f := (MvPowerSeries.X : σ → MvPowerSeries σ K))
          (Set.finite_univ : (Set.univ : Set σ).Finite))

/-- A surjective formal presentation using no more parameters than the
regular target's dimension has zero kernel. This uses that power series
over a field form a domain, rather than a general regular-domain theorem. -/
theorem injective_of_surjective
    {A : Type v} [CommRing A] [IsRegularLocalRing A]
    {σ : Type w} [Finite σ] (f : MvPowerSeries σ K →+* A)
    (hf : Function.Surjective f)
    (hcard : Nat.card σ ≤ (maximalIdeal A).spanFinrank) :
    Function.Injective f := by
  letI := PhilipponPowerSeriesRegularity.mvPowerSeries K σ
  apply (RingHom.injective_iff_ker_eq_bot f).mpr
  apply le_antisymm _ bot_le
  intro x hx
  change x = 0
  by_contra hx0
  have hdim := ringKrullDim_succ_le_of_surjective f hf
    (mem_nonZeroDivisors_iff_ne_zero.mpr hx0) hx
  rw [← IsRegularLocalRing.spanFinrank_maximalIdeal (R := A),
    ← IsRegularLocalRing.spanFinrank_maximalIdeal (R := MvPowerSeries σ K)] at hdim
  have hnat : (maximalIdeal A).spanFinrank + 1 ≤
      (maximalIdeal (MvPowerSeries σ K)).spanFinrank := by exact_mod_cast hdim
  have hle := spanFinrank_maximalIdeal_le_card K σ
  omega

variable (A : Type v) [CommRing A] [IsRegularLocalRing A] [Algebra K A]
    [IsAdicComplete (maximalIdeal A) A]

/-- Any chosen minimal generating family of the maximal ideal gives a
coefficient-preserving formal-coordinate isomorphism. -/
theorem equiv_of_generators
    (hres : Function.Surjective ((residue A).comp (algebraMap K A)))
    {σ : Type w} [Finite σ] (a : σ → A)
    (ha : Ideal.span (Set.range a) = maximalIdeal A)
    (hcard : Nat.card σ ≤ (maximalIdeal A).spanFinrank) :
    ∃ e : MvPowerSeries σ K ≃ₐ[K] A, ∀ i : σ, e (MvPowerSeries.X i) = a i := by
  obtain ⟨f, hf, hX⟩ :=
    PhilipponCompleteLocalPowerSeriesPresentation.exists_surjective K A hres a ha
  let e := AlgEquiv.ofBijective f ⟨injective_of_surjective K f.toRingHom hf hcard, hf⟩
  exact ⟨e, hX⟩

/-- The equicharacteristic regular complete-local structure theorem with
an explicitly supplied coefficient field inducing the residue field. -/
theorem exists_fin_equiv
    (hres : Function.Surjective ((residue A).comp (algebraMap K A))) :
    ∃ r : ℕ, Nonempty (MvPowerSeries (Fin r) K ≃ₐ[K] A) := by
  classical
  obtain ⟨s, hcard, hs⟩ :=
    Submodule.FG.exists_span_finset_card_eq_spanFinrank
      (maximalIdeal A).fg_of_isNoetherianRing
  have hs' : Ideal.span (Set.range (fun z : s => (z : A))) = maximalIdeal A := by
    simpa using hs
  have hcard' : Nat.card s ≤ (maximalIdeal A).spanFinrank := by simpa using hcard.le
  obtain ⟨e, _⟩ := equiv_of_generators K A hres (fun z : s => (z : A)) hs' hcard'
  exact ⟨Fintype.card s, ⟨(MvPowerSeries.renameEquiv K (Fintype.equivFin s)).symm.trans e⟩⟩

end PhilipponCompleteRegularLocalStructure

end
end

section

set_option autoImplicit false
set_option maxHeartbeats 350000
set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

namespace PhilipponMultiplicity.NoetherianCompletion

open scoped Topology

variable {R : Type*} [CommRing R]

theorem exists_powerSeriesMap (I : Ideal R) (hI : I.FG)
    {σ : Type*} [Finite σ] (a : σ → R) (ha : ∀ i, a i ∈ I) :
    ∃ f : MvPowerSeries σ R →+* AdicCompletion I R,
      (∀ r : R, f (MvPowerSeries.C r) = algebraMap R (AdicCompletion I R) r) ∧
      (∀ i : σ, f (MvPowerSeries.X i) = algebraMap R (AdicCompletion I R) (a i)) := by
  let S := AdicCompletion I R
  let J := I.map (algebraMap R S)
  letI : UniformSpace R := ⊥
  letI : WithIdeal S := ⟨J⟩
  letI : IsAdicComplete J S := AdicCompletion.isAdicComplete_self I hI
  have hcomplete : CompleteSpace S ∧ T2Space S :=
    (IsAdic.isAdicComplete_iff (I := J) rfl).mp inferInstance
  letI : CompleteSpace S := hcomplete.1
  letI : T2Space S := hcomplete.2
  have hcont : Continuous (algebraMap R S) := continuous_of_discreteTopology
  have heval : MvPowerSeries.HasEval (fun i => algebraMap R S (a i)) := by
    constructor
    · intro i
      exact WithIdeal.isTopologicallyNilpotent_of_mem (Ideal.mem_map_of_mem _ (ha i))
    · simp only [Filter.cofinite_eq_bot]
      exact Filter.tendsto_bot
  refine ⟨MvPowerSeries.eval₂Hom hcont heval, ?_, ?_⟩
  · intro r
    simp [MvPowerSeries.coe_eval₂Hom, S]
  · intro i
    simp [MvPowerSeries.coe_eval₂Hom, S]

theorem powerSeriesMap_surjective (I : Ideal R) (hI : I.FG)
    {σ : Type*} [Finite σ] (a : σ → R)
    (ha : Ideal.span (Set.range a) = I)
    (f : MvPowerSeries σ R →+* AdicCompletion I R)
    (hC : ∀ r : R, f (MvPowerSeries.C r) = algebraMap R (AdicCompletion I R) r)
    (hX : ∀ i : σ, f (MvPowerSeries.X i) = algebraMap R (AdicCompletion I R) (a i)) :
    Function.Surjective f := by
  let S := AdicCompletion I R
  let J : Ideal (MvPowerSeries σ R) := Ideal.span (Set.range MvPowerSeries.X)
  have hmap : J.map f = I.map (algebraMap R S) := by
    change (Ideal.span (Set.range MvPowerSeries.X)).map f = _
    rw [Ideal.map_span, ← Set.range_comp]
    simp only [Function.comp_def, hX]
    simpa only [Ideal.map_span, ← Set.range_comp, Function.comp_def, S] using
      congrArg (Ideal.map (algebraMap R S)) ha
  letI : IsAdicComplete (I.map (algebraMap R S)) S :=
    AdicCompletion.isAdicComplete_self I hI
  letI : IsHausdorff (J.map f) S := hmap ▸ inferInstance
  apply surjective_of_mk_map_comp_surjective (I := J) f
  intro q
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective q
  obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalOneₐ I y)
  refine ⟨MvPowerSeries.C r, ?_⟩
  change Ideal.Quotient.mk (J.map f) (f (MvPowerSeries.C r)) =
    Ideal.Quotient.mk (J.map f) y
  rw [hC, Ideal.Quotient.eq, hmap]
  change algebraMap R (AdicCompletion I R) r - y ∈
    I.map (algebraMap R (AdicCompletion I R))
  rw [← AdicCompletion.ker_evalOneₐ_eq_map (I := I) hI]
  change AdicCompletion.evalOneₐ I (algebraMap R S r - y) = 0
  rw [map_sub]
  change Ideal.Quotient.mk I r - AdicCompletion.evalOneₐ I y = 0
  rw [hr, sub_self]

theorem isNoetherianRing_completion [IsNoetherianRing R] (I : Ideal R) :
    IsNoetherianRing (AdicCompletion I R) := by
  obtain ⟨n, a, ha⟩ := Submodule.fg_iff_exists_fin_generating_family.mp I.fg_of_isNoetherianRing
  have hmem : ∀ i, a i ∈ I := fun i => ha ▸ Ideal.subset_span (Set.mem_range_self i)
  obtain ⟨f, hC, hX⟩ := exists_powerSeriesMap I I.fg_of_isNoetherianRing a hmem
  exact isNoetherianRing_of_surjective (MvPowerSeries (Fin n) R) (AdicCompletion I R) f
    (powerSeriesMap_surjective I I.fg_of_isNoetherianRing a ha f hC hX)

end PhilipponMultiplicity.NoetherianCompletion

end
end

section

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false
noncomputable section

open IsLocalRing

namespace PhilipponCompletionRegularity

/-- A flat local map with field closed fiber preserves local dimension. -/
theorem dimension_eq_of_flat_local_map
    (R S : Type*) [CommRing R] [CommRing S]
    [IsNoetherianRing R] [IsNoetherianRing S] [IsLocalRing R] [IsLocalRing S]
    [Algebra R S] [Module.Flat R S] [IsLocalHom (algebraMap R S)]
    (hmap : (maximalIdeal R).map (algebraMap R S) = maximalIdeal S) :
    ringKrullDim S = ringKrullDim R := by
  haveI : (maximalIdeal S).LiesOver (maximalIdeal R) :=
    ⟨(maximalIdeal_comap (algebraMap R S)).symm⟩
  have h := Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown
    (R := R) (S := S) (maximalIdeal R) (maximalIdeal S)
  rw [hmap, Ideal.map_quotient_self, Ideal.height_bot, add_zero] at h
  rw [← maximalIdeal_height_eq_ringKrullDim (R := S),
    ← maximalIdeal_height_eq_ringKrullDim (R := R)]
  exact_mod_cast h

/-- Completion at the maximal ideal preserves Krull dimension. -/
theorem dimension_eq
    (R : Type*) [CommRing R] [IsNoetherianRing R] [IsLocalRing R] :
    ringKrullDim (AdicCompletion (maximalIdeal R) R) = ringKrullDim R := by
  haveI := PhilipponMultiplicity.NoetherianCompletion.isNoetherianRing_completion
    (maximalIdeal R)
  exact dimension_eq_of_flat_local_map R _ AdicCompletion.maximalIdeal_eq_map.symm

/-- Regularity can be checked on the actual maximal-adic completion. -/
theorem regular_iff
    (R : Type*) [CommRing R] [IsNoetherianRing R] [IsLocalRing R] :
    IsRegularLocalRing R ↔ IsRegularLocalRing (AdicCompletion (maximalIdeal R) R) := by
  haveI := PhilipponMultiplicity.NoetherianCompletion.isNoetherianRing_completion
    (maximalIdeal R)
  rw [isRegularLocalRing_iff, isRegularLocalRing_iff,
    AdicCompletion.spanFinrank_maximalIdeal_eq, dimension_eq]

end PhilipponCompletionRegularity

end
end

section

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
noncomputable section

open IsLocalRing AlgebraicGeometry CategoryTheory TopologicalSpace

namespace PhilipponRegularStalkFormalModels

theorem completion_residue_surjective
    (K : Type u) [CommRing K] (A : Type v) [CommRing A] [IsLocalRing A]
    [IsNoetherianRing A] [Algebra K A]
    (hres : Function.Surjective ((residue A).comp (algebraMap K A))) :
    Function.Surjective
      ((residue (AdicCompletion (maximalIdeal A) A)).comp
        (algebraMap K (AdicCompletion (maximalIdeal A) A))) := by
  have h := (AdicCompletion.residueField_map_bijective A).surjective.comp hres
  convert h using 1
  ext c
  simp only [Function.comp_apply, RingHom.comp_apply, ResidueField.map_residue]
  rw [IsScalarTower.algebraMap_apply K A (AdicCompletion (maximalIdeal A) A)]

/-- The actual completion of a regular local algebra has a formal
power-series presentation over any coefficient field inducing its residue field. -/
theorem completion_model
    (K : Type u) [Field K] (A : Type v) [CommRing A] [IsRegularLocalRing A]
    [Algebra K A]
    (hres : Function.Surjective ((residue A).comp (algebraMap K A))) :
    ∃ r : ℕ, Nonempty (AdicCompletion (maximalIdeal A) A ≃+* MvPowerSeries (Fin r) K) := by
  letI := (PhilipponCompletionRegularity.regular_iff A).mp inferInstance
  obtain ⟨r, ⟨e⟩⟩ := PhilipponCompleteRegularLocalStructure.exists_fin_equiv K
    (AdicCompletion (maximalIdeal A) A) (completion_residue_surjective K A hres)
  exact ⟨r, ⟨e.symm.toRingEquiv⟩⟩

/-- Closed points of a scheme locally of finite type over an algebraically
closed field have the original ground field as coefficient field. -/
theorem closed_stalk_model
    (K : Type u) [Field K] [IsAlgClosed K] {X : Scheme.{u}}
    (π : X ⟶ Spec (.of K)) [LocallyOfFiniteType π]
    (x : X) (hx : IsClosed ({x} : Set X))
    (hreg : IsRegularLocalRing (X.presheaf.stalk x)) :
    ∃ r : ℕ, Nonempty (AdicCompletion (maximalIdeal (X.presheaf.stalk x))
      (X.presheaf.stalk x) ≃+* MvPowerSeries (Fin r) K) := by
  let A := X.presheaf.stalk x
  let ρ : CommRingCat.of K ⟶ X.presheaf.stalk x :=
    Spec.preimage (X.fromSpecStalk x ≫ π)
  letI : Algebra K A := ρ.hom.toAlgebra
  letI : IsRegularLocalRing A := hreg
  let e := residueFieldIsoBase π x hx
  have hcat : ρ ≫ X.residue x = e.inv := by
    apply Spec.map_injective
    rw [Spec.map_comp, Spec.map_preimage, SpecMap_residueFieldIsoBase_inv]
    rfl
  have hres : Function.Surjective ((residue A).comp (algebraMap K A)) := by
    change Function.Surjective (ρ ≫ X.residue x).hom
    rw [hcat]
    exact (ConcreteCategory.bijective_of_isIso e.inv).surjective
  exact completion_model K A hres

end PhilipponRegularStalkFormalModels

end
end

set_option autoImplicit false
open AlgebraicGeometry CategoryTheory TopologicalSpace IsLocalRing

theorem solution
    (K : Type u) [Field K] [IsAlgClosed K] {X : Scheme.{u}}
    (π : X ⟶ Spec (.of K)) [LocallyOfFiniteType π]
    (x : X) (hx : IsClosed ({x} : Set X))
    (hreg : IsRegularLocalRing (X.presheaf.stalk x)) :
    ∃ r : ℕ, Nonempty (AdicCompletion (maximalIdeal (X.presheaf.stalk x))
      (X.presheaf.stalk x) ≃+* MvPowerSeries (Fin r) K) := by
  exact PhilipponRegularStalkFormalModels.closed_stalk_model K π x hx hreg

#print axioms PhilipponCompleteLocalPowerSeriesPresentation.exists_map
#print axioms PhilipponCompleteLocalPowerSeriesPresentation.surjective
#print axioms PhilipponCompleteLocalPowerSeriesPresentation.exists_surjective
#print axioms PhilipponPowerSeriesRegularity.powerSeries
#print axioms PhilipponPowerSeriesRegularity.fin
#print axioms PhilipponPowerSeriesRegularity.mvPowerSeries
#print axioms PhilipponMultiplicity.Chardin.powerSeries_complete_constantCoeff_ker
#print axioms PhilipponCompleteRegularLocalStructure.maximalIdeal_eq_span_X
#print axioms PhilipponCompleteRegularLocalStructure.spanFinrank_maximalIdeal_le_card
#print axioms PhilipponCompleteRegularLocalStructure.injective_of_surjective
#print axioms PhilipponCompleteRegularLocalStructure.equiv_of_generators
#print axioms PhilipponCompleteRegularLocalStructure.exists_fin_equiv
#print axioms PhilipponMultiplicity.NoetherianCompletion.exists_powerSeriesMap
#print axioms PhilipponMultiplicity.NoetherianCompletion.powerSeriesMap_surjective
#print axioms PhilipponMultiplicity.NoetherianCompletion.isNoetherianRing_completion
#print axioms PhilipponCompletionRegularity.dimension_eq_of_flat_local_map
#print axioms PhilipponCompletionRegularity.dimension_eq
#print axioms PhilipponCompletionRegularity.regular_iff
#print axioms PhilipponRegularStalkFormalModels.completion_residue_surjective
#print axioms PhilipponRegularStalkFormalModels.completion_model
#print axioms PhilipponRegularStalkFormalModels.closed_stalk_model
#print axioms solution
