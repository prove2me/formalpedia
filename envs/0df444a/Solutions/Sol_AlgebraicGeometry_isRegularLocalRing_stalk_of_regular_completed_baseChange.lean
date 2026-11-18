-- Prove2me | solution 1 for AlgebraicGeometry.isRegularLocalRing_stalk_of_regular_completed_baseChange
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-11-18T00:10:02.172725+00:00
-- url     : https://prove2.me/submissions/c73a1403-4bc5-4747-9b1d-659e6116603e

import Mathlib

universe u v

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
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
noncomputable section

open IsLocalRing TensorProduct

namespace PhilipponCompletionClosedFiber

variable (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]

abbrev Completed := AdicCompletion (maximalIdeal A) A

theorem approximation (c : Completed A) :
    ∃ a : A, c - algebraMap A (Completed A) a ∈
      (maximalIdeal A).map (algebraMap A (Completed A)) := by
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalOneₐ (maximalIdeal A) c)
  refine ⟨a, ?_⟩
  rw [← AdicCompletion.ker_evalOneₐ_eq_map (maximalIdeal A)
    (maximalIdeal A).fg_of_isNoetherianRing, RingHom.mem_ker, map_sub]
  change AdicCompletion.evalOneₐ (maximalIdeal A) c - Ideal.Quotient.mk (maximalIdeal A) a = 0
  exact sub_eq_zero.mpr ha.symm

theorem approximation_pow (n : ℕ) (c : Completed A) :
    ∃ a : A, c - algebraMap A (Completed A) a ∈
      ((maximalIdeal A) ^ n).map (algebraMap A (Completed A)) := by
  obtain ⟨a, ha⟩ := Submodule.mkQ_surjective
    ((maximalIdeal A) ^ n • (⊤ : Submodule A A))
    (AdicCompletion.eval (maximalIdeal A) A n c)
  refine ⟨a, ?_⟩
  rw [← Submodule.restrictScalars_mem A, ← Ideal.smul_top_eq_map,
    AdicCompletion.pow_smul_top_eq_ker_eval (maximalIdeal A).fg_of_isNoetherianRing,
    LinearMap.mem_ker]
  simp only [map_sub, AdicCompletion.algebraMap_apply, AdicCompletion.eval_of]
  exact sub_eq_zero.mpr ha.symm

variable (B : Type u) [CommRing B] [Algebra A B]

abbrev BaseChange := B ⊗[A] Completed A

instance faithfullyFlat : Module.FaithfullyFlat B (BaseChange A B) := by
  haveI : Module.FaithfullyFlat A (Completed A) := Module.FaithfullyFlat.of_flat_of_isLocalHom
  infer_instance

def quotientMap (p : Ideal B) :
    B ⧸ p →+* (BaseChange A B) ⧸ p.map (algebraMap B (BaseChange A B)) :=
  Ideal.quotientMap _ (algebraMap B (BaseChange A B)) Ideal.le_comap_map

theorem quotientMap_injective (p : Ideal B) : Function.Injective (quotientMap A B p) := by
  apply Ideal.quotientMap_injective'
  exact (Ideal.comap_map_eq_self_of_faithfullyFlat p).le

theorem mapped_ideal_le (I : Ideal A) (p : Ideal B)
    (hp : I.map (algebraMap A B) ≤ p) :
    (I.map (algebraMap A (Completed A))).map
      (Algebra.TensorProduct.includeRight : Completed A →ₐ[A] BaseChange A B) ≤
      p.map (algebraMap B (BaseChange A B)) := by
  have hcomp : (Algebra.TensorProduct.includeRight : Completed A →ₐ[A] BaseChange A B).toRingHom.comp
      (algebraMap A (Completed A)) =
      (algebraMap B (BaseChange A B)).comp (algebraMap A B) := by
    ext a
    exact (Algebra.TensorProduct.includeRight : Completed A →ₐ[A] BaseChange A B).commutes a |>.trans
      (IsScalarTower.algebraMap_apply A B (BaseChange A B) a).symm
  change (I.map (algebraMap A (Completed A))).map
    (Algebra.TensorProduct.includeRight : Completed A →ₐ[A] BaseChange A B).toRingHom ≤ _
  rw [Ideal.map_map, hcomp, ← Ideal.map_map]
  exact Ideal.map_mono hp

theorem mapped_maximal_le (p : Ideal B)
    (hp : (maximalIdeal A).map (algebraMap A B) ≤ p) :
    ((maximalIdeal A).map (algebraMap A (Completed A))).map
      (Algebra.TensorProduct.includeRight : Completed A →ₐ[A] BaseChange A B) ≤
      p.map (algebraMap B (BaseChange A B)) :=
  mapped_ideal_le A B (maximalIdeal A) p hp

/-- Every quotient supported over the closed point is unchanged by the
actual tensor-product base change to the completion. -/
theorem quotientMap_surjective_of_approximation (I : Ideal A)
    (happrox : ∀ c : Completed A, ∃ a : A, c - algebraMap A (Completed A) a ∈
      I.map (algebraMap A (Completed A)))
    (p : Ideal B) (hp : I.map (algebraMap A B) ≤ p) :
    Function.Surjective (quotientMap A B p) := by
  let T := BaseChange A B
  let P := p.map (algebraMap B T)
  let q : T →+* T ⧸ P := Ideal.Quotient.mk P
  have hrepresent (z : T) : ∃ b : B, q z = q (algebraMap B T b) := by
    induction z using TensorProduct.induction_on with
    | zero => exact ⟨0, by simp⟩
    | add x y hx hy =>
        obtain ⟨b, hb⟩ := hx
        obtain ⟨c, hc⟩ := hy
        refine ⟨b + c, ?_⟩
        calc q (x + y) = q x + q y := q.map_add x y
          _ = q (algebraMap B T b) + q (algebraMap B T c) := congrArg₂ (· + ·) hb hc
          _ = q (algebraMap B T (b + c)) := by
            rw [(algebraMap B T).map_add, q.map_add]
    | tmul b c =>
        obtain ⟨a, ha⟩ := happrox c
        let r : Completed A →ₐ[A] T := Algebra.TensorProduct.includeRight
        have hmem : r (c - algebraMap A (Completed A) a) ∈ P :=
          mapped_ideal_le A B I p hp (Ideal.mem_map_of_mem r ha)
        have heq : q (r c) = q (r (algebraMap A (Completed A) a)) := by
          rw [← sub_eq_zero, ← map_sub, ← map_sub]
          exact Ideal.Quotient.eq_zero_iff_mem.mpr hmem
        refine ⟨b * algebraMap A B a, ?_⟩
        calc q (b ⊗ₜ[A] c) = q (algebraMap B T b) * q (r c) := by
              rw [← q.map_mul]
              congr 1
              change b ⊗ₜ[A] c = (b ⊗ₜ[A] (1 : Completed A)) * ((1 : B) ⊗ₜ[A] c)
              rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
          _ = q (algebraMap B T b) * q (algebraMap B T (algebraMap A B a)) := by
              rw [heq]
              congr 1
              congr 1
              exact (r.commutes a).trans (IsScalarTower.algebraMap_apply A B T a).symm
          _ = q (algebraMap B T (b * algebraMap A B a)) := by rw [map_mul, map_mul]
  intro z
  obtain ⟨t, rfl⟩ := Ideal.Quotient.mk_surjective z
  obtain ⟨b, hb⟩ := hrepresent t
  exact ⟨Ideal.Quotient.mk p b, hb.symm⟩

theorem quotientMap_surjective (p : Ideal B)
    (hp : (maximalIdeal A).map (algebraMap A B) ≤ p) :
    Function.Surjective (quotientMap A B p) :=
  quotientMap_surjective_of_approximation A B (maximalIdeal A) (approximation A) p hp

theorem quotientMap_surjective_of_power (p : Ideal B) (n : ℕ)
    (hp : ((maximalIdeal A) ^ n).map (algebraMap A B) ≤ p) :
    Function.Surjective (quotientMap A B p) :=
  quotientMap_surjective_of_approximation A B ((maximalIdeal A) ^ n)
    (approximation_pow A n) p hp

def quotientEquiv (p : Ideal B)
    (hp : (maximalIdeal A).map (algebraMap A B) ≤ p) :
    B ⧸ p ≃+* (BaseChange A B) ⧸ p.map (algebraMap B (BaseChange A B)) :=
  RingEquiv.ofBijective (quotientMap A B p)
    ⟨quotientMap_injective A B p, quotientMap_surjective A B p hp⟩

def quotientEquivOfPower (p : Ideal B) (n : ℕ)
    (hp : ((maximalIdeal A) ^ n).map (algebraMap A B) ≤ p) :
    B ⧸ p ≃+* (BaseChange A B) ⧸ p.map (algebraMap B (BaseChange A B)) :=
  RingEquiv.ofBijective (quotientMap A B p)
    ⟨quotientMap_injective A B p, quotientMap_surjective_of_power A B p n hp⟩

end PhilipponCompletionClosedFiber

end
end

section

set_option autoImplicit false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
noncomputable section

open IsLocalRing

namespace PhilipponFlatLocalRegularity

variable {R S : Type*} [CommRing R] [CommRing S]
    [IsNoetherianRing R] [IsNoetherianRing S] [IsLocalRing R] [IsLocalRing S]
    [Algebra R S] [Module.Flat R S] [IsLocalHom (algebraMap R S)]

theorem exists_sub_mem_maximalIdeal
    (hres : Function.Surjective (ResidueField.map (algebraMap R S))) (b : S) :
    ∃ a : R, algebraMap R S a - b ∈ maximalIdeal S := by
  obtain ⟨c, hc⟩ := hres (residue S b)
  obtain ⟨a, rfl⟩ := residue_surjective c
  refine ⟨a, ?_⟩
  rw [← residue_eq_zero_iff, map_sub, ← ResidueField.map_residue, hc, sub_self]

/-- Every tangent vector is represented by an element of the original
maximal ideal when the closed fiber and residue field are unchanged. -/
theorem exists_sub_mem_maximalIdeal_sq
    (hmap : (maximalIdeal R).map (algebraMap R S) = maximalIdeal S)
    (hres : Function.Surjective (ResidueField.map (algebraMap R S)))
    (b : S) (hb : b ∈ maximalIdeal S) :
    ∃ a : R, a ∈ maximalIdeal R ∧
      algebraMap R S a - b ∈ (maximalIdeal S) ^ 2 := by
  have hb' : b ∈ Ideal.span (algebraMap R S '' (maximalIdeal R : Set R)) := by
    change b ∈ (maximalIdeal R).map (algebraMap R S)
    rwa [hmap]
  clear hb
  induction hb' using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨a, ha, rfl⟩ := hx
      exact ⟨a, ha, by simp⟩
  | zero => exact ⟨0, by simp, by simp⟩
  | add x y hx hy ihx ihy =>
      obtain ⟨a, ha, hax⟩ := ihx
      obtain ⟨c, hc, hcy⟩ := ihy
      exact ⟨a + c, Ideal.add_mem _ ha hc, by
        simpa only [map_add, add_sub_add_comm] using Ideal.add_mem _ hax hcy⟩
  | smul c x hx ih =>
      obtain ⟨a, ha, hax⟩ := ih
      obtain ⟨d, hd⟩ := exists_sub_mem_maximalIdeal hres c
      refine ⟨d * a, Ideal.mul_mem_left _ _ ha, ?_⟩
      have ha' : algebraMap R S a ∈ maximalIdeal S := by
        rw [← hmap]
        exact Ideal.mem_map_of_mem _ ha
      have hprod : (algebraMap R S d - c) * algebraMap R S a ∈
          (maximalIdeal S) ^ 2 := by
        rw [pow_two]
        exact Ideal.mul_mem_mul hd ha'
      have hsum := Ideal.add_mem _ hprod (Ideal.mul_mem_left _ c hax)
      convert hsum using 1 <;> simp only [map_mul, smul_eq_mul] <;> ring

/-- The natural cotangent map is an isomorphism for a flat local map
with unchanged closed fiber and residue field. -/
theorem mapCotangent_bijective
    (hmap : (maximalIdeal R).map (algebraMap R S) = maximalIdeal S)
    (hres : Function.Surjective (ResidueField.map (algebraMap R S))) :
    Function.Bijective (Ideal.mapCotangent (maximalIdeal R) (maximalIdeal S)
      (Algebra.ofId R S) (maximalIdeal_comap (algebraMap R S)).ge) := by
  let f := Ideal.mapCotangent (maximalIdeal R) (maximalIdeal S)
    (Algebra.ofId R S) (maximalIdeal_comap (algebraMap R S)).ge
  haveI : Module.FaithfullyFlat R S := Module.FaithfullyFlat.of_flat_of_isLocalHom
  constructor
  · rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    obtain ⟨a, rfl⟩ := Ideal.toCotangent_surjective _ x
    have hmem : algebraMap R S a.val ∈ (maximalIdeal S) ^ 2 := by
      simpa only [f, Ideal.mapCotangent_toCotangent, Algebra.ofId_apply,
        Ideal.toCotangent_eq_zero] using hx
    have hmem' : a.val ∈ (((maximalIdeal R) ^ 2).map (algebraMap R S)).comap
        (algebraMap R S) := by
      change algebraMap R S a.val ∈ ((maximalIdeal R) ^ 2).map (algebraMap R S)
      rwa [Ideal.map_pow, hmap]
    rw [Ideal.comap_map_eq_self_of_faithfullyFlat] at hmem'
    exact ((maximalIdeal R).toCotangent_eq_zero a).mpr hmem'
  · intro x
    obtain ⟨b, rfl⟩ := Ideal.toCotangent_surjective _ x
    obtain ⟨a, ha, hdiff⟩ := exists_sub_mem_maximalIdeal_sq hmap hres b.val b.property
    refine ⟨(maximalIdeal R).toCotangent ⟨a, ha⟩, ?_⟩
    exact (maximalIdeal S).toCotangent_eq.mpr hdiff

theorem spanFinrank_maximalIdeal_eq
    (hmap : (maximalIdeal R).map (algebraMap R S) = maximalIdeal S)
    (hres : Function.Bijective (ResidueField.map (algebraMap R S))) :
    (maximalIdeal S).spanFinrank = (maximalIdeal R).spanFinrank := by
  let f := Ideal.mapCotangent (maximalIdeal R) (maximalIdeal S)
    (Algebra.ofId R S) (maximalIdeal_comap (algebraMap R S)).ge
  have hrank := lift_rank_eq_of_equiv_equiv _
    (LinearEquiv.ofBijective f (mapCotangent_bijective hmap hres.surjective)).toAddEquiv
    hres (fun r m ↦ by
      obtain ⟨s, rfl⟩ := residue_surjective r
      simp only [LinearEquiv.coe_toAddEquiv, LinearEquiv.ofBijective_apply,
        ResidueField.map_residue]
      change f (s • m) = algebraMap R S s • f m
      rw [map_smul, IsScalarTower.algebraMap_smul])
  rw [spanFinrank_maximalIdeal_eq_finrank_cotangentSpace,
    spanFinrank_maximalIdeal_eq_finrank_cotangentSpace]
  simpa only [Module.finrank, CotangentSpace, Cardinal.toNat_lift] using
    (congrArg Cardinal.toNat hrank).symm

/-- Regularity is equivalent across a flat local map whose closed fiber
and residue field are unchanged. -/
theorem regular_iff
    (hmap : (maximalIdeal R).map (algebraMap R S) = maximalIdeal S)
    (hres : Function.Bijective (ResidueField.map (algebraMap R S))) :
    IsRegularLocalRing R ↔ IsRegularLocalRing S := by
  rw [isRegularLocalRing_iff, isRegularLocalRing_iff,
    spanFinrank_maximalIdeal_eq hmap hres,
    PhilipponCompletionRegularity.dimension_eq_of_flat_local_map R S hmap]

end PhilipponFlatLocalRegularity

end
end

section

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 80000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
noncomputable section

open IsLocalRing

namespace PhilipponCompletionLocalComparison
open PhilipponCompletionClosedFiber

variable (A B : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    [CommRing B] [IsLocalRing B] [Algebra A B] [IsLocalHom (algebraMap A B)]

lemma maximal_le : (maximalIdeal A).map (algebraMap A B) ≤ maximalIdeal B := by
  rw [Ideal.map_le_iff_le_comap, maximalIdeal_comap]

def closedPrime : Ideal (BaseChange A B) :=
  (maximalIdeal B).map (algebraMap B (BaseChange A B))

instance closedPrime_isMaximal : (closedPrime A B).IsMaximal := by
  letI : Field (B ⧸ maximalIdeal B) := Ideal.Quotient.field (maximalIdeal B)
  exact Ideal.Quotient.maximal_of_isField _
    ((quotientEquiv A B (maximalIdeal B) (maximal_le A B)).symm.isField
      (Field.toIsField (B ⧸ maximalIdeal B)))

abbrev Ring := Localization.AtPrime (closedPrime A B)

theorem map_maximalIdeal : (maximalIdeal B).map (algebraMap B (Ring A B)) = maximalIdeal (Ring A B) := by
  rw [IsScalarTower.algebraMap_eq B (BaseChange A B) (Ring A B), ← Ideal.map_map]
  exact Localization.AtPrime.map_eq_maximalIdeal

instance map_isLocalHom : IsLocalHom (algebraMap B (Ring A B)) := by
  apply ((local_hom_TFAE (algebraMap B (Ring A B))).out 0 2).mpr
  exact (map_maximalIdeal A B).le

theorem map_flat : RingHom.Flat (R := B) (S := Ring A B) (algebraMap B (Ring A B)) := by
  haveI : Module.Flat B (BaseChange A B) := inferInstance
  haveI : Module.Flat B (Ring A B) := Module.Flat.trans B (BaseChange A B) (Ring A B)
  exact RingHom.flat_algebraMap_iff.mpr inferInstance

def residueEquiv : ResidueField B ≃+* ResidueField (Ring A B) :=
  (quotientEquiv A B (maximalIdeal B) (maximal_le A B)).trans
    (IsLocalization.AtPrime.equivQuotMaximalIdeal (closedPrime A B) (Ring A B))

theorem residueEquiv_apply (b : B) :
    residueEquiv A B (residue B b) = residue (Ring A B) (algebraMap B (Ring A B) b) := by
  change IsLocalization.AtPrime.equivQuotMaximalIdeal (closedPrime A B) (Ring A B)
    (Ideal.Quotient.mk (closedPrime A B) (algebraMap B (BaseChange A B) b)) = _
  rw [IsLocalization.AtPrime.equivQuotMaximalIdeal_apply_mk]
  rw [IsScalarTower.algebraMap_apply B (BaseChange A B) (Ring A B)]
  rfl

theorem residueField_map_bijective : Function.Bijective
    (ResidueField.map (R := B) (S := Ring A B) (algebraMap B (Ring A B))) := by
  have he : ResidueField.map (R := B) (S := Ring A B) (algebraMap B (Ring A B)) =
      (residueEquiv A B).toRingHom := by
    apply RingHom.ext
    intro b
    obtain ⟨b, rfl⟩ := residue_surjective b
    rw [ResidueField.map_residue]
    exact (residueEquiv_apply A B b).symm
  rw [he]
  exact (residueEquiv A B).bijective

/-- The canonical local ring above a point of the closed fiber has
the same regularity as the original local ring. -/
theorem regular_iff [IsNoetherianRing B] [IsNoetherianRing (BaseChange A B)] :
    IsRegularLocalRing B ↔ IsRegularLocalRing (Ring A B) := by
  haveI : Module.Flat B (Ring A B) := RingHom.flat_algebraMap_iff.mp (map_flat A B)
  exact PhilipponFlatLocalRegularity.regular_iff (map_maximalIdeal A B)
    (residueField_map_bijective A B)

end PhilipponCompletionLocalComparison

end
end

section

set_option autoImplicit false
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
noncomputable section

namespace PhilipponAdicQuotientEquivalence

variable {R S : Type*} [CommRing R] [CommRing S]

theorem eval_factor (I : Ideal R) {m n : ℕ} (h : m ≤ n) (x : AdicCompletion I R) :
    Ideal.Quotient.factorPow I h (AdicCompletion.evalₐ I n x) =
      AdicCompletion.evalₐ I m x := by
  obtain ⟨a, rfl⟩ := AdicCompletion.mk_surjective I R x
  rw [AdicCompletion.evalₐ_mk, AdicCompletion.evalₐ_mk]
  change Ideal.Quotient.mk (I ^ m) (a.val n) = Ideal.Quotient.mk (I ^ m) (a.val m)
  apply Ideal.Quotient.eq.mpr
  simpa only [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top] using (a.property h).symm

variable (I : Ideal R) (J : Ideal S)
    (e : ∀ n : ℕ, R ⧸ I ^ n ≃+* S ⧸ J ^ n)
    (he : ∀ {m n : ℕ} (h : m ≤ n) (x : R ⧸ I ^ n),
      Ideal.Quotient.factorPow J h (e n x) = e m (Ideal.Quotient.factorPow I h x))

include he in
theorem forward_compatible {m n : ℕ} (h : m ≤ n) :
    (Ideal.Quotient.factorPow J h).comp
        ((e n).toRingHom.comp (AdicCompletion.evalₐ I n).toRingHom) =
      (e m).toRingHom.comp (AdicCompletion.evalₐ I m).toRingHom := by
  apply RingHom.ext
  intro x
  change Ideal.Quotient.factorPow J h (e n (AdicCompletion.evalₐ I n x)) =
    e m (AdicCompletion.evalₐ I m x)
  rw [he, eval_factor]

def forward : AdicCompletion I R →+* AdicCompletion J S :=
  AdicCompletion.liftRingHom J
    (fun n => (e n).toRingHom.comp (AdicCompletion.evalₐ I n).toRingHom)
    (forward_compatible I J e he)

theorem eval_forward (n : ℕ) (x : AdicCompletion I R) :
    AdicCompletion.evalₐ J n (forward I J e he x) = e n (AdicCompletion.evalₐ I n x) := by
  unfold forward
  exact AdicCompletion.evalₐ_liftRingHom J
    (fun n => (e n).toRingHom.comp (AdicCompletion.evalₐ I n).toRingHom)
    (forward_compatible I J e he) n x

include he in
theorem inverse_compatible {m n : ℕ} (h : m ≤ n) (x : S ⧸ J ^ n) :
    Ideal.Quotient.factorPow I h ((e n).symm x) =
      (e m).symm (Ideal.Quotient.factorPow J h x) := by
  apply (e m).injective
  rw [RingEquiv.apply_symm_apply]
  simpa only [RingEquiv.apply_symm_apply] using (he h ((e n).symm x)).symm

/-- Compatible isomorphisms of all infinitesimal quotients give an actual
isomorphism of the adic completion rings. -/
def equiv : AdicCompletion I R ≃+* AdicCompletion J S :=
  RingEquiv.ofRingHom (forward I J e he)
    (forward J I (fun n => (e n).symm) (inverse_compatible I J e he))
    (by
      apply RingHom.ext
      intro x
      apply AdicCompletion.ext_evalₐ
      intro n
      change AdicCompletion.evalₐ J n
        (forward I J e he (forward J I (fun n => (e n).symm)
          (inverse_compatible I J e he) x)) = AdicCompletion.evalₐ J n x
      rw [eval_forward, eval_forward, RingEquiv.apply_symm_apply])
    (by
      apply RingHom.ext
      intro x
      apply AdicCompletion.ext_evalₐ
      intro n
      change AdicCompletion.evalₐ I n
        (forward J I (fun n => (e n).symm) (inverse_compatible I J e he)
          (forward I J e he x)) = AdicCompletion.evalₐ I n x
      rw [eval_forward, eval_forward, RingEquiv.symm_apply_apply])

end PhilipponAdicQuotientEquivalence

end
end

section

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 80000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
noncomputable section

open IsLocalRing

namespace PhilipponCompletionLocalAdicIso
open PhilipponCompletionClosedFiber PhilipponCompletionLocalComparison

variable (A B : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    [CommRing B] [IsLocalRing B] [Algebra A B] [IsLocalHom (algebraMap A B)]

theorem power_le (n : ℕ) : ((maximalIdeal A) ^ n).map (algebraMap A B) ≤ (maximalIdeal B) ^ n := by
  rw [Ideal.map_pow]
  exact Ideal.pow_right_mono (maximal_le A B) n

variable (D : Type u) [CommRing D] [IsLocalRing D]
    [Algebra (BaseChange A B) D] [IsLocalization.AtPrime D (closedPrime A B)]
    [Algebra B D] [IsScalarTower B (BaseChange A B) D]

def quotientEquiv (n : ℕ) :
    B ⧸ (maximalIdeal B) ^ n ≃+* D ⧸ (maximalIdeal D) ^ n :=
  (quotientEquivOfPower A B ((maximalIdeal B) ^ n) n (power_le A B n)).trans
    ((Ideal.quotEquivOfEq (show ((maximalIdeal B) ^ n).map
        (algebraMap B (BaseChange A B)) = (closedPrime A B) ^ n by
          rw [Ideal.map_pow]; rfl)).trans
      (IsLocalization.AtPrime.equivQuotMaximalIdealPow (closedPrime A B) D n).toRingEquiv)

theorem quotientEquiv_apply_mk (n : ℕ) (b : B) :
    quotientEquiv A B D n (Ideal.Quotient.mk ((maximalIdeal B) ^ n) b) =
      Ideal.Quotient.mk ((maximalIdeal D) ^ n) (algebraMap B D b) := by
  change IsLocalization.AtPrime.equivQuotMaximalIdealPow (closedPrime A B) D n
    (Ideal.Quotient.mk ((closedPrime A B) ^ n) (algebraMap B (BaseChange A B) b)) = _
  rw [IsLocalization.AtPrime.equivQuotMaximalIdealPow_apply_mk,
    IsScalarTower.algebraMap_apply B (BaseChange A B) D]

theorem compatible {m n : ℕ} (h : m ≤ n) (x : B ⧸ (maximalIdeal B) ^ n) :
    Ideal.Quotient.factorPow (maximalIdeal D) h (quotientEquiv A B D n x) =
      quotientEquiv A B D m (Ideal.Quotient.factorPow (maximalIdeal B) h x) := by
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [quotientEquiv_apply_mk]
  change Ideal.Quotient.mk ((maximalIdeal D) ^ m) (algebraMap B D b) =
    quotientEquiv A B D m (Ideal.Quotient.mk ((maximalIdeal B) ^ m) b)
  exact (quotientEquiv_apply_mk A B D m b).symm

/-- Actual completed local rings agree at the canonical point above the
closed fiber of the tensor base change to the completed base. -/
def completionIso : AdicCompletion (maximalIdeal B) B ≃+*
    AdicCompletion (maximalIdeal D) D :=
  PhilipponAdicQuotientEquivalence.equiv (maximalIdeal B) (maximalIdeal D)
    (quotientEquiv A B D) (compatible A B D)

theorem eval_completionIso (n : ℕ) (x : AdicCompletion (maximalIdeal B) B) :
    AdicCompletion.evalₐ (maximalIdeal D) n (completionIso A B D x) =
      quotientEquiv A B D n (AdicCompletion.evalₐ (maximalIdeal B) n x) :=
  PhilipponAdicQuotientEquivalence.eval_forward (maximalIdeal B) (maximalIdeal D)
    (quotientEquiv A B D) (compatible A B D) n x

theorem completionIso_algebraMap (b : B) :
    completionIso A B D (algebraMap B (AdicCompletion (maximalIdeal B) B) b) =
      algebraMap D (AdicCompletion (maximalIdeal D) D)
        (algebraMap B D b) := by
  apply AdicCompletion.ext_evalₐ
  intro n
  rw [eval_completionIso, AdicCompletion.algebraMap_apply, AdicCompletion.evalₐ_of,
    quotientEquiv_apply_mk, AdicCompletion.algebraMap_apply, AdicCompletion.evalₐ_of]
  simp only [Algebra.algebraMap_self, RingHom.id_apply]

include A in
theorem regular_of_completed_model [IsNoetherianRing B]
    (R : Type v) [CommRing R] [IsRegularLocalRing R]
    (e : AdicCompletion (maximalIdeal D) D ≃+* R) :
    IsRegularLocalRing B := by
  apply (PhilipponCompletionRegularity.regular_iff B).mpr
  exact IsRegularLocalRing.of_ringEquiv ((completionIso A B D).trans e).symm

end PhilipponCompletionLocalAdicIso
end
end

section

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 80000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
noncomputable section

open IsLocalRing AlgebraicGeometry CategoryTheory

namespace PhilipponCompletedBaseChangePoint
open PhilipponCompletionClosedFiber PhilipponCompletionLocalComparison

variable (A B : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    [CommRing B] [IsLocalRing B] [Algebra A B] [IsLocalHom (algebraMap A B)]

def point : Spec (.of (BaseChange A B)) := ⟨closedPrime A B, inferInstance⟩

theorem point_to_original :
    Spec.map (CommRingCat.ofHom (algebraMap B (BaseChange A B))) (point A B) = closedPoint B := by
  apply PrimeSpectrum.ext
  exact Ideal.comap_map_eq_self_of_faithfullyFlat (maximalIdeal B)

theorem completed_comap :
    (closedPrime A B).comap
      (Algebra.TensorProduct.includeRight : Completed A →ₐ[A] BaseChange A B) =
      maximalIdeal (Completed A) := by
  have hle : maximalIdeal (Completed A) ≤ (closedPrime A B).comap
      (Algebra.TensorProduct.includeRight : Completed A →ₐ[A] BaseChange A B) := by
    rw [AdicCompletion.maximalIdeal_eq_map, ← Ideal.map_le_iff_le_comap]
    exact mapped_maximal_le A B (maximalIdeal B) (maximal_le A B)
  have hne : (closedPrime A B).comap
      (Algebra.TensorProduct.includeRight : Completed A →ₐ[A] BaseChange A B) ≠ ⊤ :=
    Ideal.IsPrime.ne_top'
  exact (le_maximalIdeal hne).antisymm hle

theorem point_to_completed :
    Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.includeRight : Completed A →ₐ[A] BaseChange A B).toRingHom)
      (point A B) = closedPoint (Completed A) := by
  apply PrimeSpectrum.ext
  exact completed_comap A B

/-- The stalk at the actual closed-fiber point of the affine tensor
base change has the same completed local ring as the original local ring. -/
def completionIso : AdicCompletion (maximalIdeal B) B ≃+*
    AdicCompletion (maximalIdeal ((Spec (.of (BaseChange A B))).presheaf.stalk (point A B)))
      ((Spec (.of (BaseChange A B))).presheaf.stalk (point A B)) := by
  let D := (Spec.structureSheaf (BaseChange A B)).presheaf.stalk (point A B)
  letI : IsLocalRing D := inferInstanceAs
    (IsLocalRing ((Spec (.of (BaseChange A B))).presheaf.stalk (point A B)))
  letI : Algebra B D := Algebra.compHom D (algebraMap B (BaseChange A B))
  letI : IsLocalization.AtPrime D (closedPrime A B) := by
    change IsLocalization.AtPrime
      ((Spec.structureSheaf (BaseChange A B)).presheaf.stalk (point A B)) (point A B).asIdeal
    infer_instance
  letI : IsScalarTower B (BaseChange A B) D := by
    constructor
    intro b t d
    change (b • t) • d = (algebraMap B (BaseChange A B) b) • (t • d)
    rw [Algebra.smul_def b t]
    exact mul_smul (algebraMap B (BaseChange A B) b) t d
  exact PhilipponCompletionLocalAdicIso.completionIso A B D

end PhilipponCompletedBaseChangePoint

end
end

section

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 80000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
noncomputable section

open IsLocalRing AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace PhilipponCompletedPullbackPoint
open PhilipponCompletionClosedFiber

variable (A B : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    [CommRing B] [IsLocalRing B] [Algebra A B] [IsLocalHom (algebraMap A B)]

abbrev originalMap : Spec (.of B) ⟶ Spec (.of A) :=
  Spec.map (CommRingCat.ofHom (algebraMap A B))

abbrev completionMap : Spec (.of (Completed A)) ⟶ Spec (.of A) :=
  Spec.map (CommRingCat.ofHom (algebraMap A (Completed A)))

abbrev model : Scheme.{u} := pullback (originalMap A B) (completionMap A)

def tensorIso : model A B ≅ Spec (.of (BaseChange A B)) :=
  pullbackSpecIso A B (Completed A)

/-- An actual point of the scheme-theoretic pullback, lying above both
closed points. -/
def point : model A B :=
  (tensorIso A B).inv (PhilipponCompletedBaseChangePoint.point A B)

theorem point_to_original :
    pullback.fst (originalMap A B) (completionMap A) (point A B) = closedPoint B := by
  change ((tensorIso A B).inv ≫ pullback.fst _ _)
    (PhilipponCompletedBaseChangePoint.point A B) = _
  rw [tensorIso, pullbackSpecIso_inv_fst']
  exact PhilipponCompletedBaseChangePoint.point_to_original A B

theorem point_to_completed :
    pullback.snd (originalMap A B) (completionMap A) (point A B) =
      closedPoint (Completed A) := by
  change ((tensorIso A B).inv ≫ pullback.snd _ _)
    (PhilipponCompletedBaseChangePoint.point A B) = _
  rw [tensorIso, pullbackSpecIso_inv_snd]
  exact PhilipponCompletedBaseChangePoint.point_to_completed A B

def stalkEquiv : (model A B).presheaf.stalk (point A B) ≃+*
    (Spec (.of (BaseChange A B))).presheaf.stalk
      (PhilipponCompletedBaseChangePoint.point A B) :=
  (asIso ((tensorIso A B).inv.stalkMap
    (PhilipponCompletedBaseChangePoint.point A B))).commRingCatIsoToRingEquiv

include A in
/-- Regularity at the actual point of the completed scheme pullback
descends to the original local ring. No finite-type assumption on the
local homomorphism is needed. -/
theorem regular_of_pullback [IsNoetherianRing B]
    (hreg : IsRegularLocalRing ((model A B).presheaf.stalk (point A B))) :
    IsRegularLocalRing B := by
  letI := hreg
  let D := (Spec.structureSheaf (BaseChange A B)).presheaf.stalk
    (PhilipponCompletedBaseChangePoint.point A B)
  letI : IsLocalRing D := inferInstanceAs
    (IsLocalRing ((Spec (.of (BaseChange A B))).presheaf.stalk
      (PhilipponCompletedBaseChangePoint.point A B)))
  letI : IsRegularLocalRing D := IsRegularLocalRing.of_ringEquiv (stalkEquiv A B)
  letI : Algebra B D := Algebra.compHom D (algebraMap B (BaseChange A B))
  letI : IsLocalization.AtPrime D (PhilipponCompletionLocalComparison.closedPrime A B) := by
    change IsLocalization.AtPrime
      ((Spec.structureSheaf (BaseChange A B)).presheaf.stalk
        (PhilipponCompletedBaseChangePoint.point A B))
      (PhilipponCompletedBaseChangePoint.point A B).asIdeal
    infer_instance
  letI : IsScalarTower B (BaseChange A B) D := by
    constructor
    intro b t d
    change (b • t) • d = (algebraMap B (BaseChange A B) b) • (t • d)
    rw [Algebra.smul_def b t]
    exact mul_smul (algebraMap B (BaseChange A B) b) t d
  letI : IsRegularLocalRing (AdicCompletion (maximalIdeal D) D) :=
    (PhilipponCompletionRegularity.regular_iff D).mp inferInstance
  exact PhilipponCompletionLocalAdicIso.regular_of_completed_model A B D _ (RingEquiv.refl _)

end PhilipponCompletedPullbackPoint

end
end

section

set_option autoImplicit false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace


namespace PhilipponBlowupCompletion

instance stalk_flat (X : Scheme.{u}) (x : X) : Flat (X.fromSpecStalk x) := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  letI := TopCat.Presheaf.algebra_section_stalk X.presheaf (⟨x, hxU⟩ : U)
  haveI := hU.isLocalization_stalk (⟨x, hxU⟩ : U)
  have hg : (X.presheaf.germ U x hxU).hom.Flat := by
    change (algebraMap Γ(X, U) (X.presheaf.stalk x)).Flat
    exact RingHom.flat_algebraMap_iff.mpr
      (IsLocalization.flat _ (hU.primeIdealOf ⟨x, hxU⟩).asIdeal.primeCompl)
  haveI : Flat (Spec.map (X.presheaf.germ U x hxU)) := Flat.SpecMap_iff.mpr hg
  rw [← hU.fromSpecStalk_eq_fromSpecStalk hxU, IsAffineOpen.fromSpecStalk]
  infer_instance

abbrev completedRing (X : Scheme.{u}) (x : X) :=
  AdicCompletion (IsLocalRing.maximalIdeal (X.presheaf.stalk x)) (X.presheaf.stalk x)

def toStalk (X : Scheme.{u}) (x : X) :
    Spec (CommRingCat.of (completedRing X x)) ⟶ Spec (X.presheaf.stalk x) :=
  Spec.map (CommRingCat.ofHom (algebraMap (X.presheaf.stalk x) (completedRing X x)))

def toBase (X : Scheme.{u}) (x : X) : Spec (CommRingCat.of (completedRing X x)) ⟶ X :=
  toStalk X x ≫ X.fromSpecStalk x

instance toStalk_flat (X : Scheme.{u}) [IsLocallyNoetherian X] (x : X) : Flat (toStalk X x) := by
  apply Flat.SpecMap_iff.mpr
  exact RingHom.flat_algebraMap_iff.mpr inferInstance

instance toBase_flat (X : Scheme.{u}) [IsLocallyNoetherian X] (x : X) : Flat (toBase X x) := by
  unfold toBase
  infer_instance

end PhilipponBlowupCompletion
end
end

section

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace PhilipponAlterationProjection

/-- A preimmersion into a field spectrum has reduced source, including the empty source. -/
lemma isReduced_of_preimmersion_to_field
    (K : Type u) [Field K] {Z : Scheme.{u}}
    (f : Z ⟶ Spec (.of K)) [IsPreimmersion f] : IsReduced Z := by
  haveI (z : Z) : _root_.IsReduced (Z.presheaf.stalk z) := by
    have hfield : IsField ((Spec (.of K)).presheaf.stalk (f z)) :=
      isField_stalk_of_closure_mem_irreducibleComponents (Spec (.of K)) (f z) (by
        rw [Subsingleton.elim (f z) (genericPoint (Spec (.of K)))]
        simp only [irreducibleComponents_eq_singleton, Set.mem_singleton_iff]
        exact genericPoint_spec (Spec (.of K)))
    letI : Field ((Spec (.of K)).presheaf.stalk (f z)) := hfield.toField
    let e := RingEquiv.ofBijective (f.stalkMap z).hom
      ⟨(f.stalkMap z).hom.injective, f.stalkMap_surjective z⟩
    exact isReduced_of_injective e.symm e.symm.injective
  exact isReduced_of_isReduced_stalk Z

/-- Preimmersions have geometrically reduced fibres. -/
lemma geometricallyReduced_of_preimmersion
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsPreimmersion f] : GeometricallyReduced f := by
  constructor
  intro K _ y Z fst snd h
  haveI : IsPreimmersion snd :=
    MorphismProperty.of_isPullback h (inferInstance : IsPreimmersion f)
  exact isReduced_of_preimmersion_to_field K snd

/-- The canonical map from a local spectrum is flat. -/
lemma flat_fromSpecStalk (X : Scheme.{u}) (x : X) : Flat (X.fromSpecStalk x) := by
  obtain ⟨U, hU, hx, _⟩ := exists_isAffineOpen_mem_and_subset
    (show x ∈ (⊤ : X.Opens) from trivial)
  rw [← hU.fromSpecStalk_eq_fromSpecStalk hx]
  dsimp only [IsAffineOpen.fromSpecStalk]
  haveI : Flat (Spec.map (X.presheaf.germ U x hx)) := by
    apply Flat.SpecMap_iff.mpr
    letI : Algebra Γ(X, U) (X.presheaf.stalk x) := (X.presheaf.germ U x hx).hom.toAlgebra
    letI := hU.isLocalization_stalk ⟨x, hx⟩
    change (algebraMap Γ(X, U) (X.presheaf.stalk x)).Flat
    exact RingHom.flat_algebraMap_iff.mpr
      (IsLocalization.flat (X.presheaf.stalk x) (hU.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl)
  infer_instance

/-- The generic-point residue-field inclusion into an integral scheme is flat. -/
lemma flat_fromSpecResidueField_genericPoint (Y : Scheme.{u}) [IsIntegral Y] :
    Flat (Y.fromSpecResidueField (genericPoint Y)) := by
  have hbij : Function.Bijective (Y.residue (genericPoint Y)) :=
    ⟨(Y.residue (genericPoint Y)).hom.injective, Y.residue_surjective _⟩
  letI : IsIso (Y.residue (genericPoint Y)) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr hbij
  haveI := flat_fromSpecStalk Y (genericPoint Y)
  dsimp only [Scheme.fromSpecResidueField]
  infer_instance

/-- The generic fibre of a morphism between integral schemes is reduced. -/
lemma isReduced_genericFiber
    {X Y : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X] [IsIntegral Y]
    (f : X ⟶ Y) : IsReduced (f.fiber (genericPoint Y)) := by
  letI : Flat (Y.fromSpecResidueField (genericPoint Y)) := flat_fromSpecResidueField_genericPoint Y
  letI : GeometricallyReduced (Y.fromSpecResidueField (genericPoint Y)) :=
    geometricallyReduced_of_preimmersion (Y.fromSpecResidueField (genericPoint Y))
  haveI : Flat (f.fiberι (genericPoint Y)) := by
    dsimp only [Scheme.Hom.fiberι]
    exact MorphismProperty.pullback_fst f (Y.fromSpecResidueField (genericPoint Y))
      (flat_fromSpecResidueField_genericPoint Y)
  haveI : GeometricallyReduced (f.fiberι (genericPoint Y)) := by
    dsimp only [Scheme.Hom.fiberι]
    exact MorphismProperty.pullback_fst f (Y.fromSpecResidueField (genericPoint Y))
      (geometricallyReduced_of_preimmersion (Y.fromSpecResidueField (genericPoint Y)))
  exact GeometricallyReduced.isReduced_of_flat_of_isLocallyNoetherian
    (f.fiberι (genericPoint Y))

/-- A dominant morphism maps the generic point of an integral source to that of its target. -/
lemma genericPoint_eq_of_dominant
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (f : X ⟶ Y) [IsDominant f] : f (genericPoint X) = genericPoint Y := by
  have h := (genericPoint_spec X).image f.continuous
  have hg : IsGenericPoint (f (genericPoint X)) (Set.univ : Set Y) := by
    simpa only [Set.image_univ, f.denseRange.closure_range] using h
  exact hg.eq (genericPoint_spec Y)

/-- The generic fibre of a dominant morphism of integral schemes is irreducible. -/
lemma irreducibleSpace_genericFiber
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (f : X ⟶ Y) [IsDominant f] : IrreducibleSpace (f.fiber (genericPoint Y)) := by
  let z : f.fiber (genericPoint Y) :=
    (f.fiberHomeo (genericPoint Y)).symm
      ⟨genericPoint X, genericPoint_eq_of_dominant f⟩
  have hz : f.fiberι (genericPoint Y) z = genericPoint X :=
    f.fiberι_fiberHomeo_symm (genericPoint Y) _
  have hgen : IsGenericPoint z (Set.univ : Set (f.fiber (genericPoint Y))) := by
    rw [isGenericPoint_iff_specializes]
    intro w
    simp only [Set.mem_univ, iff_true]
    apply (f.fiberι (genericPoint Y)).isEmbedding.isInducing.specializes_iff.mp
    rw [hz]
    exact genericPoint_specializes _
  exact (irreducibleSpace_def _).mpr hgen.isIrreducible

/-- The generic fibre of a dominant morphism of integral schemes is integral. -/
lemma isIntegral_genericFiber
    {X Y : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X] [IsIntegral Y]
    (f : X ⟶ Y) [IsDominant f] : IsIntegral (f.fiber (genericPoint Y)) := by
  letI := isReduced_genericFiber f
  letI := irreducibleSpace_genericFiber f
  exact isIntegral_of_irreducibleSpace_of_isReduced _

end PhilipponAlterationProjection

end

section

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace PhilipponAlterationProjection

/-- A flat preimmersion induces isomorphisms on local rings. -/
lemma isIso_stalkMap_of_flat_preimmersion
    {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f] [IsPreimmersion f] (x : X) :
    IsIso (f.stalkMap x) := by
  letI : Algebra (Y.presheaf.stalk (f x)) (X.presheaf.stalk x) :=
    (f.stalkMap x).hom.toAlgebra
  have : Module.FaithfullyFlat (Y.presheaf.stalk (f x)) (X.presheaf.stalk x) :=
    @Module.FaithfullyFlat.of_flat_of_isLocalHom _ _ _ _ _ _ _
      (Flat.stalkMap f x) (f.toLRSHom.prop x)
  have hff : RingHom.FaithfullyFlat (f.stalkMap x).hom := this
  apply (ConcreteCategory.isIso_iff_bijective _).mpr
  exact ⟨hff.injective, f.stalkMap_surjective x⟩

/-- The generic-fibre inclusion preserves all local rings. -/
lemma isIso_stalkMap_genericFiber
    {X Y : Scheme.{u}} [IsIntegral Y] (f : X ⟶ Y)
    (x : f.fiber (genericPoint Y)) : IsIso ((f.fiberι (genericPoint Y)).stalkMap x) := by
  haveI : Flat (f.fiberι (genericPoint Y)) :=
    MorphismProperty.pullback_fst f (Y.fromSpecResidueField (genericPoint Y))
      (flat_fromSpecResidueField_genericPoint Y)
  exact isIso_stalkMap_of_flat_preimmersion (f.fiberι (genericPoint Y)) x

/-- Normal local rings are retained in the generic fibre. -/
lemma integrallyClosed_stalk_genericFiber
    {X Y : Scheme.{u}} [IsIntegral Y] (f : X ⟶ Y)
    (hnormal : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (z : f.fiber (genericPoint Y)) :
    IsIntegrallyClosed ((f.fiber (genericPoint Y)).presheaf.stalk z) := by
  letI := hnormal (f.fiberι (genericPoint Y) z)
  letI : IsIso ((f.fiberι (genericPoint Y)).stalkMap z) := isIso_stalkMap_genericFiber f z
  exact IsIntegrallyClosed.of_equiv
    (asIso ((f.fiberι (genericPoint Y)).stalkMap z)).commRingCatIsoToRingEquiv

end PhilipponAlterationProjection

end

section

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
noncomputable section

open IsLocalRing AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace PhilipponGlobalCompletedPullback

variable {Y X : Scheme.{u}} [IsLocallyNoetherian X] (f : Y ⟶ X) (y : Y)

abbrev BaseRing := X.presheaf.stalk (f y)
abbrev SourceRing := Y.presheaf.stalk y

local instance localAlgebra : Algebra (BaseRing f y) (SourceRing y) :=
  (f.stalkMap y).hom.toAlgebra

local instance localHom : IsLocalHom (algebraMap (BaseRing f y) (SourceRing y)) :=
  f.toLRSHom.prop y

abbrev localModel : Scheme.{u} :=
  PhilipponCompletedPullbackPoint.model (BaseRing f y) (SourceRing y)

abbrev model : Scheme.{u} :=
  pullback f (PhilipponBlowupCompletion.toBase X (f y))

/-- Restricting the source to its actual local spectrum gives a map
between the actual local and global completed-base-change schemes. -/
def comparison : localModel f y ⟶ model f y :=
  pullback.lift
    (pullback.fst _ _ ≫ Y.fromSpecStalk y)
    (pullback.snd _ _)
    (by
      rw [Category.assoc, ← Scheme.SpecMap_stalkMap_fromSpecStalk]
      change pullback.fst _ _ ≫
        PhilipponCompletedPullbackPoint.originalMap (BaseRing f y) (SourceRing y) ≫
          X.fromSpecStalk (f y) =
        pullback.snd _ _ ≫
          PhilipponCompletedPullbackPoint.completionMap (BaseRing f y) ≫ X.fromSpecStalk (f y)
      rw [← Category.assoc, pullback.condition, Category.assoc])

@[reassoc (attr := simp)]
theorem comparison_fst :
    comparison f y ≫ pullback.fst f (PhilipponBlowupCompletion.toBase X (f y)) =
      pullback.fst _ _ ≫ Y.fromSpecStalk y := pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem comparison_snd :
    comparison f y ≫ pullback.snd f (PhilipponBlowupCompletion.toBase X (f y)) =
      pullback.snd _ _ := pullback.lift_snd _ _ _

/-- The comparison is itself a base change of the actual local-spectrum
inclusion of the source. Monicity of the base local-spectrum inclusion
is what permits the intermediate base to be removed. -/
theorem comparison_isPullback :
    IsPullback (comparison f y) (pullback.fst _ _)
      (pullback.fst f (PhilipponBlowupCompletion.toBase X (f y))) (Y.fromSpecStalk y) := by
  have h := IsPullback.of_isLimit (pullbackIsPullbackOfCompMono
    (PhilipponCompletedPullbackPoint.originalMap (BaseRing f y) (SourceRing y))
    (PhilipponCompletedPullbackPoint.completionMap (BaseRing f y))
    (X.fromSpecStalk (f y)))
  change IsPullback (pullback.fst _ _) (pullback.snd _ _)
    (Spec.map (f.stalkMap y) ≫ X.fromSpecStalk (f y))
    (PhilipponBlowupCompletion.toBase X (f y)) at h
  rw [Scheme.SpecMap_stalkMap_fromSpecStalk] at h
  exact IsPullback.of_right
    (by simpa only [comparison, pullback.lift_snd] using h.flip)
    (comparison_fst f y)
    (IsPullback.of_hasPullback f (PhilipponBlowupCompletion.toBase X (f y))).flip

instance comparison_flat : Flat (comparison f y) :=
  MorphismProperty.of_isPullback (comparison_isPullback f y).flip
    (inferInstance : Flat (Y.fromSpecStalk y))

instance comparison_preimmersion : IsPreimmersion (comparison f y) :=
  MorphismProperty.of_isPullback (comparison_isPullback f y).flip
    (inferInstance : IsPreimmersion (Y.fromSpecStalk y))

instance comparison_stalkMap_isIso (z : localModel f y) :
    IsIso ((comparison f y).stalkMap z) :=
  PhilipponAlterationProjection.isIso_stalkMap_of_flat_preimmersion (comparison f y) z

/-- An actual point of the global completed base change above the given
source point and the closed point of the completed base. -/
def point : model f y :=
  comparison f y (PhilipponCompletedPullbackPoint.point (BaseRing f y) (SourceRing y))

theorem point_to_source :
    pullback.fst f (PhilipponBlowupCompletion.toBase X (f y)) (point f y) = y := by
  change (comparison f y ≫ pullback.fst _ _)
    (PhilipponCompletedPullbackPoint.point (BaseRing f y) (SourceRing y)) = _
  rw [comparison_fst]
  change Y.fromSpecStalk y (pullback.fst
    (PhilipponCompletedPullbackPoint.originalMap (BaseRing f y) (SourceRing y))
    (PhilipponCompletedPullbackPoint.completionMap (BaseRing f y))
    (PhilipponCompletedPullbackPoint.point (BaseRing f y) (SourceRing y))) = y
  rw [PhilipponCompletedPullbackPoint.point_to_original, Scheme.fromSpecStalk_closedPoint]

theorem point_to_completed :
    pullback.snd f (PhilipponBlowupCompletion.toBase X (f y)) (point f y) =
      closedPoint (PhilipponBlowupCompletion.completedRing X (f y)) := by
  change (comparison f y ≫ pullback.snd _ _)
    (PhilipponCompletedPullbackPoint.point (BaseRing f y) (SourceRing y)) = _
  rw [comparison_snd]
  exact PhilipponCompletedPullbackPoint.point_to_completed (BaseRing f y) (SourceRing y)

def stalkEquiv : (model f y).presheaf.stalk (point f y) ≃+*
    (localModel f y).presheaf.stalk
      (PhilipponCompletedPullbackPoint.point (BaseRing f y) (SourceRing y)) :=
  (asIso ((comparison f y).stalkMap
    (PhilipponCompletedPullbackPoint.point (BaseRing f y) (SourceRing y)))).commRingCatIsoToRingEquiv

/-- Regularity at this actual point of the global completed pullback
descends to the original source stalk. -/
theorem regular_of_completed_pullback [IsLocallyNoetherian Y]
    (hreg : IsRegularLocalRing ((model f y).presheaf.stalk (point f y))) :
    IsRegularLocalRing (Y.presheaf.stalk y) := by
  letI := hreg
  apply PhilipponCompletedPullbackPoint.regular_of_pullback (BaseRing f y) (SourceRing y)
  exact IsRegularLocalRing.of_ringEquiv (stalkEquiv f y)

end PhilipponGlobalCompletedPullback

end
end

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits IsLocalRing
theorem solution
    {Y X : Scheme.{u}} [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    (f : Y ⟶ X) (y : Y)
    (hreg : let A := X.presheaf.stalk (f y)
      let C := AdicCompletion (maximalIdeal A) A
      let P := pullback f
        (Spec.map (CommRingCat.ofHom (algebraMap A C)) ≫ X.fromSpecStalk (f y))
      ∀ z : P, IsRegularLocalRing (P.presheaf.stalk z)) :
    IsRegularLocalRing (Y.presheaf.stalk y) := by
  apply PhilipponGlobalCompletedPullback.regular_of_completed_pullback f y
  exact hreg _
#print axioms PhilipponMultiplicity.NoetherianCompletion.exists_powerSeriesMap
#print axioms PhilipponMultiplicity.NoetherianCompletion.powerSeriesMap_surjective
#print axioms PhilipponMultiplicity.NoetherianCompletion.isNoetherianRing_completion
#print axioms PhilipponCompletionRegularity.dimension_eq_of_flat_local_map
#print axioms PhilipponCompletionRegularity.dimension_eq
#print axioms PhilipponCompletionRegularity.regular_iff
#print axioms PhilipponCompletionClosedFiber.approximation
#print axioms PhilipponCompletionClosedFiber.approximation_pow
#print axioms PhilipponCompletionClosedFiber.faithfullyFlat
#print axioms PhilipponCompletionClosedFiber.quotientMap_injective
#print axioms PhilipponCompletionClosedFiber.mapped_maximal_le
#print axioms PhilipponCompletionClosedFiber.mapped_ideal_le
#print axioms PhilipponCompletionClosedFiber.quotientMap_surjective_of_approximation
#print axioms PhilipponCompletionClosedFiber.quotientMap_surjective
#print axioms PhilipponCompletionClosedFiber.quotientMap_surjective_of_power
#print axioms PhilipponCompletionClosedFiber.quotientEquiv
#print axioms PhilipponCompletionClosedFiber.quotientEquivOfPower
#print axioms PhilipponFlatLocalRegularity.exists_sub_mem_maximalIdeal
#print axioms PhilipponFlatLocalRegularity.exists_sub_mem_maximalIdeal_sq
#print axioms PhilipponFlatLocalRegularity.mapCotangent_bijective
#print axioms PhilipponFlatLocalRegularity.spanFinrank_maximalIdeal_eq
#print axioms PhilipponFlatLocalRegularity.regular_iff
#print axioms PhilipponCompletionLocalComparison.closedPrime_isMaximal
#print axioms PhilipponCompletionLocalComparison.maximal_le
#print axioms PhilipponCompletionLocalComparison.map_maximalIdeal
#print axioms PhilipponCompletionLocalComparison.map_isLocalHom
#print axioms PhilipponCompletionLocalComparison.map_flat
#print axioms PhilipponCompletionLocalComparison.residueEquiv
#print axioms PhilipponCompletionLocalComparison.residueEquiv_apply
#print axioms PhilipponCompletionLocalComparison.residueField_map_bijective
#print axioms PhilipponCompletionLocalComparison.regular_iff
#print axioms PhilipponAdicQuotientEquivalence.eval_factor
#print axioms PhilipponAdicQuotientEquivalence.forward_compatible
#print axioms PhilipponAdicQuotientEquivalence.forward
#print axioms PhilipponAdicQuotientEquivalence.eval_forward
#print axioms PhilipponAdicQuotientEquivalence.inverse_compatible
#print axioms PhilipponAdicQuotientEquivalence.equiv
#print axioms PhilipponCompletionLocalAdicIso.power_le
#print axioms PhilipponCompletionLocalAdicIso.quotientEquiv
#print axioms PhilipponCompletionLocalAdicIso.quotientEquiv_apply_mk
#print axioms PhilipponCompletionLocalAdicIso.compatible
#print axioms PhilipponCompletionLocalAdicIso.completionIso
#print axioms PhilipponCompletionLocalAdicIso.eval_completionIso
#print axioms PhilipponCompletionLocalAdicIso.completionIso_algebraMap
#print axioms PhilipponCompletionLocalAdicIso.regular_of_completed_model
#print axioms PhilipponCompletedBaseChangePoint.point_to_original
#print axioms PhilipponCompletedBaseChangePoint.completed_comap
#print axioms PhilipponCompletedBaseChangePoint.point_to_completed
#print axioms PhilipponCompletedBaseChangePoint.completionIso
#print axioms PhilipponCompletedPullbackPoint.tensorIso
#print axioms PhilipponCompletedPullbackPoint.point_to_original
#print axioms PhilipponCompletedPullbackPoint.point_to_completed
#print axioms PhilipponCompletedPullbackPoint.stalkEquiv
#print axioms PhilipponCompletedPullbackPoint.regular_of_pullback
#print axioms PhilipponBlowupCompletion.stalk_flat
#print axioms PhilipponBlowupCompletion.toBase_flat
#print axioms PhilipponAlterationProjection.isReduced_of_preimmersion_to_field
#print axioms PhilipponAlterationProjection.geometricallyReduced_of_preimmersion
#print axioms PhilipponAlterationProjection.flat_fromSpecStalk
#print axioms PhilipponAlterationProjection.flat_fromSpecResidueField_genericPoint
#print axioms PhilipponAlterationProjection.isReduced_genericFiber
#print axioms PhilipponAlterationProjection.genericPoint_eq_of_dominant
#print axioms PhilipponAlterationProjection.irreducibleSpace_genericFiber
#print axioms PhilipponAlterationProjection.isIntegral_genericFiber
#print axioms PhilipponAlterationProjection.isIso_stalkMap_of_flat_preimmersion
#print axioms PhilipponAlterationProjection.isIso_stalkMap_genericFiber
#print axioms PhilipponAlterationProjection.integrallyClosed_stalk_genericFiber
#print axioms PhilipponGlobalCompletedPullback.comparison_isPullback
#print axioms PhilipponGlobalCompletedPullback.comparison_flat
#print axioms PhilipponGlobalCompletedPullback.comparison_preimmersion
#print axioms PhilipponGlobalCompletedPullback.comparison_stalkMap_isIso
#print axioms PhilipponGlobalCompletedPullback.point_to_source
#print axioms PhilipponGlobalCompletedPullback.point_to_completed
#print axioms PhilipponGlobalCompletedPullback.stalkEquiv
#print axioms PhilipponGlobalCompletedPullback.regular_of_completed_pullback
#print axioms solution
