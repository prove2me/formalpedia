-- Prove2me | solution 1 for AlgebraicCurve.TwoChartIntegralModel.exists_valuationSubring_forall_mem_nonunits_mem_asIdeal_of_mem_toBase
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/a2e2c2f1-f6d3-57b3-baa2-6e3ac85786e9

import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_exists_valuationSubring_of_mem_minimalPrimes_chartAlgFin
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_TwoChartIntegralModel_exists_valuationSubring_forall_mem_nonunits_mem_asIdeal_of_mem_toBase

set_option autoImplicit false

universe u

namespace OnCompAux

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve AlgebraicCurve.TwoChartIntegralModel IsLocalRing

section Overlap

variable (R : Type u) [CommRing R] (F : Type u) [Field F] [Algebra R F] (j : F) [Fact (j ≠ 0)]

theorem exists_mid_of_ιFin_eq_ιInf (y : XFin R F j) (y' : XInf R F j)
    (h : (ιFin R F j).base y = (ιInf R F j).base y') :
    ∃ z : XMid R F j, (fFin R F j).base z = y ∧ (fInf R F j).base z = y' := by
  have h' : (colimit.ι (span (fFin R F j) (fInf R F j)) WalkingSpan.left).base y =
      (colimit.ι (span (fFin R F j) (fInf R F j)) WalkingSpan.right).base y' := h
  obtain ⟨k, fi, fj, z, h1, h2⟩ := (Scheme.IsLocallyDirected.ι_eq_ι_iff _).1 h'
  rcases k with (_ | _ | _)
  · have hfi : fi = WalkingSpan.Hom.fst := Subsingleton.elim _ _
    have hfj : fj = WalkingSpan.Hom.snd := Subsingleton.elim _ _
    subst hfi hfj
    exact ⟨z, h1, h2⟩
  · exact nomatch fj
  · exact nomatch fi

theorem exists_comap_eq_of_ιFin_eq_ιInf (y : XFin R F j) (y' : XInf R F j)
    (h : (ιFin R F j).base y = (ιInf R F j).base y') :
    ∃ z : XMid R F j, y.asIdeal = Ideal.comap (inclFin R F j).toRingHom z.asIdeal ∧
      y'.asIdeal = Ideal.comap (inclInf R F j).toRingHom z.asIdeal := by
  obtain ⟨z, h1, h2⟩ := exists_mid_of_ιFin_eq_ιInf R F j y y' h
  exact ⟨z, by rw [← h1]; rfl, by rw [← h2]; rfl⟩

theorem jInvChartInf_mem_of_not_mem_range (y' : XInf R F j)
    (hx : (ιInf R F j).base y' ∉ Set.range (ιFin R F j).base) :
    jInvChartInf R F j ∈ y'.asIdeal := by
  by_contra hj
  letI : Algebra (chartAlgInf R F j) (chartAlgMid R F j) := (inclInf R F j).toRingHom.toAlgebra
  haveI : IsLocalization.Away (jInvChartInf R F j) (chartAlgMid R F j) :=
    isLocalization_away_inclInf R F j
  have hdisj : Disjoint (↑(Submonoid.powers (jInvChartInf R F j)) : Set (chartAlgInf R F j))
      (↑y'.asIdeal : Set (chartAlgInf R F j)) := by
    rw [Set.disjoint_left]
    rintro _ ⟨n, rfl⟩ hn
    exact hj (y'.isPrime.mem_of_pow_mem n hn)
  have hmem : y' ∈ Set.range (PrimeSpectrum.comap
      (algebraMap (chartAlgInf R F j) (chartAlgMid R F j))) := by
    rw [PrimeSpectrum.localization_comap_range (chartAlgMid R F j)
      (Submonoid.powers (jInvChartInf R F j))]
    exact hdisj
  obtain ⟨z, hz⟩ := hmem
  apply hx
  have hglue : (ιFin R F j).base ((fFin R F j).base z) = (ιInf R F j).base ((fInf R F j).base z) :=
    congrArg (fun f => f.base z) (glue_condition R F j)
  refine ⟨(fFin R F j).base z, hglue.trans ?_⟩
  show (ιInf R F j).base (PrimeSpectrum.comap (inclInf R F j).toRingHom z) = _
  rw [← hz]
  rfl

theorem exists_inf_witness (z : XMid R F j) (b : chartAlgFin R F j) :
    ∃ (n : ℕ) (g : chartAlgInf R F j),
      (b : F) * ((jInvChartInf R F j ^ n : chartAlgInf R F j) : F) = (g : F) ∧
      jInvChartInf R F j ^ n ∉ Ideal.comap (inclInf R F j).toRingHom z.asIdeal ∧
      (b ∈ Ideal.comap (inclFin R F j).toRingHom z.asIdeal ↔
        g ∈ Ideal.comap (inclInf R F j).toRingHom z.asIdeal) := by
  have hj0 : j ≠ 0 := Fact.out
  have hb : (b : F) ∈ chartAlg R F (insert j⁻¹⁻¹ {j⁻¹}) := by
    rw [inv_inv]
    exact chartAlg_mono R F (Set.singleton_subset_iff.2 (Set.mem_insert j _)) b.2
  obtain ⟨n, hn⟩ := exists_pow_mul_mem_chartAlg (Set.mem_singleton j⁻¹) (inv_ne_zero hj0) hb
  have hu : IsUnit (inclInf R F j (jInvChartInf R F j) ^ n) := (isUnit_inclInf_jInvChartInf R F j).pow n
  have e1 : ∀ x, (inclInf R F j).toRingHom x = inclInf R F j x := fun _ => rfl
  have e2 : ∀ x, (inclFin R F j).toRingHom x = inclFin R F j x := fun _ => rfl
  refine ⟨n, ⟨j⁻¹ ^ n * b, hn⟩, ?_, ?_, ?_⟩
  · rw [Subalgebra.coe_pow, coe_jInvChartInf]
    ring
  · intro hmem
    rw [Ideal.mem_comap, e1, map_pow] at hmem
    exact z.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ hmem hu)
  · rw [Ideal.mem_comap, Ideal.mem_comap, e1, e2]
    have hprod : inclInf R F j ⟨j⁻¹ ^ n * b, hn⟩ =
        inclInf R F j (jInvChartInf R F j) ^ n * inclFin R F j b := by
      apply Subtype.ext
      rw [Subalgebra.coe_mul, Subalgebra.coe_pow, coe_chartIncl, coe_chartIncl, coe_chartIncl,
        coe_jInvChartInf]
    rw [hprod, Ideal.unit_mul_mem_iff_mem _ hu]

end Overlap

section FinWitness

variable (R : Type u) [CommRing R] (F : Type u) [Field F] [Algebra R F] (j : F) [Fact (j ≠ 0)]

theorem exists_fin_witness (z : XMid R F j) (b : chartAlgInf R F j) :
    ∃ (n : ℕ) (g : chartAlgFin R F j),
      (b : F) * ((jChartFin R F j ^ n : chartAlgFin R F j) : F) = (g : F) ∧
      jChartFin R F j ^ n ∉ Ideal.comap (inclFin R F j).toRingHom z.asIdeal ∧
      (b ∈ Ideal.comap (inclInf R F j).toRingHom z.asIdeal ↔
        g ∈ Ideal.comap (inclFin R F j).toRingHom z.asIdeal) := by
  have hj0 : j ≠ 0 := Fact.out
  have hb : (b : F) ∈ chartAlg R F (insert j⁻¹ {j}) :=
    chartAlg_mono R F (Set.singleton_subset_iff.2 (Set.mem_insert j⁻¹ _)) b.2
  obtain ⟨n, hn⟩ := exists_pow_mul_mem_chartAlg (Set.mem_singleton j) hj0 hb
  have hu : IsUnit (inclFin R F j (jChartFin R F j) ^ n) := (isUnit_inclFin_jChartFin R F j).pow n
  have e1 : ∀ x, (inclInf R F j).toRingHom x = inclInf R F j x := fun _ => rfl
  have e2 : ∀ x, (inclFin R F j).toRingHom x = inclFin R F j x := fun _ => rfl
  refine ⟨n, ⟨j ^ n * b, hn⟩, ?_, ?_, ?_⟩
  · rw [Subalgebra.coe_pow, coe_jChartFin]
    ring
  · intro hmem
    rw [Ideal.mem_comap, e2, map_pow] at hmem
    exact z.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ hmem hu)
  · rw [Ideal.mem_comap, Ideal.mem_comap, e1, e2]
    have hprod : inclFin R F j ⟨j ^ n * b, hn⟩ =
        inclFin R F j (jChartFin R F j) ^ n * inclInf R F j b := by
      apply Subtype.ext
      rw [Subalgebra.coe_mul, Subalgebra.coe_pow, coe_chartIncl, coe_chartIncl, coe_chartIncl,
        coe_jChartFin]
    rw [hprod, Ideal.unit_mul_mem_iff_mem _ hu]

end FinWitness

section Valuation

theorem chartAlg_singleton_le_valuationSubring
    {F : Type u} [Field F] {T : Type u} [Field T] {A₁ : Type u} [CommRing A₁] [Algebra A₁ T]
    (emb : T →+* F) (O : ValuationSubring F) (t : T)
    (ht : emb t ∈ O) (hconst : ∀ a : A₁, emb (algebraMap A₁ T a) ∈ O) :
    ∀ c, c ∈ AlgebraicCurve.TwoChartIntegralModel.chartAlg A₁ T {t} → emb c ∈ O := by
  intro c hc
  let S' : Subalgebra A₁ T :=
    { carrier := {x | emb x ∈ O}
      mul_mem' := fun {a b} ha hb => by
        simp only [Set.mem_setOf_eq, map_mul]; exact mul_mem ha hb
      one_mem' := by simp only [Set.mem_setOf_eq, map_one]; exact one_mem O
      add_mem' := fun {a b} ha hb => by
        simp only [Set.mem_setOf_eq, map_add]; exact add_mem ha hb
      zero_mem' := by simp only [Set.mem_setOf_eq, map_zero]; exact zero_mem O
      algebraMap_mem' := hconst }
  have hadj : Algebra.adjoin A₁ ({t} : Set T) ≤ S' := Algebra.adjoin_le (Set.singleton_subset_iff.2 ht)
  let ψ : ↥(Algebra.adjoin A₁ ({t} : Set T)) →+* ↥O :=
    (emb.comp (Algebra.adjoin A₁ ({t} : Set T)).val.toRingHom).codRestrict O (fun s => hadj s.2)
  have hcint : IsIntegral ↥(Algebra.adjoin A₁ ({t} : Set T)) c :=
    (AlgebraicCurve.TwoChartIntegralModel.mem_chartAlg_iff A₁ T).1 hc
  have hint : IsIntegral ↥O (emb c) :=
    hcint.map_of_comp_eq ψ emb (RingHom.ext fun _ => rfl)
  obtain ⟨y, hy⟩ := (IsIntegrallyClosedIn.isIntegral_iff (R := ↥O) (A := F)).1 hint
  rw [← hy]
  exact y.2

theorem gauss_inv {R : Type u} [CommRing R] {F : Type u} [Field F] [Algebra R F]
    (V : ValuationSubring F) (ϖ : R) (j : F) (hj0 : j ≠ 0) (hjV : j ∈ V) (hjiV : j⁻¹ ∈ V)
    (h : ∀ P : Polynomial R, ¬ (Polynomial.C ϖ ∣ P) →
      Polynomial.aeval j⁻¹ P ∈ V ∧ (Polynomial.aeval j⁻¹ P)⁻¹ ∈ V) :
    ∀ P : Polynomial R, ¬ (Polynomial.C ϖ ∣ P) →
      Polynomial.aeval j P ∈ V ∧ (Polynomial.aeval j P)⁻¹ ∈ V := by
  intro P hP

  have hrev : ¬ (Polynomial.C ϖ ∣ P.reverse) := by
    intro hd
    apply hP
    rw [Polynomial.C_dvd_iff_dvd_coeff] at hd ⊢
    intro i
    by_cases hi : i ≤ P.natDegree
    · have := hd (P.natDegree - i)
      rwa [Polynomial.coeff_reverse, Polynomial.revAt_le (Nat.sub_le _ _),
        Nat.sub_sub_self hi] at this
    · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (not_le.1 hi)]
      exact dvd_zero _
  obtain ⟨h1, h2⟩ := h P.reverse hrev
  haveI : Invertible j := invertibleOfNonzero hj0
  have key : Polynomial.aeval j P = Polynomial.aeval j⁻¹ P.reverse * j ^ P.natDegree := by
    rw [Polynomial.aeval_def, Polynomial.aeval_def, Polynomial.reverse, ← invOf_eq_inv,
      Polynomial.eval₂_reflect_mul_pow _ _ _ _ le_rfl]
  refine ⟨?_, ?_⟩
  · rw [key]; exact mul_mem h1 (pow_mem hjV _)
  · rw [key, mul_inv, ← inv_pow]; exact mul_mem h2 (pow_mem hjiV _)

end Valuation

section Main

variable (R : Type u) [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    (K₀ : Type u) [Field K₀] [Algebra R K₀] [IsFractionRing R K₀]
    (F : Type u) [Field F] [Algebra R F] [Algebra K₀ F] [IsScalarTower R K₀ F]
    (j : F) [Fact (j ≠ 0)]

theorem exists_valuationSubring_of_mem (t : F) [Fact (t ≠ 0)] (htt : Transcendental R t)
    (hFD : FiniteDimensional ↥(IntermediateField.adjoin K₀ ({t} : Set F)) F)
    (hsep : Algebra.IsSeparable ↥(IntermediateField.adjoin K₀ ({t} : Set F)) F)
    (ϖ : R) (hϖ : Prime ϖ) (y : Ideal ↥(chartAlgFin R F t)) [y.IsPrime]
    (hy : algebraMap R ↥(chartAlgFin R F t) ϖ ∈ y) :
    ∃ V : ValuationSubring F,
      IsDiscreteValuationRing ↥V ∧
      (∀ f : ↥(chartAlgFin R F t), (f : F) ∈ V) ∧
      (∀ f : ↥(chartAlgFin R F t), (f : F) ∈ V.nonunits → f ∈ y) ∧
      algebraMap R F ϖ ∈ V.nonunits ∧
      (∀ P : Polynomial R, ¬ (Polynomial.C ϖ ∣ P) →
        Polynomial.aeval t P ∈ V ∧ (Polynomial.aeval t P)⁻¹ ∈ V) := by
  obtain ⟨𝔭, h𝔭, h𝔭y⟩ := Ideal.exists_minimalPrimes_le (J := y) ((Ideal.span_singleton_le_iff_mem _).2 hy)
  obtain ⟨V, hdvr, hsub, hcen, hϖV, hG⟩ :=
    AlgebraicCurve.TwoChartIntegralModel.exists_valuationSubring_of_mem_minimalPrimes_chartAlgFin
      R K₀ F t htt hFD hsep ϖ hϖ 𝔭 h𝔭
  exact ⟨V, hdvr, hsub, fun f hf => h𝔭y ((hcen f).2 hf), hϖV, hG⟩

theorem exists_valuationSubring_branch (htj : Transcendental R j)
    (hFD : FiniteDimensional ↥(IntermediateField.adjoin K₀ ({j} : Set F)) F)
    (hsep : Algebra.IsSeparable ↥(IntermediateField.adjoin K₀ ({j} : Set F)) F)
    (ϖ : R) (hϖ : Prime ϖ)
    (x : ↥(AlgebraicCurve.TwoChartIntegralModel R F j)) (hx : ϖ ∈ ((toBase R F j).base x).asIdeal) :
    ∃ V : ValuationSubring F,
      IsDiscreteValuationRing ↥V ∧
      (∀ f : ↥(chartAlgFin R F j), (f : F) ∈ V) ∧
      (∀ f : ↥(chartAlgInf R F j), (f : F) ∈ V) ∧
      algebraMap R F ϖ ∈ V.nonunits ∧
      (∀ P : Polynomial R, ¬ (Polynomial.C ϖ ∣ P) →
        Polynomial.aeval j P ∈ V ∧ (Polynomial.aeval j P)⁻¹ ∈ V) ∧
      (∀ y : ↥(XFin R F j), (ιFin R F j).base y = x →
        ∀ b : ↥(chartAlgFin R F j), (b : F) ∈ V.nonunits → b ∈ y.asIdeal) ∧
      (∀ y : ↥(XInf R F j), (ιInf R F j).base y = x →
        ∀ b : ↥(chartAlgInf R F j), (b : F) ∈ V.nonunits → b ∈ y.asIdeal) := by
  have hj0 : j ≠ 0 := Fact.out
  have hX : ¬ (Polynomial.C ϖ ∣ (Polynomial.X : Polynomial R)) := by
    intro hd
    have := (Polynomial.C_dvd_iff_dvd_coeff _ _).1 hd 1
    rw [Polynomial.coeff_X_one] at this
    exact hϖ.not_unit (isUnit_of_dvd_one this)
  have hRV : ∀ (V : ValuationSubring F), (∀ f : ↥(chartAlgFin R F j), (f : F) ∈ V) →
      ∀ a : R, (RingHom.id F) (algebraMap R F a) ∈ V := fun V h a => h ⟨algebraMap R F a, Subalgebra.algebraMap_mem _ a⟩
  have hRV' : ∀ (V : ValuationSubring F), (∀ f : ↥(chartAlgInf R F j), (f : F) ∈ V) →
      ∀ a : R, (RingHom.id F) (algebraMap R F a) ∈ V := fun V h a => h ⟨algebraMap R F a, Subalgebra.algebraMap_mem _ a⟩
  rcases em (x ∈ Set.range (ιFin R F j).base) with ⟨y₀, hy₀⟩ | hxFin
  ·
    subst hy₀
    have hyϖ : algebraMap R ↥(chartAlgFin R F j) ϖ ∈ y₀.asIdeal := by
      have h := congrArg (fun f : XFin R F j ⟶ Spec (CommRingCat.of R) => (f.base y₀).asIdeal) (ιFin_toBase R F j)
      simp only [Scheme.Hom.comp_base, TopCat.comp_app] at h
      rw [h] at hx
      exact hx
    obtain ⟨V, hdvr, hsub, hcen, hϖV, hG⟩ :=
      exists_valuationSubring_of_mem R K₀ F j htj hFD hsep ϖ hϖ y₀.asIdeal hyϖ
    have hjV : j ∈ V := by simpa [Polynomial.aeval_def] using (hG Polynomial.X hX).1
    have hjiV : j⁻¹ ∈ V := by simpa [Polynomial.aeval_def] using (hG Polynomial.X hX).2
    have hsubI : ∀ f : ↥(chartAlgInf R F j), (f : F) ∈ V := fun f =>
      chartAlg_singleton_le_valuationSubring (RingHom.id F) V j⁻¹ hjiV (hRV V hsub) f f.2
    refine ⟨V, hdvr, hsub, hsubI, hϖV, hG, ?_, ?_⟩
    · intro y hy b hb
      have hyy : y = y₀ := (ιFin R F j).isOpenEmbedding.injective hy
      subst hyy
      exact hcen b hb
    · intro y' hy' b hb
      obtain ⟨z, hzy, hzy'⟩ := exists_comap_eq_of_ιFin_eq_ιInf R F j y₀ y' hy'.symm
      obtain ⟨n, g, hbg, -, hiff⟩ := exists_fin_witness R F j z b
      rw [hzy']
      apply hiff.2
      rw [← hzy]
      apply hcen
      rw [← hbg]
      rw [ValuationSubring.mem_nonunits_iff] at hb ⊢
      rw [map_mul]
      calc V.valuation (b : F) * V.valuation ((jChartFin R F j ^ n : ↥(chartAlgFin R F j)) : F)
          ≤ V.valuation (b : F) * 1 := mul_le_mul_right ((V.valuation_le_one_iff _).2 (hsub _)) _
        _ = V.valuation (b : F) := mul_one _
        _ < 1 := hb
  ·
    obtain ⟨y₀, hy₀⟩ : ∃ y₀ : ↥(XInf R F j), (ιInf R F j).base y₀ = x := by
      rcases mem_range_ιFin_or_mem_range_ιInf R F j x with h | ⟨y₀, h⟩
      · exact absurd h hxFin
      · exact ⟨y₀, h⟩
    subst hy₀
    have hyϖ : algebraMap R ↥(chartAlgInf R F j) ϖ ∈ y₀.asIdeal := by
      have h := congrArg (fun f : XInf R F j ⟶ Spec (CommRingCat.of R) => (f.base y₀).asIdeal) (ιInf_toBase R F j)
      simp only [Scheme.Hom.comp_base, TopCat.comp_app] at h
      rw [h] at hx
      exact hx
    haveI : Fact (j⁻¹ ≠ 0) := ⟨inv_ne_zero hj0⟩
    have htj' : Transcendental R j⁻¹ := fun h => htj (IsAlgebraic.inv_iff.1 h)
    have hadj : IntermediateField.adjoin K₀ ({j⁻¹} : Set F) = IntermediateField.adjoin K₀ ({j} : Set F) := by
      apply le_antisymm
      · rw [IntermediateField.adjoin_simple_le_iff]
        exact inv_mem (IntermediateField.mem_adjoin_simple_self K₀ j)
      · rw [IntermediateField.adjoin_simple_le_iff]
        have := inv_mem (IntermediateField.mem_adjoin_simple_self K₀ j⁻¹)
        rwa [inv_inv] at this
    have hFD' : FiniteDimensional ↥(IntermediateField.adjoin K₀ ({j⁻¹} : Set F)) F := by rw [hadj]; exact hFD
    have hsep' : Algebra.IsSeparable ↥(IntermediateField.adjoin K₀ ({j⁻¹} : Set F)) F := by rw [hadj]; exact hsep
    obtain ⟨V, hdvr, hsubI, hcen, hϖV, hG'⟩ :=
      exists_valuationSubring_of_mem R K₀ F j⁻¹ htj' hFD' hsep' ϖ hϖ y₀.asIdeal hyϖ
    have hjiV : j⁻¹ ∈ V := by simpa [Polynomial.aeval_def] using (hG' Polynomial.X hX).1
    have hjV : j ∈ V := by simpa [Polynomial.aeval_def] using (hG' Polynomial.X hX).2
    have hsub : ∀ f : ↥(chartAlgFin R F j), (f : F) ∈ V := fun f =>
      chartAlg_singleton_le_valuationSubring (RingHom.id F) V j hjV (hRV' V hsubI) f f.2
    refine ⟨V, hdvr, hsub, hsubI, hϖV, gauss_inv V ϖ j hj0 hjV hjiV hG', ?_, ?_⟩
    · intro y hy; exact absurd ⟨y, hy⟩ hxFin
    · intro y hy b hb
      have hyy : y = y₀ := (ιInf R F j).isOpenEmbedding.injective hy
      subst hyy
      exact hcen b hb

end Main

end OnCompAux

theorem solution
    (R : Type u) [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    (K₀ : Type u) [Field K₀] [Algebra R K₀] [IsFractionRing R K₀]
    (F : Type u) [Field F] [Algebra R F] [Algebra K₀ F] [IsScalarTower R K₀ F]
    (j : F) [Fact (j ≠ 0)] (htj : Transcendental R j)
    (hFD : FiniteDimensional ↥(IntermediateField.adjoin K₀ ({j} : Set F)) F)
    (hsep : Algebra.IsSeparable ↥(IntermediateField.adjoin K₀ ({j} : Set F)) F)
    (ϖ : R) (hϖ : Prime ϖ)
    (x : ↥(AlgebraicCurve.TwoChartIntegralModel R F j))
    (hx : ϖ ∈ ((AlgebraicCurve.TwoChartIntegralModel.toBase R F j).base x).asIdeal) :
    ∃ V : ValuationSubring F,
      IsDiscreteValuationRing ↥V ∧
      (∀ f : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin R F j), (f : F) ∈ V) ∧
      (∀ f : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf R F j), (f : F) ∈ V) ∧
      algebraMap R F ϖ ∈ V.nonunits ∧
      (∀ P : Polynomial R, ¬ (Polynomial.C ϖ ∣ P) →
        Polynomial.aeval j P ∈ V ∧ (Polynomial.aeval j P)⁻¹ ∈ V) ∧
      (∀ y : ↥(AlgebraicCurve.TwoChartIntegralModel.XFin R F j), (AlgebraicCurve.TwoChartIntegralModel.ιFin R F j).base y = x →
        ∀ b : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin R F j), (b : F) ∈ V.nonunits → b ∈ y.asIdeal) ∧
      (∀ y : ↥(AlgebraicCurve.TwoChartIntegralModel.XInf R F j), (AlgebraicCurve.TwoChartIntegralModel.ιInf R F j).base y = x →
        ∀ b : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf R F j), (b : F) ∈ V.nonunits → b ∈ y.asIdeal) :=
  OnCompAux.exists_valuationSubring_branch R K₀ F j htj hFD hsep ϖ hϖ x hx

end S_AlgebraicCurve_TwoChartIntegralModel_exists_valuationSubring_forall_mem_nonunits_mem_asIdeal_of_mem_toBase
end P2MW
export P2MW.S_AlgebraicCurve_TwoChartIntegralModel_exists_valuationSubring_forall_mem_nonunits_mem_asIdeal_of_mem_toBase (solution)
