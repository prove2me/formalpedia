-- Prove2me | Definitions.Def_ReciprocityTheory_NeutralLocalFields_LocalFieldComparison_LocalFieldAutomorphisms_ExistsApplyEqOfMemDec
-- name    : ReciprocityTheory_NeutralLocalFields_LocalFieldComparison_LocalFieldAutomorphisms_ExistsApplyEqOfMemDec
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-25T16:42:05.27301+00:00
-- url     : https://prove2.me/theorems/a7cb01af-665f-5683-b229-b687f3a8d577
-- title:
--   Exists Apply Eq Of Mem Dec
-- statement:
--   Definitions and structural lemmas for Exists Apply Eq Of Mem Dec, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/NeutralLocalFields/LocalFieldComparison/LocalFieldAutomorphisms/ExistsApplyEqOfMemDec.lean

import Definitions.Def_ReciprocityTheory_NeutralLocalFields_LocalFieldComparison_LocalFieldAutomorphisms_ContinuousGK
import Theorems.Thm_ReciprocityTheory_Neutral_Cmp_continuous_res
import Theorems.Thm_ReciprocityTheory_Neutral_Cmp_isAlgClosure_Kloc
import Theorems.Thm_ReciprocityTheory_Neutral_Cmp_res_injective
import Theorems.Thm_ReciprocityTheory_Neutral_Cmp_res_mem_dec
import Theorems.Thm_ReciprocityTheory_Neutral_Cmp_res_spec

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace ReciprocityTheory.Neutral.Cmp
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain
variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {p : ℕ} [Fact p.Prime]
theorem norm_natCast_padicAlgCl : ‖((p : ℕ) : PadicAlgCl p)‖ = (p : ℝ)⁻¹ := by
  first
  | (rw [← map_natCast (algebraMap ℚ_[p] (PadicAlgCl p)) p, norm_algebraMap', Padic.norm_p])
  | (rw [← map_natCast (algebraMap ℚ_[p] (PadicAlgCl p)) p, PadicAlgCl.norm_extends, Padic.norm_p])
  | (have h1 := PadicAlgCl.norm_extends p (p : ℚ_[p]); rw [map_natCast] at h1; rw [h1, Padic.norm_p])
  | simp [Padic.norm_p]
theorem norm_apply_le_of_mem_dec {A : ValuationSubring Ω} {ι : Ω →+* PadicAlgCl p} (h : Compat p A ι) {τ : Ω ≃ₐ[F] Ω}
    (hτ : τ ∈ Dec (F := F) A) (x : Ω) : ‖ι (τ x)‖ ≤ ‖ι x‖ := by
  have hs : ∀ y ∈ A, τ y ∈ A := by
    intro y hy
    have h2 := ValuationSubring.smul_mem_pointwise_smul τ y A hy
    letI : MulAction (Ω ≃ₐ[F] Ω) (ValuationSubring Ω) := ValuationSubring.pointwiseMulAction
    have hsA := MulAction.mem_stabilizer_iff.mp hτ
    first
    | (rw [hsA] at h2; exact h2)
    | exact hsA ▸ h2
    | (simp only [hsA] at h2; exact h2)
    | (erw [hsA] at h2; exact h2)
  have key : ∀ y, ‖ι y‖ ≤ 1 → ‖ι (τ y)‖ ≤ 1 := fun y hy => (h (τ y)).1 (hs y ((h y).2 hy))
  by_contra hlt
  push_neg at hlt
  have hc : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have hpa : (0 : ℝ) < p := by linarith
  have ha : 0 < ‖ι x‖ := by
    rcases (norm_nonneg (ι x)).lt_or_eq with h0 | h0
    · exact h0
    · exfalso
      have h1 : ι x = 0 := norm_eq_zero.mp h0.symm
      have hx : x = 0 := (map_eq_zero ι).mp h1
      subst hx
      simp at hlt
  have hr : 1 < ‖ι (τ x)‖ / ‖ι x‖ := (one_lt_div ha).mpr hlt
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (p : ℝ) hr
  obtain ⟨m, hm1, hm2⟩ := exists_mem_Ico_zpow (pow_pos ha n) hc
  have hbn : (p : ℝ) * ‖ι x‖ ^ n < ‖ι (τ x)‖ ^ n := by
    rw [div_pow] at hn
    first
    | exact (lt_div_iff₀ (pow_pos ha n)).mp hn
    | exact (lt_div_iff (pow_pos ha n)).mp hn
  have h3 : (p : ℝ) ^ (m + 1) < ‖ι (τ x)‖ ^ n := by
    rw [zpow_add_one₀ hpa.ne']
    calc (p : ℝ) ^ m * p ≤ ‖ι x‖ ^ n * p := mul_le_mul_of_nonneg_right hm1 hpa.le
      _ = p * ‖ι x‖ ^ n := mul_comm _ _
      _ < ‖ι (τ x)‖ ^ n := hbn
  have hz : (0 : ℝ) < (p : ℝ) ^ (m + 1) := by
    first
    | exact zpow_pos hpa _
    | exact zpow_pos_of_pos hpa _
  have hk := key (x ^ n * (p : Ω) ^ (m + 1)) (by
    simp only [map_mul, map_pow, map_zpow₀, map_natCast, norm_mul, norm_pow, norm_zpow,
      norm_natCast_padicAlgCl, inv_zpow]
    rw [← div_eq_mul_inv, div_le_one hz]
    exact hm2.le)
  simp only [map_mul, map_pow, map_zpow₀, map_natCast, norm_mul, norm_pow, norm_zpow,
    norm_natCast_padicAlgCl, inv_zpow] at hk
  rw [← div_eq_mul_inv, div_le_one hz] at hk
  linarith
theorem norm_apply_of_mem_dec {A : ValuationSubring Ω} {ι : Ω →+* PadicAlgCl p} (h : Compat p A ι) {τ : Ω ≃ₐ[F] Ω}
    (hτ : τ ∈ Dec (F := F) A) (x : Ω) : ‖ι (τ x)‖ = ‖ι x‖ := by
  refine le_antisymm (norm_apply_le_of_mem_dec h hτ x) ?_
  have h1 := norm_apply_le_of_mem_dec (τ := τ⁻¹) h (inv_mem hτ) (τ x)
  have e : τ⁻¹ (τ x) = x := by
    first
    | exact τ.symm_apply_apply x
    | (rw [← AlgEquiv.mul_apply, inv_mul_cancel, AlgEquiv.one_apply])
    | simp
  rwa [e] at h1
theorem norm_sum_mul_pow_le (n : ℕ) (u : ℕ → PadicAlgCl p) (z : PadicAlgCl p) {δ : ℝ} (hu : ∀ i, ‖u i‖ ≤ δ) :
    ‖∑ i ∈ Finset.range n, u i * z ^ i‖ ≤ δ * ∑ i ∈ Finset.range n, ‖z‖ ^ i := by
  calc ‖∑ i ∈ Finset.range n, u i * z ^ i‖ ≤ ∑ i ∈ Finset.range n, ‖u i * z ^ i‖ := norm_sum_le _ _
    _ ≤ ∑ i ∈ Finset.range n, δ * ‖z‖ ^ i := by
        apply Finset.sum_le_sum
        intro i _
        rw [norm_mul, norm_pow]
        exact mul_le_mul_of_nonneg_right (hu i) (pow_nonneg (norm_nonneg _) _)
    _ = δ * ∑ i ∈ Finset.range n, ‖z‖ ^ i := by rw [Finset.mul_sum]
theorem minpoly_aeval_of_mem_dec {A : ValuationSubring Ω} {ι : Ω →+* PadicAlgCl p} (h : Compat p A ι) {τ : Ω ≃ₐ[F] Ω}
    (hτ : τ ∈ Dec (F := F) A) (x : Ω) : Polynomial.aeval (ι (τ x)) (minpoly (Kloc F ι) (ι x)) = 0 := by
  classical
  have hdense : ∀ c : PadicAlgCl p, c ∈ Kloc F ι → ∀ δ : ℝ, 0 < δ →
      ∃ f : F, ‖c - ι (algebraMap F Ω f)‖ < δ := by
    intro c hc δ hδ
    let R : Subring (PadicAlgCl p) := (ι.comp (algebraMap F Ω)).range
    have hQ : ∀ a : ℚ_[p], algebraMap ℚ_[p] (PadicAlgCl p) a ∈ R.topologicalClosure := by
      intro a
      show _ ∈ closure (R : Set (PadicAlgCl p))
      rw [Metric.mem_closure_iff]
      intro ε hε
      have hr' : ∃ r : ℚ, ‖a - r‖ < ε := by
        first
        | exact Padic.rat_dense p a hε
        | exact Padic.rat_dense a hε
        | exact Padic.rat_dense (p := p) a hε
      obtain ⟨r, hr⟩ := hr'
      refine ⟨ι (algebraMap F Ω (r : F)), ⟨(r : F), rfl⟩, ?_⟩
      rw [dist_eq_norm, map_ratCast, map_ratCast, ← map_ratCast (algebraMap ℚ_[p] (PadicAlgCl p)) r,
        ← map_sub]
      first
      | (rw [norm_algebraMap']; exact hr)
      | (rw [PadicAlgCl.norm_extends]; exact hr)
    let C : Subalgebra ℚ_[p] (PadicAlgCl p) :=
      { R.topologicalClosure with algebraMap_mem' := hQ }
    have hKC : (Kloc F ι).toSubalgebra ≤ C := by
      have halg : ∀ y ∈ Set.range (ι.comp (algebraMap F Ω)), IsAlgebraic ℚ_[p] y :=
        fun y _ => Algebra.IsAlgebraic.isAlgebraic y
      show (IntermediateField.adjoin ℚ_[p] (Set.range (ι.comp (algebraMap F Ω)))).toSubalgebra ≤ C
      first
      | (rw [IntermediateField.adjoin_toSubalgebra_of_isAlgebraic halg]
         exact Algebra.adjoin_le fun y hy => R.le_topologicalClosure hy)
      | (rw [IntermediateField.adjoin_algebraic_toSubalgebra halg]
         exact Algebra.adjoin_le fun y hy => R.le_topologicalClosure hy)
      | (rw [IntermediateField.adjoin_eq_algebra_adjoin]
         · exact Algebra.adjoin_le fun y hy => R.le_topologicalClosure hy
         · intro y hy
           exact (Algebra.adjoin ℚ_[p] (Set.range (ι.comp (algebraMap F Ω)))).inv_mem_of_algebraic
             (Algebra.IsAlgebraic.isAlgebraic _) hy)
    have hcC : c ∈ closure (R : Set (PadicAlgCl p)) := hKC hc
    rw [Metric.mem_closure_iff] at hcC
    obtain ⟨b, ⟨f, rfl⟩, hb⟩ := hcC δ hδ
    exact ⟨f, by rwa [dist_eq_norm] at hb⟩
  have hsum : ∀ w : PadicAlgCl p, Polynomial.aeval w (minpoly (Kloc F ι) (ι x)) =
      ∑ i ∈ Finset.range ((minpoly (Kloc F ι) (ι x)).natDegree + 1),
        (((minpoly (Kloc F ι) (ι x)).coeff i : Kloc F ι) : PadicAlgCl p) * w ^ i := by
    intro w
    rw [Polynomial.aeval_eq_sum_range]
    first
    | rfl
    | (refine Finset.sum_congr rfl fun i _ => ?_; rw [Algebra.smul_def]; rfl)
    | simp only [Algebra.smul_def, IntermediateField.algebraMap_apply]
  obtain ⟨N, hN⟩ : ∃ N : ℕ, N = (minpoly (Kloc F ι) (ι x)).natDegree + 1 := ⟨_, rfl⟩
  rw [← hN] at hsum
  obtain ⟨c, hc⟩ : ∃ c : ℕ → PadicAlgCl p,
      ∀ i, c i = (((minpoly (Kloc F ι) (ι x)).coeff i : Kloc F ι) : PadicAlgCl p) := ⟨_, fun _ => rfl⟩
  have hcK : ∀ i, c i ∈ Kloc F ι := fun i => by rw [hc i]; exact ((minpoly (Kloc F ι) (ι x)).coeff i).2
  simp only [← hc] at hsum
  have hy0 : ∑ i ∈ Finset.range N, c i * ι x ^ i = 0 := by
    rw [← hsum]; exact minpoly.aeval _ _
  by_contra hne
  have hv : 0 < ‖Polynomial.aeval (ι (τ x)) (minpoly (Kloc F ι) (ι x))‖ := norm_pos_iff.mpr hne
  rw [hsum] at hv hne
  obtain ⟨M, hM⟩ : ∃ M : ℝ, M = ∑ i ∈ Finset.range N, ‖ι (τ x)‖ ^ i + ∑ i ∈ Finset.range N, ‖ι x‖ ^ i :=
    ⟨_, rfl⟩
  have hM0 : 0 ≤ M := by rw [hM]; positivity
  obtain ⟨δ, hδ0, hδlt⟩ : ∃ δ : ℝ, 0 < δ ∧ δ * M < ‖∑ i ∈ Finset.range N, c i * ι (τ x) ^ i‖ := by
    have hM1' : (0 : ℝ) < M + 1 := by linarith
    refine ⟨‖∑ i ∈ Finset.range N, c i * ι (τ x) ^ i‖ / (M + 1), div_pos hv hM1', ?_⟩
    have hM1 : M + 1 ≠ 0 := hM1'.ne'
    have e : ‖∑ i ∈ Finset.range N, c i * ι (τ x) ^ i‖ / (M + 1) * (M + 1) =
        ‖∑ i ∈ Finset.range N, c i * ι (τ x) ^ i‖ := div_mul_cancel₀ _ hM1
    have hδ' : 0 < ‖∑ i ∈ Finset.range N, c i * ι (τ x) ^ i‖ / (M + 1) := div_pos hv hM1'
    nlinarith
  choose f hf using fun i => hdense (c i) (hcK i) δ hδ0
  obtain ⟨u, hu_def⟩ : ∃ u : ℕ → PadicAlgCl p, ∀ i, u i = c i - ι (algebraMap F Ω (f i)) :=
    ⟨_, fun _ => rfl⟩
  have hu : ∀ i, ‖u i‖ ≤ δ := fun i => by rw [hu_def]; exact (hf i).le
  obtain ⟨w, hw⟩ : ∃ w : Ω, w = ∑ i ∈ Finset.range N, algebraMap F Ω (f i) * x ^ i := ⟨_, rfl⟩
  have hιw : ι w = ∑ i ∈ Finset.range N, ι (algebraMap F Ω (f i)) * ι x ^ i := by
    rw [hw]; simp only [map_sum, map_mul, map_pow]
  have hιτw : ι (τ w) = ∑ i ∈ Finset.range N, ι (algebraMap F Ω (f i)) * ι (τ x) ^ i := by
    rw [hw]; simp only [map_sum, map_mul, map_pow, AlgEquiv.commutes]
  have h1 : ι w = -∑ i ∈ Finset.range N, u i * ι x ^ i := by
    rw [hιw, eq_neg_iff_add_eq_zero, ← Finset.sum_add_distrib, ← hy0]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hu_def]; ring
  have h2 : ∑ i ∈ Finset.range N, c i * ι (τ x) ^ i =
      ∑ i ∈ Finset.range N, u i * ι (τ x) ^ i + ι (τ w) := by
    rw [hιτw, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hu_def]; ring
  have h3 : ‖ι (τ w)‖ = ‖ι w‖ := norm_apply_of_mem_dec h hτ w
  have h4 : ‖∑ i ∈ Finset.range N, c i * ι (τ x) ^ i‖ ≤ δ * M := by
    rw [h2]
    calc _ ≤ ‖∑ i ∈ Finset.range N, u i * ι (τ x) ^ i‖ + ‖ι (τ w)‖ := norm_add_le _ _
      _ ≤ δ * ∑ i ∈ Finset.range N, ‖ι (τ x)‖ ^ i + δ * ∑ i ∈ Finset.range N, ‖ι x‖ ^ i := by
          refine add_le_add (norm_sum_mul_pow_le _ u _ hu) ?_
          rw [h3, h1, norm_neg]
          exact norm_sum_mul_pow_le _ u _ hu
      _ = δ * M := by rw [hM, mul_add]
  linarith
theorem exists_apply_eq_of_mem_dec {A : ValuationSubring Ω} {ι : Ω →+* PadicAlgCl p} (h : Compat p A ι) {τ : Ω ≃ₐ[F] Ω}
    (hτ : τ ∈ Dec (F := F) A) (x : Ω) : ∃ σ : GK F ι, σ (ι x) = ι (τ x) := by
  haveI := isAlgClosure_Kloc (F := F) ι
  have hint : IsIntegral (Kloc F ι) (ι x) := by
    first
    | exact Algebra.IsIntegral.isIntegral _
    | exact (Algebra.IsAlgebraic.isAlgebraic (R := Kloc F ι) (ι x)).isIntegral
  have hc : IsConjRoot (Kloc F ι) (ι x) (ι (τ x)) :=
    isConjRoot_of_aeval_eq_zero hint (minpoly_aeval_of_mem_dec h hτ x)
  obtain ⟨σ, hσ⟩ := isConjRoot_iff_exists_algEquiv.mp hc
  first
  | exact ⟨σ, hσ⟩
  | exact ⟨σ.symm, by rw [← hσ]; simp⟩
theorem exists_res_eqOn_of_mem_dec {A : ValuationSubring Ω} {ι : Ω →+* PadicAlgCl p} (h : Compat p A ι) {τ : Ω ≃ₐ[F] Ω}
    (hτ : τ ∈ Dec (F := F) A) (E : IntermediateField F Ω) [FiniteDimensional F E] :
    ∃ σ : GK F ι, ∀ y ∈ E, res ι σ y = τ y := by
  obtain ⟨α, hα⟩ := Field.exists_primitive_element F E
  obtain ⟨σ, hσ⟩ := exists_apply_eq_of_mem_dec h hτ (α : Ω)
  refine ⟨σ, fun y hy => ?_⟩
  have h1 : res ι σ (α : Ω) = τ (α : Ω) := ι.injective (by rw [res_spec, hσ])
  have hint : IsIntegral F α := IsIntegral.of_finite F α
  have htop : Algebra.adjoin F {α} = ⊤ := by
    first
    | rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isIntegral hint, hα,
        IntermediateField.top_toSubalgebra]
    | rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hint.isAlgebraic, hα,
        IntermediateField.top_toSubalgebra]
    | rw [← IntermediateField.adjoin_toSubalgebra_of_isAlgebraic (S := {α})
        (fun _ _ => Algebra.IsAlgebraic.isAlgebraic _), hα, IntermediateField.top_toSubalgebra]
    | rw [← IntermediateField.adjoin_algebraic_toSubalgebra (S := {α})
        (fun _ _ => Algebra.IsAlgebraic.isAlgebraic _), hα, IntermediateField.top_toSubalgebra]
  have key : ((res ι σ).toAlgHom.comp E.val : E →ₐ[F] Ω) = τ.toAlgHom.comp E.val := by
    apply AlgHom.ext_of_adjoin_eq_top htop
    intro z hz
    rw [Set.mem_singleton_iff] at hz
    subst hz
    simpa using h1
  have h2 := congrArg (fun φ : E →ₐ[F] Ω => φ ⟨y, hy⟩) key
  simpa using h2
theorem exists_res_eq {A : ValuationSubring Ω} {ι : Ω →+* PadicAlgCl p} (h : Compat p A ι) {τ : Ω ≃ₐ[F] Ω}
    (hτ : τ ∈ Dec (F := F) A) : ∃ σ : GK F ι, res ι σ = τ := by
  classical
  haveI := isAlgClosure_Kloc (F := F) ι
  have hclosed : ∀ a b : PadicAlgCl p, IsClosed {σ : GK F ι | σ a = b} := by
    intro a b
    rw [← isOpen_compl_iff, isOpen_iff_forall_mem_open]
    intro σ hσ
    have hai : IsIntegral (Kloc F ι) a := by
      first
      | exact Algebra.IsIntegral.isIntegral _
      | exact (Algebra.IsAlgebraic.isAlgebraic (R := Kloc F ι) a).isIntegral
    haveI hfin : FiniteDimensional (Kloc F ι) (IntermediateField.adjoin (Kloc F ι) {a}) :=
      IntermediateField.adjoin.finiteDimensional hai
    have hU : IsOpen ((IntermediateField.adjoin (Kloc F ι) {a}).fixingSubgroup : Set (GK F ι)) :=
      IntermediateField.fixingSubgroup_isOpen _
    refine ⟨(fun ρ => σ⁻¹ * ρ) ⁻¹' ((IntermediateField.adjoin (Kloc F ι) {a}).fixingSubgroup : Set (GK F ι)),
      ?_, hU.preimage (continuous_const.mul continuous_id), ?_⟩
    · intro ρ hρ
      have hfix : (σ⁻¹ * ρ) a = a :=
        (IntermediateField.mem_fixingSubgroup_iff _ _).1 hρ a (IntermediateField.mem_adjoin_simple_self _ a)
      intro hρb
      apply hσ
      show σ a = b
      have e : σ ((σ⁻¹ * ρ) a) = ρ a := by
        first
        | (rw [← AlgEquiv.mul_apply, ← mul_assoc, mul_inv_cancel, one_mul])
        | (rw [← AlgEquiv.mul_apply, ← mul_assoc, mul_right_inv, one_mul])
        | simp
      rw [← hρb, ← e, hfix]
    · show σ⁻¹ * σ ∈ (IntermediateField.adjoin (Kloc F ι) {a}).fixingSubgroup
      rw [inv_mul_cancel]
      exact Subgroup.one_mem _
  let T : {E : IntermediateField F Ω // FiniteDimensional F E} → Set (GK F ι) :=
    fun E => {σ | ∀ y ∈ E.1, res ι σ y = τ y}
  have hTcl : ∀ E, IsClosed (T E) := by
    intro E
    have e : T E = ⋂ y ∈ E.1, {σ : GK F ι | σ (ι y) = ι (τ y)} := by
      ext σ
      simp only [T, Set.mem_setOf_eq, Set.mem_iInter]
      refine forall₂_congr fun y _ => ?_
      rw [← res_spec, ι.injective.eq_iff]
    rw [e]
    exact isClosed_biInter fun y _ => hclosed _ _
  have hTne : ∀ E, (T E).Nonempty := by
    intro E
    haveI := E.2
    obtain ⟨σ, hσ⟩ := exists_res_eqOn_of_mem_dec h hτ E.1
    exact ⟨σ, hσ⟩
  have hdir : Directed (· ⊇ ·) T := by
    intro E₁ E₂
    haveI := E₁.2
    haveI := E₂.2
    refine ⟨⟨E₁.1 ⊔ E₂.1, inferInstance⟩, ?_, ?_⟩
    · intro σ hσ y hy
      exact hσ y ((le_sup_left : E₁.1 ≤ E₁.1 ⊔ E₂.1) hy)
    · intro σ hσ y hy
      exact hσ y ((le_sup_right : E₂.1 ≤ E₁.1 ⊔ E₂.1) hy)
  haveI : Nonempty {E : IntermediateField F Ω // FiniteDimensional F E} := ⟨⟨⊥, inferInstance⟩⟩
  obtain ⟨σ, hσ⟩ := IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed T hdir hTne
    (fun E => (hTcl E).isCompact) hTcl
  refine ⟨σ, ?_⟩
  ext y
  rw [Set.mem_iInter] at hσ
  have hy : IsIntegral F y := Algebra.IsIntegral.isIntegral y
  exact hσ ⟨IntermediateField.adjoin F {y}, IntermediateField.adjoin.finiteDimensional hy⟩ y
    (IntermediateField.mem_adjoin_simple_self F y)
def resDec {A : ValuationSubring Ω} {ι : Ω →+* PadicAlgCl p} (h : Compat p A ι) : GK F ι →* Dec (F := F) A :=
  (res ι).codRestrict (Dec (F := F) A) (res_mem_dec h)
theorem bijective_resDec {A : ValuationSubring Ω} {ι : Ω →+* PadicAlgCl p} (h : Compat p A ι) :
    Function.Bijective (resDec (F := F) h) := by
  refine ⟨fun σ₁ σ₂ he => res_injective ι (congrArg Subtype.val he), fun τ => ?_⟩
  obtain ⟨σ, hσ⟩ := exists_res_eq h τ.2
  exact ⟨σ, Subtype.ext hσ⟩
theorem continuous_resDec {A : ValuationSubring Ω} {ι : Ω →+* PadicAlgCl p} (h : Compat p A ι) :
    Continuous (resDec (F := F) h) := by
  first
  | exact (continuous_res ι).subtype_mk _
  | exact Continuous.subtype_mk (continuous_res ι) (res_mem_dec h)
  | exact continuous_induced_rng.2 (continuous_res ι)
def equiv {A : ValuationSubring Ω} {ι : Ω →+* PadicAlgCl p} (h : Compat p A ι) : GK F ι ≃ₜ* Dec (F := F) A := by
  haveI := isAlgClosure_Kloc (F := F) ι
  haveI : T2Space (Ω ≃ₐ[F] Ω) := krullTopology_t2
  haveI : IsGalois (Kloc F ι) (PadicAlgCl p) := isGalois_iff.mpr ⟨inferInstance, inferInstance⟩
  exact
  { toMulEquiv := MulEquiv.ofBijective (resDec h) (bijective_resDec h)
    continuous_toFun := continuous_resDec h
    continuous_invFun := Continuous.continuous_symm_of_equiv_compact_to_t2
      (f := (MulEquiv.ofBijective (resDec h) (bijective_resDec h)).toEquiv) (continuous_resDec h) }
end ReciprocityTheory.Neutral.Cmp


