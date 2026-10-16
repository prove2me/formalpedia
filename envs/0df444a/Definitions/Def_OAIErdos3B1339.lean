-- Prove2me | Definitions.Def_OAIErdos3B1339
-- name    : OAIErdos3B1339
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-15T18:51:35.392205+00:00
-- url     : https://prove2.me/theorems/f74c9d41-5e7c-4e29-bb50-9e1dba5cd093
-- title:
--   OpenAI Erdős-3 split, definitions bundle 1340 of 1340
-- statement:
--   Definitions bundle 1340 of 1340 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs) and OpenAI's `@[simp]` lemmas from the same modules.
--
--   It imports the previous bundle `OAIErdos3B1338`, so the bundles form a chain and importing this one makes the definitions of bundles 1 to 1340 available.
--
--   Modules: `OAI.Erdos3.NilpotentLieFiltration.CertifiedFullChartDetectedDecomposition.exists_admissible_stage`, `OAI.Erdos3.NilpotentLieFiltration.CertifiedFullChartFiniteHistory.append_admissible`, `OAI.Erdos3.NilpotentLieFiltration.CertifiedFullChartFiniteHistory.append_admissible_K`, `OAI.Erdos3.NilpotentLieFiltration.CertifiedFullChartFiniteHistory.append_admissible_entry`, `OAI.Erdos3.NilpotentLieFiltration.CertifiedFullChartFiniteHistory.append_admissible_prefix`, `OAI.Erdos3.NilpotentLieFiltration.CertifiedFullChartFiniteHistory.append_admissible_q`, `OAI.Erdos3.NilpotentLieFiltration.CertifiedFullChartFiniteHistory.append_admissible_rat`, `OAI.Erdos3.NilpotentLieFiltration.CertifiedFullChartFiniteHistory.append_admissible_slow`, `OAI.Erdos3.NilpotentLieFiltration.CertifiedFullChartFiniteHistory.exists_append_admissible`, `OAI.Erdos3.NilpotentLieFiltration.FullChartAdmissibleStageCorrection`, `OAI.Erdos3.NilpotentLieFiltration.FullChartControlledFactors.exists_prescribed_full_lifts`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B1333

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.FullChartPrescribedPolynomialLifts
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial _root_.MvPolynomial _root_.OAI.MvPolynomial
open scoped TensorProduct

attribute [local irreducible] realPolynomialSymbolLift realPolynomialSymbolHom realSymbolHomogeneousPullbackHom weightedAdaptedRealChartHom realChartSubstitute

variable {s m : ℕ} {X τ ι L : Type} [Fintype X]
  [LieRing L] [LieAlgebra ℚ L]
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
  (J : Fin m → Type) [∀ j, Fintype (J j)]

local notation "wt" => fullTaggedVariableWeight (X := X) J

theorem FullChartControlledFactors.exists_prescribed_full_lifts
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)) (N : X → ℕ)
    (left right : F.RealPolynomialSymbolGroup wt)
    {budget : ℝ} (h : FullChartControlledFactors F b ω hF J poly N left right budget)
    (v : τ → ℕ) (β δ : (X ⊕ (Σ j, J j)) → MvPolynomial τ ℝ)
    (hβ : ∀ i, (β i).IsWeightedHomogeneous v (wt i))
    (hδ : ∀ i, δ i ∈ weightedSupportLE v (wt i))
    (htop : ∀ i, weightedHomogeneousComponent v (wt i) (δ i) =
      MvPolynomial.aeval β (normalizedRealPolynomialChart (fun i => (N i : ℝ))
        (fullTaggedMajorTopCoordinates J poly) i))
    (D : ℕ) (hD : 0 < D) (hgrid : ∀ i, realPolynomialCoefficientGrid D (β i)) :
    ∃ q : ℕ, 0 < q ∧ (q : ℝ) ≤ Real.exp budget ∧
      ∃ e r : (F.realification.adaptedPolynomialFiltration v).Group,
        F.realPolynomialSymbolHom b ω hF v e =
          F.realSymbolHomogeneousPullbackHom b ω hF wt v β hβ left ∧
        F.realPolynomialSymbolHom b ω hF v r =
          F.realSymbolHomogeneousPullbackHom b ω hF wt v β hβ right ∧
        F.PolynomialRationalGrid b v (q * D ^ s) r ∧
        0 < q * D ^ s ∧
        ∀ {υ : Type*} (u : υ → ℕ) (γ : τ → MvPolynomial υ ℝ)
          (hγ : ∀ i, γ i ∈ weightedSupportLE u (v i))
          (T : υ → ℝ), (∀ i, 0 < T i) →
          ∀ B : ℝ, 1 ≤ B →
          (∀ i, realPolynomialMass (scaleMvPolynomialAxes T (MvPolynomial.aeval γ (δ i))) ≤ B) →
          F.PolynomialSlowBound b u T
            (((Fintype.card (X ⊕ (Σ j, J j)) : ℝ) + 1) ^ s * Real.exp budget * B ^ s)
            (F.weightedAdaptedRealChartHom v u γ hγ e) := by
  obtain ⟨P, e, hbound, _, _, hdegree, he, hsymbol⟩ :=
    FullChartControlledFactors.exists_inhomogeneous_left_lift
      F b ω hF J poly N left right h v β δ hβ hδ htop
  obtain ⟨q, hq, hqB, _, _, _, hright⟩ := h
  let R := F.realSymbolHomogeneousPullbackHom b ω hF wt v β hβ right
  have hR : F.SymbolRationalGrid b ω hF v (q * D ^ s) R :=
    F.symbolRationalGrid_homogeneousPullback_rational_of_coefficientGrid b ω hF wt v
      (fullTaggedVariableWeight_pos J) β hβ q D hgrid right hright
  let r := F.realPolynomialSymbolLift b ω hF v R
  have hr : F.PolynomialRationalGrid b v (q * D ^ s) r := by
    unfold PolynomialRationalGrid
    dsimp only [r]
    rw [F.realPolynomialSymbolLift_log]
    exact F.realSymbolRepresentative_rational_coefficients b ω hF v (q * D ^ s) R hR
  refine ⟨q, hq, hqB, e, r, hsymbol, F.realPolynomialSymbolHom_lift b ω hF v R,
    hr, Nat.mul_pos hq (pow_pos hD s), ?_⟩
  intro υ u γ hγ T hT B hB hmass
  exact F.polynomialSlowBound_inhomogeneous_chart_lift b ω hF v u e δ P he γ hγ
    T hT hbound (Real.exp_pos _).le hB hdegree hmass

end Erdos3.NilpotentLieFiltration

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.TerminalChartSlowEvaluation
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial PolynomialTranslationLie RationalFilteredNilmanifold
open scoped TensorProduct

variable {m : ℕ} {X : Type}
variable {ι L η : Type*} [LieRing L] [LieAlgebra ℚ L] [Fintype η] {s : ℕ}
variable (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
variable (J : Fin m → Type) [∀ j, Fintype (J j)] (k : ℕ)
variable (fast : Submodule ℚ F.AssociatedGraded)
variable (basis : Basis η ℝ (ℝ ⊗[ℚ] (F.AssociatedGraded ⧸ fast)))
variable (lift : (F.AssociatedGraded ⧸ fast) →ₗ[ℚ] F.AssociatedGraded)
variable (Z left right : F.RealPolynomialSymbolGroup (fullTaggedVariableWeight (X := X) J))
variable (K₀ : Set (X ⊕ (Σ j, J j) → ℝ))
variable (Utag : ∀ j, Submodule ℝ (J j → ℝ))
variable (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
variable (N : X → ℕ) (budget : ℝ)

local notation "wt" => fullTaggedVariableWeight (X := X) J
local notation "quotientReal" => ℝ ⊗[ℚ] (F.AssociatedGraded ⧸ fast)
local notation "chart" => normalizedRealPolynomialChart (fun i => (N i : ℝ))
  (fullTaggedMajorTopCoordinates J poly)

def FullChartAdmissibleStageCorrection
    (q : ℕ) (K' : Set (X ⊕ (Σ j, J j) → ℝ))
    (pair : VectorPolynomial (X ⊕ (Σ j, J j)) ℚ quotientReal ×
      VectorPolynomial (X ⊕ (Σ j, J j)) ℚ quotientReal) : Prop :=
      (∀ α, Finsupp.weight wt α ≠ k → coefficients pair.1 α = 0) ∧
      (∀ α, Finsupp.weight wt α ≠ k → coefficients pair.2 α = 0) ∧
      (∀ i, (coordinate (basis.coord i).toAddMonoidHom pair.1).totalDegree ≤ k) ∧
      (∀ i, (coordinate (basis.coord i).toAddMonoidHom pair.2).totalDegree ≤ k) ∧
      0 < q ∧ (q : ℝ) ≤ Real.exp ((Fintype.card η : ℝ) * budget) ∧
      K' ⊆ K₀ ∧
      (∀ t ∈ K', ∀ r : ℚ, (fun i => (r : ℝ) ^ wt i * t i) ∈ K') ∧
      (∀ t ∈ K₀, (∀ j, (fun a => t (Sum.inr ⟨j, a⟩)) ∈ Utag j) → t ∈ K') ∧
      (∀ α i, |basis.coord i (coefficients pair.1 α)| ≤ Real.exp budget) ∧
      (∀ α, (fun i => basis.coord i (coefficients pair.2 α)) ∈ realDenominatorGrid q) ∧
      (∀ t ∈ K', ∀ j ≤ k,
        F.realSymbolGradeEvaluation b ω hF wt j t
          ((left * F.restrictedMajorCorrection b ω hF wt fast lift k
              (realChartSubstitute chart pair.1))⁻¹ * Z *
            (F.restrictedMajorCorrection b ω hF wt fast lift k pair.2 * right)⁻¹).coord ∈
          fast.baseChange ℝ) ∧
      (∃ (detectedfast : η → LieSubalgebra ℚ (weightedSubalgebra (lowTaggedWeight J k) k))
        (slow rat : VectorPolynomial (X ⊕ Fin (Fintype.card (LowTaggedIndex J k))) ℚ quotientReal),
        pair.1 = lowTaggedVectorExtend J k slow ∧ pair.2 = lowTaggedVectorExtend J k rat ∧
        K' = fullTaggedGradedBaseIntersection J k K₀
          (fun i => majorPhaseDetectedRealBase J k (detectedfast i))) ∧
      RationalTaggedConstraintCertificate J K₀ K' budget (Fintype.card η * m) ∧
      ∀ t ∈ K', eval₂ t
        (F.realSymbolGradeQuotientPolynomial b ω hF wt fast k (left⁻¹ * Z * right⁻¹).coord) =
        eval₂ t (realChartSubstitute chart pair.1) + eval₂ t pair.2

theorem CertifiedFullChartDetectedDecomposition.exists_admissible_stage
    (h : CertifiedFullChartDetectedDecomposition F b ω hF J k fast basis lift
      Z left right K₀ Utag poly N budget) :
    ∃ (q : ℕ) (K' : Set (X ⊕ (Σ j, J j) → ℝ))
      (pair : VectorPolynomial (X ⊕ (Σ j, J j)) ℚ quotientReal ×
        VectorPolynomial (X ⊕ (Σ j, J j)) ℚ quotientReal),
      FullChartAdmissibleStageCorrection F b ω hF J k fast basis lift
        Z left right K₀ Utag poly N budget q K' pair := by
  obtain ⟨pS, pR, q, K', hpair⟩ := CertifiedFullChartDetectedDecomposition.exists_homogeneous
    (F := F) (b := b) (ω := ω) (hF := hF) (fast := fast) (lift := lift)
    (J := J) (k := k) (basis := basis) (Z := Z) (left := left) (right := right)
    (K₀ := K₀) (Utag := Utag) (poly := poly) (N := N) (budget := budget) h
  refine ⟨q, K', (pS, pR), ?_⟩
  unfold FullChartAdmissibleStageCorrection
  with_reducible exact hpair

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration.CertifiedFullChartFiniteHistory

open Module VectorPolynomial
open scoped TensorProduct Classical

attribute [local irreducible] realSymbolGradeEvaluation restrictedMajorCorrection realSymbolGradeQuotientPolynomial outer

variable {m : ℕ} {X : Type} {ι L η : Type*}
  [LieRing L] [LieAlgebra ℚ L] [Fintype η] {s : ℕ}

variable (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
variable (J : Fin m → Type) [∀ j, Fintype (J j)]
variable (fast : Submodule ℚ F.AssociatedGraded)
variable (basis : Basis η ℝ (ℝ ⊗[ℚ] (F.AssociatedGraded ⧸ fast)))
variable (lift : (F.AssociatedGraded ⧸ fast) →ₗ[ℚ] F.AssociatedGraded)
variable (Z : F.RealPolynomialSymbolGroup (fullTaggedVariableWeight (X := X) J))
variable (Kinitial : Set (X ⊕ (Σ j, J j) → ℝ))
variable (Utag : ∀ j, Submodule ℝ (J j → ℝ))
variable (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
variable (N : X → ℕ) (Bphase : ℝ)

local notation "wt" => fullTaggedVariableWeight (X := X) J
local notation "chart" => normalizedRealPolynomialChart (fun i => (N i : ℝ))
  (fullTaggedMajorTopCoordinates J poly)
local notation "State" => CertifiedFullChartFiniteHistory F b ω hF J fast basis lift Z Kinitial Utag poly N Bphase

variable {F b ω hF J fast basis lift Z Kinitial Utag poly N Bphase}

theorem exists_append_admissible {n : ℕ} (H : State n)
    (budget : ℝ) (hbudget : budget ≤ Bphase) (q : ℕ)
    (K' : Set (X ⊕ (Σ j, J j) → ℝ))
    (pair : VectorPolynomial (X ⊕ (Σ j, J j)) ℚ (ℝ ⊗[ℚ] (F.AssociatedGraded ⧸ fast)) ×
      VectorPolynomial (X ⊕ (Σ j, J j)) ℚ (ℝ ⊗[ℚ] (F.AssociatedGraded ⧸ fast)))
    (hpair : FullChartAdmissibleStageCorrection F b ω hF J (n + 1) fast basis lift
      Z H.outer.1 H.outer.2 H.K Utag poly N budget q K' pair) :
    ∃ Hnext : State (n + 1),
      Hnext.slow = Function.update H.slow n pair.1 ∧
      Hnext.rat = Function.update H.rat n pair.2 ∧
      Hnext.q = Function.update H.q n q ∧ Hnext.K = K' := by
  let pS := pair.1
  let pR := pair.2
  have hq := hpair.2.2.2.2.1
  have hqB := hpair.2.2.2.2.2.1
  have hsub := hpair.2.2.2.2.2.2.1
  have hdilate := hpair.2.2.2.2.2.2.2.1
  have hretain := hpair.2.2.2.2.2.2.2.2.1
  have hcap := hpair.2.2.2.2.2.2.2.2.2.1
  have hgrid := hpair.2.2.2.2.2.2.2.2.2.2.1
  have hnext := hpair.2.2.2.2.2.2.2.2.2.2.2.1
  have hcert := hpair.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  let slow' := Function.update H.slow n pS
  let rat' := Function.update H.rat n pR
  let q' := Function.update H.q n q
  have hslow (j : ℕ) (hj : j < n) : slow' j = H.slow j :=
    Function.update_of_ne (Nat.ne_of_lt hj) _ _
  have hrat (j : ℕ) (hj : j < n) : rat' j = H.rat j :=
    Function.update_of_ne (Nat.ne_of_lt hj) _ _
  have hqold (j : ℕ) (hj : j < n) : q' j = H.q j :=
    Function.update_of_ne (Nat.ne_of_lt hj) _ _
  have hprefix : F.restrictedMajorOuterFactors b ω hF wt fast lift
      (fun j => realChartSubstitute chart (slow' j)) rat' n = H.outer := by
    unfold outer
    apply F.restrictedMajorOuterFactors_congr
    · intro j hj
      rw [hslow j hj]
    · exact hrat
  have houter : F.restrictedMajorOuterFactors b ω hF wt fast lift
      (fun j => realChartSubstitute chart (slow' j)) rat' (n + 1) =
      (H.outer.1 * F.restrictedMajorCorrection b ω hF wt fast lift (n + 1)
        (realChartSubstitute chart pS),
       F.restrictedMajorCorrection b ω hF wt fast lift (n + 1) pR * H.outer.2) := by
    rw [restrictedMajorOuterFactors, hprefix]
    simp only [slow', rat', Function.update_self]
  have hcapB : ∀ α i, |basis.coord i (coefficients pS α)| ≤ Real.exp Bphase :=
    fun α i => (hcap α i).trans (Real.exp_le_exp.mpr hbudget)
  have hqBB : (q : ℝ) ≤ Real.exp ((Fintype.card η : ℝ) * Bphase) :=
    hqB.trans (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hbudget (Nat.cast_nonneg _)))
  let Hnext : State (n + 1) := {
    slow := slow'
    rat := rat'
    q := q'
    K := K'
    certificate := by
      simpa only [Nat.succ_mul] using H.certificate.trans (hcert.monoB hbudget)
    subset := fun t ht => H.subset (hsub ht)
    dilation := hdilate
    retained := fun t ht hU => hretain t (H.retained t ht hU) hU
    slow_bound := by
      intro j hj α i
      by_cases hjn : j = n
      · subst j
        simpa only [slow', Function.update_self] using hcapB α i
      · rw [hslow j (by omega)]
        exact H.slow_bound j (by omega) α i
    q_pos := by
      intro j hj
      by_cases hjn : j = n
      · subst j
        simpa only [q', Function.update_self] using hq
      · rw [hqold j (by omega)]
        exact H.q_pos j (by omega)
    q_bound := by
      intro j hj
      by_cases hjn : j = n
      · subst j
        simpa only [q', Function.update_self] using hqBB
      · rw [hqold j (by omega)]
        exact H.q_bound j (by omega)
    rat_grid := by
      intro j hj α
      by_cases hjn : j = n
      · subst j
        simpa only [rat', q', Function.update_self] using hgrid α
      · rw [hrat j (by omega), hqold j (by omega)]
        exact H.rat_grid j (by omega) α
    invariant := by
      dsimp only
      rw [houter]
      with_reducible exact hnext }
  exact ⟨Hnext, rfl, rfl, rfl, rfl⟩

noncomputable def append_admissible {n : ℕ} (H : State n) (budget : ℝ) (hbudget : budget ≤ Bphase) (q : ℕ)
  (K' : Set (X ⊕ (Σ j, J j) → ℝ))
  (pair : VectorPolynomial (X ⊕ (Σ j, J j)) ℚ (ℝ ⊗[ℚ] (F.AssociatedGraded ⧸ fast)) ×
    VectorPolynomial (X ⊕ (Σ j, J j)) ℚ (ℝ ⊗[ℚ] (F.AssociatedGraded ⧸ fast)))
  (hpair : FullChartAdmissibleStageCorrection F b ω hF J (n + 1) fast basis lift
    Z H.outer.1 H.outer.2 H.K Utag poly N budget q K' pair) : State (n + 1) :=
  Classical.choose (exists_append_admissible H budget hbudget q K' pair hpair)

@[simp] theorem append_admissible_slow
    {n : ℕ} (H : State n) (budget : ℝ) (hbudget : budget ≤ Bphase) (q : ℕ)
  (K' : Set (X ⊕ (Σ j, J j) → ℝ))
  (pair : VectorPolynomial (X ⊕ (Σ j, J j)) ℚ (ℝ ⊗[ℚ] (F.AssociatedGraded ⧸ fast)) ×
    VectorPolynomial (X ⊕ (Σ j, J j)) ℚ (ℝ ⊗[ℚ] (F.AssociatedGraded ⧸ fast)))
  (hpair : FullChartAdmissibleStageCorrection F b ω hF J (n + 1) fast basis lift
    Z H.outer.1 H.outer.2 H.K Utag poly N budget q K' pair) :
    (H.append_admissible budget hbudget q K' pair hpair).slow =
      Function.update H.slow n pair.1 :=
  (Classical.choose_spec (exists_append_admissible H budget hbudget q K' pair hpair)).1

@[simp] theorem append_admissible_rat
    {n : ℕ} (H : State n) (budget : ℝ) (hbudget : budget ≤ Bphase) (q : ℕ)
  (K' : Set (X ⊕ (Σ j, J j) → ℝ))
  (pair : VectorPolynomial (X ⊕ (Σ j, J j)) ℚ (ℝ ⊗[ℚ] (F.AssociatedGraded ⧸ fast)) ×
    VectorPolynomial (X ⊕ (Σ j, J j)) ℚ (ℝ ⊗[ℚ] (F.AssociatedGraded ⧸ fast)))
  (hpair : FullChartAdmissibleStageCorrection F b ω hF J (n + 1) fast basis lift
    Z H.outer.1 H.outer.2 H.K Utag poly N budget q K' pair) :
    (H.append_admissible budget hbudget q K' pair hpair).rat =
      Function.update H.rat n pair.2 :=
  (Classical.choose_spec (exists_append_admissible H budget hbudget q K' pair hpair)).2.1

@[simp] theorem append_admissible_q
    {n : ℕ} (H : State n) (budget : ℝ) (hbudget : budget ≤ Bphase) (q : ℕ)
  (K' : Set (X ⊕ (Σ j, J j) → ℝ))
  (pair : VectorPolynomial (X ⊕ (Σ j, J j)) ℚ (ℝ ⊗[ℚ] (F.AssociatedGraded ⧸ fast)) ×
    VectorPolynomial (X ⊕ (Σ j, J j)) ℚ (ℝ ⊗[ℚ] (F.AssociatedGraded ⧸ fast)))
  (hpair : FullChartAdmissibleStageCorrection F b ω hF J (n + 1) fast basis lift
    Z H.outer.1 H.outer.2 H.K Utag poly N budget q K' pair) :
    (H.append_admissible budget hbudget q K' pair hpair).q =
      Function.update H.q n q :=
  (Classical.choose_spec (exists_append_admissible H budget hbudget q K' pair hpair)).2.2.1

theorem append_admissible_K
    {n : ℕ} (H : State n) (budget : ℝ) (hbudget : budget ≤ Bphase) (q : ℕ)
  (K' : Set (X ⊕ (Σ j, J j) → ℝ))
  (pair : VectorPolynomial (X ⊕ (Σ j, J j)) ℚ (ℝ ⊗[ℚ] (F.AssociatedGraded ⧸ fast)) ×
    VectorPolynomial (X ⊕ (Σ j, J j)) ℚ (ℝ ⊗[ℚ] (F.AssociatedGraded ⧸ fast)))
  (hpair : FullChartAdmissibleStageCorrection F b ω hF J (n + 1) fast basis lift
    Z H.outer.1 H.outer.2 H.K Utag poly N budget q K' pair) :
    (H.append_admissible budget hbudget q K' pair hpair).K = K' :=
  (Classical.choose_spec (exists_append_admissible H budget hbudget q K' pair hpair)).2.2.2

theorem append_admissible_prefix
    {n : ℕ} (H : State n) (budget : ℝ) (hbudget : budget ≤ Bphase) (q : ℕ)
  (K' : Set (X ⊕ (Σ j, J j) → ℝ))
  (pair : VectorPolynomial (X ⊕ (Σ j, J j)) ℚ (ℝ ⊗[ℚ] (F.AssociatedGraded ⧸ fast)) ×
    VectorPolynomial (X ⊕ (Σ j, J j)) ℚ (ℝ ⊗[ℚ] (F.AssociatedGraded ⧸ fast)))
  (hpair : FullChartAdmissibleStageCorrection F b ω hF J (n + 1) fast basis lift
    Z H.outer.1 H.outer.2 H.K Utag poly N budget q K' pair) (j : ℕ) (hj : j < n) :
    (H.append_admissible budget hbudget q K' pair hpair).slow j = H.slow j ∧
    (H.append_admissible budget hbudget q K' pair hpair).rat j = H.rat j ∧
    (H.append_admissible budget hbudget q K' pair hpair).q j = H.q j := by
  simp only [CertifiedFullChartFiniteHistory.append_admissible_slow,
    CertifiedFullChartFiniteHistory.append_admissible_rat, CertifiedFullChartFiniteHistory.append_admissible_q,
    Function.update_of_ne (Nat.ne_of_lt hj), and_self]

@[simp] theorem append_admissible_entry
    {n : ℕ} (H : State n) (budget : ℝ) (hbudget : budget ≤ Bphase) (q : ℕ)
  (K' : Set (X ⊕ (Σ j, J j) → ℝ))
  (pair : VectorPolynomial (X ⊕ (Σ j, J j)) ℚ (ℝ ⊗[ℚ] (F.AssociatedGraded ⧸ fast)) ×
    VectorPolynomial (X ⊕ (Σ j, J j)) ℚ (ℝ ⊗[ℚ] (F.AssociatedGraded ⧸ fast)))
  (hpair : FullChartAdmissibleStageCorrection F b ω hF J (n + 1) fast basis lift
    Z H.outer.1 H.outer.2 H.K Utag poly N budget q K' pair) :
    (H.append_admissible budget hbudget q K' pair hpair).slow n = pair.1 ∧
    (H.append_admissible budget hbudget q K' pair hpair).rat n = pair.2 ∧
    (H.append_admissible budget hbudget q K' pair hpair).q n = q := by
  simp only [CertifiedFullChartFiniteHistory.append_admissible_slow,
    CertifiedFullChartFiniteHistory.append_admissible_rat, CertifiedFullChartFiniteHistory.append_admissible_q,
    Function.update_self, and_self]

end Erdos3.NilpotentLieFiltration.CertifiedFullChartFiniteHistory

end

section

namespace Erdos3.NilpotentLieFiltration
open Module VectorPolynomial PolynomialTranslationLie RationalFilteredNilmanifold
open scoped TensorProduct

variable {m : ℕ} {X : Type} {ι L η : Type*}
  [LieRing L] [LieAlgebra ℚ L] [Fintype η] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
  (J : Fin m → Type) [∀ j, Fintype (J j)] (k : ℕ)
  (fast : Submodule ℚ F.AssociatedGraded)
  (basis : Basis η ℝ (ℝ ⊗[ℚ] (F.AssociatedGraded ⧸ fast)))
  (lift : (F.AssociatedGraded ⧸ fast) →ₗ[ℚ] F.AssociatedGraded)
  (Z left right : F.RealPolynomialSymbolGroup (fullTaggedVariableWeight (X := X) J))
  (K₀ : Set (X ⊕ (Σ j, J j) → ℝ))
  (Utag : ∀ j, Submodule ℝ (J j → ℝ))
  (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)) (N : X → ℕ) (budget : ℝ)

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial PolynomialTranslationLie RationalFilteredNilmanifold
open scoped TensorProduct Classical

attribute [local irreducible] FullChartAdmissibleStageCorrection realSymbolGradeQuotientPolynomial realSymbolGradeEvaluation restrictedMajorCorrection

variable {m : ℕ} {X : Type}
variable {ι L η : Type*} [LieRing L] [LieAlgebra ℚ L] [Fintype η] {s : ℕ}
variable (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
variable (J : Fin m → Type) [∀ j, Fintype (J j)] (k : ℕ)
variable (fast : Submodule ℚ F.AssociatedGraded)
variable (basis : Basis η ℝ (ℝ ⊗[ℚ] (F.AssociatedGraded ⧸ fast)))
variable (lift : (F.AssociatedGraded ⧸ fast) →ₗ[ℚ] F.AssociatedGraded)
variable (Z left right : F.RealPolynomialSymbolGroup (fullTaggedVariableWeight (X := X) J))
variable (K₀ : Set (X ⊕ (Σ j, J j) → ℝ))
variable (Utag : ∀ j, Submodule ℝ (J j → ℝ))
variable (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
variable (N : X → ℕ) (budget : ℝ)


end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration.CertifiedFullChartFiniteHistory

open Module VectorPolynomial
open scoped TensorProduct Classical

attribute [local irreducible] realSymbolGradeEvaluation restrictedMajorCorrection realSymbolGradeQuotientPolynomial outer realChartSubstitute

variable {m : ℕ} {X : Type} {ι L η : Type*}
  [LieRing L] [LieAlgebra ℚ L] [Fintype η] {s : ℕ}

variable (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
variable (J : Fin m → Type) [∀ j, Fintype (J j)]
variable (fast : Submodule ℚ F.AssociatedGraded)
variable (basis : Basis η ℝ (ℝ ⊗[ℚ] (F.AssociatedGraded ⧸ fast)))
variable (lift : (F.AssociatedGraded ⧸ fast) →ₗ[ℚ] F.AssociatedGraded)
variable (Z : F.RealPolynomialSymbolGroup (fullTaggedVariableWeight (X := X) J))
variable (Kinitial : Set (X ⊕ (Σ j, J j) → ℝ))
variable (Utag : ∀ j, Submodule ℝ (J j → ℝ))
variable (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
variable (N : X → ℕ) (Bphase : ℝ)


variable {F b ω hF J fast basis lift Z Kinitial Utag poly N Bphase}

end Erdos3.NilpotentLieFiltration.CertifiedFullChartFiniteHistory

end

section

namespace Erdos3.NilpotentLieFiltration
open Module VectorPolynomial
open scoped TensorProduct

attribute [local irreducible] realSymbolGradeEvaluation restrictedMajorCorrection realSymbolGradeQuotientPolynomial CertifiedFullChartFiniteHistory.outer FullChartControlledFactors

namespace CertifiedFullChartFiniteHistory
variable {X ι η L : Type} [LieRing L] [LieAlgebra ℚ L] [Fintype η] {s m : ℕ}
  {F : NilpotentLieFiltration L s} {b : Basis ι ℚ L} {ω : ι → ℕ}
  {hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i})}

  {J : Fin m → Type} [∀ j, Fintype (J j)]
  {fast : Submodule ℚ F.AssociatedGraded}
  {basis : Basis η ℝ (ℝ ⊗[ℚ] (F.AssociatedGraded ⧸ fast))}
  {lift : (F.AssociatedGraded ⧸ fast) →ₗ[ℚ] F.AssociatedGraded}
  {Z : F.RealPolynomialSymbolGroup (fullTaggedVariableWeight (X := X) J)}
  {Kinitial : Set (X ⊕ (Σ j, J j) → ℝ)}
  {Utag : ∀ j, Submodule ℝ (J j → ℝ)}
  {poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)} {N : X → ℕ} {Bphase : ℝ}

end CertifiedFullChartFiniteHistory
end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial _root_.MvPolynomial _root_.OAI.MvPolynomial
open scoped TensorProduct

attribute [local irreducible] weightedAdaptedRealChartHom realPolynomialSymbolHom realSymbolHomogeneousPullbackHom

namespace CertifiedFullChartFiniteHistory

variable {m s : ℕ} {X ι η L : Type} [Fintype η] [LieRing L] [LieAlgebra ℚ L]
  {F : NilpotentLieFiltration L s} {b : Basis ι ℚ L} {ω : ι → ℕ}
  {hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i})}
  {J : Fin m → Type} [∀ j, Fintype (J j)]
  {W : LieSubalgebra ℚ F.AssociatedGraded}
  {basis : Basis η ℝ (ℝ ⊗[ℚ] (F.AssociatedGraded ⧸ W.toSubmodule))}
  {lift : (F.AssociatedGraded ⧸ W.toSubmodule) →ₗ[ℚ] F.AssociatedGraded}
  {Z : F.RealPolynomialSymbolGroup (fullTaggedVariableWeight (X := X) J)}
  {Kinitial : Set (X ⊕ (Σ j, J j) → ℝ)}
  {Utag : ∀ j, Submodule ℝ (J j → ℝ)}
  {poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)} {N : X → ℕ} {Bphase : ℝ}


end CertifiedFullChartFiniteHistory
end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial _root_.MvPolynomial _root_.OAI.MvPolynomial
open scoped TensorProduct

attribute [local irreducible] realPolynomialSymbolLift realPolynomialSymbolHom realSymbolHomogeneousPullbackHom weightedAdaptedRealChartHom realChartSubstitute symbolPointwiseSubalgebra realificationLieSubalgebra PolynomialRationalGrid PolynomialSlowBound

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3

open _root_.MvPolynomial _root_.OAI.MvPolynomial

namespace NilpotentLieFiltration

open Module VectorPolynomial NilpotentLieBCHGroup
open scoped TensorProduct

attribute [local irreducible] weightedAdaptedRealChartHom realChartSubstitute

variable {σ τ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L)
    (w : σ → ℕ)

end NilpotentLieFiltration
end Erdos3

end

end OAI

end


