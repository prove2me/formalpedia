-- Prove2me | Definitions.Def_OAIErdos3B1335
-- name    : OAIErdos3B1335
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-15T19:38:06.78062+00:00
-- url     : https://prove2.me/theorems/a4d5b77e-2804-44f0-ac06-8ff1d8af148f
-- title:
--   OpenAI Erdős-3 split, definitions bundle 1336 of 1348
-- statement:
--   Definitions bundle 1336 of 1348 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs) and OpenAI's `@[simp]` lemmas from the same modules.
--
--   It imports the previous bundle `OAIErdos3B1334`, so the bundles form a chain and importing this one makes the definitions of bundles 1 to 1336 available.
--
--   Modules: `OAI.Erdos3.NilpotentLieFiltration.CertifiedFullChartFiniteHistory.AdmissibleChildAt`, `OAI.Erdos3.NilpotentLieFiltration.CertifiedFullChartFiniteHistory.BudgetedBranchTree`, `OAI.Erdos3.NilpotentLieFiltration.CertifiedFullChartFiniteHistory.BudgetedBranchTree.card_level_le_forward_prefix`, `OAI.Erdos3.NilpotentLieFiltration.CertifiedFullChartFiniteHistory.BudgetedBranchTree.card_level_le_prefix_exp`, `OAI.Erdos3.NilpotentLieFiltration.CertifiedFullChartFiniteHistory.BudgetedBranchTree.exists_representative_child`, `OAI.Erdos3.NilpotentLieFiltration.CertifiedFullChartFiniteHistory.BudgetedBranchTree.level`, `OAI.Erdos3.NilpotentLieFiltration.CertifiedFullChartFiniteHistory.BudgetedBranchTree.stage_bounds`, `OAI.Erdos3.NilpotentLieFiltration.CertifiedFullChartFiniteHistory.RepresentsCorrection`, `OAI.Erdos3.NilpotentLieFiltration.CertifiedFullChartFiniteHistory.append_admissible_is_child_at`, `OAI.Erdos3.NilpotentLieFiltration.CertifiedFullChartFiniteHistory.earlyForwardBranchTree`, `OAI.Erdos3.NilpotentLieFiltration.CertifiedFullChartFiniteHistory.exists_budgeted_reached_child_of_major_correlation_witness`, `OAI.Erdos3.NilpotentLieFiltration.CertifiedFullChartFiniteHistory.exists_early_forward_branch_tree`, `OAI.Erdos3.NilpotentLieFiltration.CertifiedFullChartFiniteHistory.exists_finite_children_at_budget`, `OAI.Erdos3.NilpotentLieFiltration.CertifiedFullChartFiniteHistory.exists_finite_children_of_stage_bounds`, `OAI.Erdos3.NilpotentLieFiltration.CertifiedFullChartFiniteHistory.exists_prefix_counted_budgeted_branch_tree`, `OAI.Erdos3.NilpotentLieFiltration.CertifiedFullChartFiniteHistory.stageBranchLog`, `OAI.Erdos3.NilpotentLieFiltration.CertifiedFullChartFiniteHistory.stageBranchLog_mono`, `OAI.Erdos3.NilpotentLieFiltration.CertifiedFullChartFiniteHistory.univInitialHistory`, `OAI.Erdos3.NilpotentLieFiltration.exists_certified_budgeted_tree_terminal_constants`, `OAI.Erdos3.NilpotentLieFiltration.exists_full_chart_finite_stage_branches`, `OAI.Erdos3.RationalFilteredNilmanifold.pairOrbitSymbol_chart_eq_of_homogeneous_eq`, `OAI.Erdos3.RationalFilteredNilmanifold.pairOrbitSymbol_polynomialOrbitRealChart`, `OAI.Erdos3.RationalFilteredNilmanifold.pairOrbit_polynomialOrbitRealChart_log`, `OAI.Erdos3.VectorPolynomial.OrdinarySliceNativeDetection`, `OAI.Erdos3.VectorPolynomial.ScalarReferenceNativeDetection`, `OAI.Erdos3.VectorPolynomial.allocatedCandidateTerminalControlConstant`, `OAI.Erdos3.VectorPolynomial.allocatedCandidateTerminalPhaseConstant`, `OAI.Erdos3.scalarJointPathEquiv`, `OAI.Erdos3.scalarJointPathEquiv_fst`, `OAI.Erdos3.scalarJointPathEquiv_snd_val`, `OAI.Erdos3.scalarNoiseIndexEquiv`, `OAI.Erdos3.scalarNoiseIndexEquiv_none`, `OAI.Erdos3.scalarNoiseIndexEquiv_some`, `OAI.Erdos3.scalarNoiseIndexEquiv_symm`, `OAI.Erdos3.scalarNoiseSupportEquiv`, `OAI.Erdos3.scalarNoiseSupportEquiv_symm_val`, `OAI.Erdos3.scalarNoiseSupportEquiv_val`, `OAI.Erdos3.trimmedSpatialWidths_scalarNoiseIndexEquiv`, `_private.Geometry.CertifiedFullChartBudgetedTreeBounds.0.OAI.Erdos3.NilpotentLieFiltration.exists_full_chart_optional_stage_branch`, `_private.Geometry.CertifiedFullChartBudgetedTreeBounds.0.OAI.Erdos3.NilpotentLieFiltration.stage_branch_numeric`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B1332

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.CertifiedFullChartBudgetedTreeBounds
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration
open Module VectorPolynomial PolynomialTranslationLie RationalFilteredNilmanifold
open scoped TensorProduct Classical

attribute [local irreducible] FullChartAdmissibleStageCorrection realSymbolGradeQuotientPolynomial realSymbolGradeEvaluation restrictedMajorCorrection fullChartStageCountConstant

variable {m : ℕ} {X : Type} [Fintype X] {ι L η : Type*}
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

local notation "Point" => (X ⊕ (Σ j, J j) → ℝ)
local notation "VP" => VectorPolynomial (X ⊕ (Σ j, J j)) ℚ
  (ℝ ⊗[ℚ] (F.AssociatedGraded ⧸ fast))
local notation "chart" => normalizedRealPolynomialChart (fun i => (N i : ℝ))
  (fullTaggedMajorTopCoordinates J poly)
local notation "Good" => FullChartAdmissibleStageCorrection F b ω hF J k fast basis lift
  Z left right K₀ Utag poly N budget

theorem stage_branch_numeric {p budget : ℝ} {r a : ℕ}
    (hp : 0 ≤ p) (hr : (r : ℝ) ≤ p) (hb : budget ≤ p) (ha : 254 ≤ a) :
    (r : ℝ) * budget ≤ (p + a) ^ a ∧ budget ≤ (p + a) ^ a := by
  have ha2 : (2 : ℝ) ≤ (a : ℝ) := by exact_mod_cast (show 2 ≤ a by omega)
  have hbase : 1 ≤ p + a := by linarith
  have hshift : p ≤ p + a := le_add_of_nonneg_right (Nat.cast_nonneg a)
  have hpower : p ^ 2 ≤ (p + a) ^ a :=
    (pow_le_pow_left₀ hp hshift 2).trans (pow_le_pow_right₀ hbase (by omega))
  have hprod : (r : ℝ) * budget ≤ p * p :=
    (mul_le_mul_of_nonneg_left hb (Nat.cast_nonneg r)).trans
      (mul_le_mul_of_nonneg_right hr hp)
  refine ⟨hprod.trans (by simpa only [pow_two] using hpower), ?_⟩
  exact hb.trans (hshift.trans (by simpa only [pow_one] using
    (pow_le_pow_right₀ hbase (show 1 ≤ a by omega))))

theorem exists_full_chart_optional_stage_branch
    (q : ℕ) (K' : Set Point) (p : ℝ) (blocks a : ℕ) (ha : 254 ≤ a)
    (hcert : RationalTaggedConstraintCertificate J Set.univ K' p blocks)
    (hp : 0 ≤ p) (hX : (Fintype.card X : ℝ) ≤ p)
    (hJ : (Fintype.card (Σ j, J j) : ℝ) ≤ p)
    (hη : (Fintype.card η : ℝ) ≤ p) (hblocks : (blocks : ℝ) ≤ p)
    (hretained : ∀ point, (∀ j, (fun i => point (Sum.inr ⟨j, i⟩)) ∈ Utag j) → point ∈ K₀)
    (hpoly : ∀ j ex, ex ≠ 0 → coefficients (poly j) ex ∈ Utag j)
    (hN : ∀ i, 1 ≤ N i) (hq : 0 < q)
    (hqcap : (q : ℝ) ≤ Real.exp ((p + a) ^ a)) (hbudget : budget ≤ (p + a) ^ a) :
    ∃ c : ℕ, (c : ℝ) ≤ Real.exp
        ((p + fullChartStageCountConstant k a) ^ fullChartStageCountConstant k a) ∧
      ∃ candidate : Fin c → VP × VP, (∀ j, Good q K' (candidate j)) ∧
        ∀ pair, Good q K' pair → ∃ j, ∀ t ∈ K',
          eval₂ t (candidate j).1 = eval₂ t pair.1 ∧
          eval₂ t (candidate j).2 = eval₂ t pair.2 ∧
          eval₂ t (realChartSubstitute chart (candidate j).1) =
            eval₂ t (realChartSubstitute chart pair.1) := by
  by_cases hex : ∃ pair, Good q K' pair
  · obtain ⟨pair, hpair⟩ := hex
    have hret : ∀ point, (∀ j, (fun z => point (Sum.inr ⟨j, z⟩)) ∈ Utag j) →
        point ∈ K' := by
      unfold FullChartAdmissibleStageCorrection at hpair
      rcases hpair with ⟨_, _, _, _, _, _, _, _, hretain, _⟩
      intro point hpoint
      exact hretain point (hretained point hpoint) hpoint
    exact exists_full_chart_finite_stage_representatives F b ω hF J k fast basis lift
      Z left right K₀ Utag poly N budget q K' p blocks a ha hcert hp hX hJ hη hblocks
      hret hpoly hN hq hqcap hbudget
  · refine ⟨0, by simpa using Real.exp_nonneg _, Fin.elim0, ?_, ?_⟩
    · intro j; exact Fin.elim0 j
    · intro pair hpair; exact (hex ⟨pair, hpair⟩).elim

theorem exists_full_chart_finite_stage_branches
    {past p : ℝ} {blocks : ℕ}
    (a : ℕ) (ha : 254 ≤ a)
    (hprevious : RationalTaggedConstraintCertificate J Set.univ K₀ past blocks)
    (hp : 0 ≤ p) (hpast : past ≤ p) (hbudget : budget ≤ p)
    (hX : (Fintype.card X : ℝ) ≤ p) (hm : (m : ℝ) ≤ p)
    (hJ : (Fintype.card (Σ j, J j) : ℝ) ≤ p)
    (hη : (Fintype.card η : ℝ) ≤ p)
    (hblocks : ((blocks + Fintype.card η * m : ℕ) : ℝ) ≤ p)
    (hretained : ∀ point, (∀ j, (fun i => point (Sum.inr ⟨j, i⟩)) ∈ Utag j) → point ∈ K₀)
    (hpoly : ∀ j ex, ex ≠ 0 → coefficients (poly j) ex ∈ Utag j)
    (hN : ∀ i, 1 ≤ N i) :
    ∃ count : ℕ, (count : ℝ) ≤ Real.exp
        ((Fintype.card η : ℝ) * budget + (p + 8) ^ 8 +
          (p + fullChartStageCountConstant k a) ^ fullChartStageCountConstant k a) ∧
      ∃ candidate : Fin count → (ℕ × Set Point) × (VP × VP),
        (∀ i, Good (candidate i).1.1 (candidate i).1.2 (candidate i).2) ∧
        ∀ q K' pair, Good q K' pair → ∃ i,
          (candidate i).1 = (q, K') ∧ ∀ t ∈ K',
            eval₂ t (candidate i).2.1 = eval₂ t pair.1 ∧
            eval₂ t (candidate i).2.2 = eval₂ t pair.2 ∧
            eval₂ t (realChartSubstitute chart (candidate i).2.1) =
              eval₂ t (realChartSubstitute chart pair.1) := by
  obtain ⟨n, hn, branches, hbranches, hcover⟩ :=
    exists_fullChart_admissible_stage_branches F b ω hF J k fast basis lift
      Z left right K₀ Utag poly N budget hprevious hp hpast hbudget hm hJ hblocks
  let validLabel := fun (l : ℕ × Set Point) (pair : VP × VP) => Good l.1 l.2 pair
  let relLabel := fun (l : ℕ × Set Point) (pair pair' : VP × VP) => ∀ t ∈ l.2,
    eval₂ t pair.1 = eval₂ t pair'.1 ∧ eval₂ t pair.2 = eval₂ t pair'.2 ∧
    eval₂ t (realChartSubstitute chart pair.1) = eval₂ t (realChartSubstitute chart pair'.1)
  let valid := fun i => validLabel (branches i)
  let rel := fun i => relLabel (branches i)
  have hnum := stage_branch_numeric hp hη hbudget ha
  have hbranch : ∀ i : Fin n, ∃ c : ℕ,
      (c : ℝ) ≤ Real.exp ((p + fullChartStageCountConstant k a) ^ fullChartStageCountConstant k a) ∧
      ∃ candidate : Fin c → VP × VP, (∀ j, valid i (candidate j)) ∧
        ∀ pair, valid i pair → ∃ j, rel i (candidate j) pair := by
    intro i
    dsimp only [valid, rel, validLabel, relLabel]
    exact exists_full_chart_optional_stage_branch F b ω hF J k fast basis lift
      Z left right K₀ Utag poly N budget (branches i).1 (branches i).2
      p (blocks + Fintype.card η * m) a ha (hbranches i).2.2 hp hX hJ hη hblocks
      hretained hpoly hN (hbranches i).1
      (((Nat.cast_le.mpr (hbranches i).2.1).trans (Nat.floor_le (Real.exp_nonneg _))).trans
        (Real.exp_le_exp.mpr hnum.1)) hnum.2
  obtain ⟨count, hcount, candidate, hvalid, hcomplete⟩ :=
    exists_finite_classified_representatives branches validLabel relLabel
      (fun l pair => hcover l.1 l.2 pair) hbranch
  refine ⟨count, ?_, candidate, hvalid, fun q K' pair => hcomplete (q, K') pair⟩
  exact (hcount.trans (mul_le_mul_of_nonneg_right hn (Real.exp_nonneg _))).trans_eq
    (Real.exp_add _ _).symm

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3

open scoped BigOperators

namespace NilpotentLieFiltration

end NilpotentLieFiltration

end Erdos3

end

section

namespace Erdos3.NilpotentLieFiltration.CertifiedFullChartFiniteHistory
open Module VectorPolynomial
open scoped TensorProduct Classical

attribute [local irreducible] FullChartAdmissibleStageCorrection realSymbolGradeEvaluation restrictedMajorCorrection outer fullChartStageCountConstant

variable {m : ℕ} {X : Type} [Fintype X] {ι L η : Type*}
  [LieRing L] [LieAlgebra ℚ L] [Fintype η] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
  (J : Fin m → Type) [∀ j, Fintype (J j)]
  (fast : Submodule ℚ F.AssociatedGraded)
  (basis : Basis η ℝ (ℝ ⊗[ℚ] (F.AssociatedGraded ⧸ fast)))
  (lift : (F.AssociatedGraded ⧸ fast) →ₗ[ℚ] F.AssociatedGraded)
  (Z : F.RealPolynomialSymbolGroup (fullTaggedVariableWeight (X := X) J))
  (Utag : ∀ j, Submodule ℝ (J j → ℝ))
  (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)) (N : X → ℕ) (Bphase : ℝ)

local notation "Point" => (X ⊕ (Σ j, J j) → ℝ)
local notation "VP" => VectorPolynomial (X ⊕ (Σ j, J j)) ℚ
  (ℝ ⊗[ℚ] (F.AssociatedGraded ⧸ fast))
local notation "State" => CertifiedFullChartFiniteHistory F b ω hF J fast basis lift Z
  Set.univ Utag poly N Bphase
local notation "chart" => normalizedRealPolynomialChart (fun i => (N i : ℝ))
  (fullTaggedMajorTopCoordinates J poly)

def RepresentsCorrection {n : ℕ} (Hnext : State (n + 1)) (q : ℕ)
    (K' : Set Point) (pair : VP × VP) : Prop :=
  Hnext.q n = q ∧ Hnext.K = K' ∧ ∀ t ∈ K',
    eval₂ t (Hnext.slow n) = eval₂ t pair.1 ∧
    eval₂ t (Hnext.rat n) = eval₂ t pair.2 ∧
    eval₂ t (realChartSubstitute chart (Hnext.slow n)) =
      eval₂ t (realChartSubstitute chart pair.1)

variable {F b ω hF J fast basis lift Z Utag poly N Bphase}

end Erdos3.NilpotentLieFiltration.CertifiedFullChartFiniteHistory

end

section

namespace Erdos3.NilpotentLieFiltration.CertifiedFullChartFiniteHistory
open Module VectorPolynomial
open scoped TensorProduct Classical

attribute [local irreducible] FullChartAdmissibleStageCorrection realSymbolGradeEvaluation restrictedMajorCorrection outer fullChartStageCountConstant

variable {m : ℕ} {X : Type} [Fintype X] {ι L η : Type*}
  [LieRing L] [LieAlgebra ℚ L] [Fintype η] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
  (J : Fin m → Type) [∀ j, Fintype (J j)]
  (fast : Submodule ℚ F.AssociatedGraded)
  (basis : Basis η ℝ (ℝ ⊗[ℚ] (F.AssociatedGraded ⧸ fast)))
  (lift : (F.AssociatedGraded ⧸ fast) →ₗ[ℚ] F.AssociatedGraded)
  (Z : F.RealPolynomialSymbolGroup (fullTaggedVariableWeight (X := X) J))
  (Utag : ∀ j, Submodule ℝ (J j → ℝ))
  (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)) (N : X → ℕ) (Bphase : ℝ)

local notation "State" => CertifiedFullChartFiniteHistory F b ω hF J fast basis lift Z
  Set.univ Utag poly N Bphase

variable {F b ω hF J fast basis lift Z Utag poly N Bphase}

variable (F b ω hF J fast basis lift Z Utag poly N Bphase)

noncomputable def univInitialHistory : State 0 :=
  initial F b ω hF J fast basis lift Z Set.univ Utag poly N Bphase
    (fun _ _ _ => Set.mem_univ _)

variable {F b ω hF J fast basis lift Z Utag poly N Bphase}
variable {depth : ℕ} {p : ℝ}

end Erdos3.NilpotentLieFiltration.CertifiedFullChartFiniteHistory

end

section

namespace Erdos3.NilpotentLieFiltration.CertifiedFullChartFiniteHistory
open Module VectorPolynomial
open scoped TensorProduct Classical

attribute [local irreducible] FullChartAdmissibleStageCorrection realSymbolGradeEvaluation restrictedMajorCorrection outer fullChartStageCountConstant

variable {m : ℕ} {X : Type} [Fintype X] {ι L η : Type*}
  [LieRing L] [LieAlgebra ℚ L] [Fintype η] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
  (J : Fin m → Type) [∀ j, Fintype (J j)]
  (fast : Submodule ℚ F.AssociatedGraded)
  (basis : Basis η ℝ (ℝ ⊗[ℚ] (F.AssociatedGraded ⧸ fast)))
  (lift : (F.AssociatedGraded ⧸ fast) →ₗ[ℚ] F.AssociatedGraded)
  (Z : F.RealPolynomialSymbolGroup (fullTaggedVariableWeight (X := X) J))
  (Utag : ∀ j, Submodule ℝ (J j → ℝ))
  (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)) (N : X → ℕ) (Bphase : ℝ)

local notation "Point" => (X ⊕ (Σ j, J j) → ℝ)
local notation "VP" => VectorPolynomial (X ⊕ (Σ j, J j)) ℚ
  (ℝ ⊗[ℚ] (F.AssociatedGraded ⧸ fast))
local notation "State" => CertifiedFullChartFiniteHistory F b ω hF J fast basis lift Z
  Set.univ Utag poly N Bphase

def AdmissibleChildAt (budget : ℝ) {n : ℕ} (H : State n) (Hnext : State (n + 1)) : Prop :=
  FullChartAdmissibleStageCorrection F b ω hF J (n + 1) fast basis lift
    Z H.outer.1 H.outer.2 H.K Utag poly N budget (Hnext.q n) Hnext.K
      (Hnext.slow n, Hnext.rat n) ∧
  ∀ j < n, Hnext.slow j = H.slow j ∧ Hnext.rat j = H.rat j ∧ Hnext.q j = H.q j

variable {F b ω hF J fast basis lift Z Utag poly N Bphase}

omit [Fintype X] in
theorem append_admissible_is_child_at {n : ℕ} (H : State n)
    (budget : ℝ) (hcap : budget ≤ Bphase) (q : ℕ)
    (K' : Set Point) (pair : VP × VP)
    (hpair : FullChartAdmissibleStageCorrection F b ω hF J (n + 1) fast basis lift
      Z H.outer.1 H.outer.2 H.K Utag poly N budget q K' pair) :
    AdmissibleChildAt F b ω hF J fast basis lift Z Utag poly N Bphase budget H
      (H.append_admissible budget hcap q K' pair hpair) := by
  refine ⟨?_, fun j hj => append_admissible_prefix H budget hcap q K' pair hpair j hj⟩
  rw [append_admissible_K, (append_admissible_entry H budget hcap q K' pair hpair).1,
    (append_admissible_entry H budget hcap q K' pair hpair).2.1,
    (append_admissible_entry H budget hcap q K' pair hpair).2.2]
  exact hpair

theorem exists_finite_children_at_budget {n : ℕ} (H : State n)
    (budget : ℝ) (hcap : budget ≤ Bphase)
    {p : ℝ} (hp : 0 ≤ p) (hpast : Bphase ≤ p) (hbudget : budget ≤ p)
    (hX : (Fintype.card X : ℝ) ≤ p) (hm : (m : ℝ) ≤ p)
    (hJ : (Fintype.card (Σ j, J j) : ℝ) ≤ p)
    (hη : (Fintype.card η : ℝ) ≤ p)
    (hblocks : (((n + 1) * (Fintype.card η * m) : ℕ) : ℝ) ≤ p)
    (hpoly : ∀ j ex, ex ≠ 0 → coefficients (poly j) ex ∈ Utag j)
    (hN : ∀ i, 1 ≤ N i) :
    ∃ children : Finset (State (n + 1)),
      (children.card : ℝ) ≤ Real.exp
        ((Fintype.card η : ℝ) * budget + (p + 8) ^ 8 +
          (p + fullChartStageCountConstant (n + 1) 254) ^
            fullChartStageCountConstant (n + 1) 254) ∧
      (∀ Hnext ∈ children, AdmissibleChildAt F b ω hF J fast basis lift Z
        Utag poly N Bphase budget H Hnext) ∧
      ∀ q K' pair, FullChartAdmissibleStageCorrection F b ω hF J (n + 1)
        fast basis lift Z H.outer.1 H.outer.2 H.K Utag poly N budget q K' pair →
        ∃ Hnext ∈ children, RepresentsCorrection F b ω hF J fast basis lift Z
          Utag poly N Bphase Hnext q K' pair := by
  obtain ⟨count, hcount, candidate, hgood, hcover⟩ :=
    exists_full_chart_finite_stage_branches F b ω hF J (n + 1) fast basis lift
      Z H.outer.1 H.outer.2 H.K Utag poly N budget 254 (by omega)
      H.certificate hp hpast hbudget hX hm hJ hη
      (by simpa only [Nat.succ_mul] using hblocks)
      (fun point hpoint => H.retained point (Set.mem_univ _) hpoint) hpoly hN
  let next (i : Fin count) : State (n + 1) :=
    H.append_admissible budget hcap (candidate i).1.1 (candidate i).1.2
      (candidate i).2 (hgood i)
  refine ⟨Finset.univ.image next, ?_, ?_, ?_⟩
  · exact (Nat.cast_le.mpr ((Finset.card_image_le).trans_eq
      (Finset.card_fin count))).trans hcount
  · intro Hnext hmem
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hmem
    exact append_admissible_is_child_at H budget hcap _ _ _ (hgood i)
  · intro q K' pair hpair
    obtain ⟨i, hlabel, heval⟩ := hcover q K' pair hpair
    refine ⟨next i, Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩, ?_⟩
    have hentry := append_admissible_entry H budget hcap
      (candidate i).1.1 (candidate i).1.2 (candidate i).2 (hgood i)
    refine ⟨hentry.2.2.trans (congrArg Prod.fst hlabel), ?_, ?_⟩
    · exact (append_admissible_K H budget hcap _ _ _ (hgood i)).trans
        (congrArg Prod.snd hlabel)
    · intro t ht
      change eval₂ t ((next i).slow n) = _ ∧ _
      dsimp only [next]
      rw [hentry.1, hentry.2.1]
      with_reducible exact heval t ht

end Erdos3.NilpotentLieFiltration.CertifiedFullChartFiniteHistory

end

section

namespace Erdos3.NilpotentLieFiltration.CertifiedFullChartFiniteHistory
open Module VectorPolynomial
open scoped TensorProduct Classical

attribute [local irreducible] FullChartAdmissibleStageCorrection realSymbolGradeEvaluation restrictedMajorCorrection outer fullChartStageCountConstant

variable {m : ℕ} {X : Type} [Fintype X] {ι L η : Type*}
  [LieRing L] [LieAlgebra ℚ L] [Fintype η] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
  (J : Fin m → Type) [∀ j, Fintype (J j)]
  (fast : Submodule ℚ F.AssociatedGraded)
  (basis : Basis η ℝ (ℝ ⊗[ℚ] (F.AssociatedGraded ⧸ fast)))
  (lift : (F.AssociatedGraded ⧸ fast) →ₗ[ℚ] F.AssociatedGraded)
  (Z : F.RealPolynomialSymbolGroup (fullTaggedVariableWeight (X := X) J))
  (Utag : ∀ j, Submodule ℝ (J j → ℝ))
  (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)) (N : X → ℕ) (Bphase : ℝ)


variable {F b ω hF J fast basis lift Z Utag poly N Bphase}
variable {depth : ℕ} {p : ℝ}

end Erdos3.NilpotentLieFiltration.CertifiedFullChartFiniteHistory

end

section

namespace Erdos3.NilpotentLieFiltration.CertifiedFullChartFiniteHistory
open Module VectorPolynomial
open scoped TensorProduct Classical

attribute [local irreducible] FullChartAdmissibleStageCorrection realSymbolGradeEvaluation restrictedMajorCorrection outer

end Erdos3.NilpotentLieFiltration.CertifiedFullChartFiniteHistory

end

section

namespace Erdos3.NilpotentLieFiltration.CertifiedFullChartFiniteHistory
open Module VectorPolynomial
open scoped TensorProduct Classical

attribute [local irreducible] FullChartAdmissibleStageCorrection realSymbolGradeEvaluation restrictedMajorCorrection outer fullChartStageCountConstant

variable {m : ℕ} {X : Type} [Fintype X] {ι L η : Type*}
  [LieRing L] [LieAlgebra ℚ L] [Fintype η] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
  (J : Fin m → Type) [∀ j, Fintype (J j)]
  (fast : Submodule ℚ F.AssociatedGraded)
  (basis : Basis η ℝ (ℝ ⊗[ℚ] (F.AssociatedGraded ⧸ fast)))
  (lift : (F.AssociatedGraded ⧸ fast) →ₗ[ℚ] F.AssociatedGraded)
  (Z : F.RealPolynomialSymbolGroup (fullTaggedVariableWeight (X := X) J))
  (Utag : ∀ j, Submodule ℝ (J j → ℝ))
  (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)) (N : X → ℕ) (Bphase : ℝ)

local notation "Point" => (X ⊕ (Σ j, J j) → ℝ)
local notation "VP" => VectorPolynomial (X ⊕ (Σ j, J j)) ℚ
  (ℝ ⊗[ℚ] (F.AssociatedGraded ⧸ fast))
local notation "State" => CertifiedFullChartFiniteHistory F b ω hF J fast basis lift Z
  Set.univ Utag poly N Bphase

variable (stageBudget : ℕ → ℝ)

structure BudgetedBranchTree (depth : ℕ) (p : ℝ) where
  children : ∀ n, State n → Finset (State (n + 1))
  card : ∀ n, n < depth → ∀ H, (children n H).card ≤
    ⌈Real.exp ((Fintype.card η : ℝ) * stageBudget n + (p + 8) ^ 8 +
      (p + fullChartStageCountConstant (n + 1) 254) ^
        fullChartStageCountConstant (n + 1) 254)⌉₊
  admissible : ∀ n, n < depth → ∀ H Hnext, Hnext ∈ children n H →
    AdmissibleChildAt F b ω hF J fast basis lift Z Utag poly N Bphase (stageBudget n) H Hnext
  complete : ∀ n, n < depth → ∀ H q K' pair,
    FullChartAdmissibleStageCorrection F b ω hF J (n + 1) fast basis lift
      Z H.outer.1 H.outer.2 H.K Utag poly N (stageBudget n) q K' pair →
    ∃ Hnext ∈ children n H, RepresentsCorrection F b ω hF J fast basis lift Z
      Utag poly N Bphase Hnext q K' pair

variable {F b ω hF J fast basis lift Z Utag poly N Bphase stageBudget}

variable {depth : ℕ} {p : ℝ}

noncomputable def BudgetedBranchTree.level
    (T : BudgetedBranchTree F b ω hF J fast basis lift Z Utag poly N Bphase stageBudget depth p)
    (n : ℕ) : Finset (State n) :=
  finiteGradedBranchLevel (univInitialHistory F b ω hF J fast basis lift Z Utag poly N Bphase)
    T.children n

omit [Fintype X] in

theorem BudgetedBranchTree.exists_representative_child
    (T : BudgetedBranchTree F b ω hF J fast basis lift Z Utag poly N Bphase stageBudget depth p)
    {n : ℕ} (hn : n < depth) {H : State n} (hH : H ∈ T.level n)
    (q : ℕ) (K' : Set Point) (pair : VP × VP)
    (hpair : FullChartAdmissibleStageCorrection F b ω hF J (n + 1) fast basis lift
      Z H.outer.1 H.outer.2 H.K Utag poly N (stageBudget n) q K' pair) :
    ∃ Hnext ∈ T.level (n + 1),
      AdmissibleChildAt F b ω hF J fast basis lift Z Utag poly N Bphase (stageBudget n) H Hnext ∧
      RepresentsCorrection F b ω hF J fast basis lift Z Utag poly N Bphase Hnext q K' pair := by
  obtain ⟨Hnext, hmem, hrep⟩ := T.complete n hn H q K' pair hpair
  exact ⟨Hnext, finiteGradedBranchLevel_child_mem _ T.children hH hmem,
    T.admissible n hn H Hnext hmem, hrep⟩

end Erdos3.NilpotentLieFiltration.CertifiedFullChartFiniteHistory

end

section

namespace Erdos3.NilpotentLieFiltration.CertifiedFullChartFiniteHistory
open Module VectorPolynomial
open scoped TensorProduct Classical

attribute [local irreducible] FullChartAdmissibleStageCorrection realSymbolGradeEvaluation restrictedMajorCorrection outer fullChartStageCountConstant

variable {m : ℕ} {X : Type} [Fintype X] {ι L η : Type*}
  [LieRing L] [LieAlgebra ℚ L] [Fintype η] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
  (J : Fin m → Type) [∀ j, Fintype (J j)]
  (fast : Submodule ℚ F.AssociatedGraded)
  (basis : Basis η ℝ (ℝ ⊗[ℚ] (F.AssociatedGraded ⧸ fast)))
  (lift : (F.AssociatedGraded ⧸ fast) →ₗ[ℚ] F.AssociatedGraded)
  (Z : F.RealPolynomialSymbolGroup (fullTaggedVariableWeight (X := X) J))
  (Utag : ∀ j, Submodule ℝ (J j → ℝ))
  (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)) (N : X → ℕ) (Bphase : ℝ)


variable {F b ω hF J fast basis lift Z Utag poly N Bphase}
variable {stageBudget cumulative : ℕ → ℝ} {depth : ℕ} {p : ℝ}

omit [Fintype X] in

theorem BudgetedBranchTree.stage_bounds
    (T : BudgetedBranchTree F b ω hF J fast basis lift Z Utag poly N Bphase stageBudget depth p)
    (hmono : ∀ n < depth, cumulative n ≤ cumulative (n + 1))
    (hcap : ∀ n < depth, stageBudget n ≤ cumulative (n + 1)) :
    ∀ n, n ≤ depth → ∀ H ∈ T.level n, StageBounds stageBudget cumulative H := by
  apply finiteGradedBranchLevel_all_valid
    (univInitialHistory F b ω hF J fast basis lift Z Utag poly N Bphase)
    T.children depth (fun _ H => StageBounds stageBudget cumulative H)
  · unfold univInitialHistory
    exact StageBounds.initial stageBudget cumulative (fun _ _ _ => Set.mem_univ _)
  · intro n hn H _ hH Hnext hnext
    have hadmissible := T.admissible n hn H Hnext hnext
    exact hH.of_admissible_child Hnext hadmissible.2 hadmissible.1
      (hmono n hn) (hcap n hn)

end Erdos3.NilpotentLieFiltration.CertifiedFullChartFiniteHistory

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.CertifiedFullChartBudgetedTreeTerminal
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration.CertifiedFullChartFiniteHistory
open Module VectorPolynomial
open scoped TensorProduct Classical

attribute [local irreducible] FullChartAdmissibleStageCorrection realSymbolGradeEvaluation restrictedMajorCorrection outer

theorem exists_budgeted_reached_child_of_major_correlation_witness (m n : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧
      ∀ {X L ι η : Type} [Fintype X] [DecidableEq X] [Fintype η]
        [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
        (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
        (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
        (J : Fin m → Type) [∀ j, Fintype (J j)]
        (fast : Submodule ℚ F.AssociatedGraded)
        (basis : Basis η ℝ (ℝ ⊗[ℚ] (F.AssociatedGraded ⧸ fast)))
        (lift : (F.AssociatedGraded ⧸ fast) →ₗ[ℚ] F.AssociatedGraded),
      BasisGradedSubmodule (F.associatedGradedBasis b ω hF) ω fast →
      (∀ y, fast.mkQ (lift y) = y) →
      ∀ (Z : F.RealPolynomialSymbolGroup (fullTaggedVariableWeight (X := X) J))
        (U : ∀ j, Submodule ℝ (J j → ℝ))
        (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)) (N : X → ℕ)
        (Bphase pTree pPhase Rrank : ℝ) (stageBudget : ℕ → ℝ) (depth : ℕ)
        (T : BudgetedBranchTree F b ω hF J fast basis lift Z U poly N Bphase stageBudget depth pTree)
        (H : CertifiedFullChartFiniteHistory F b ω hF J fast basis lift Z
          Set.univ U poly N Bphase n),
      n < depth → H ∈ T.level n → (pPhase + C) ^ C ≤ stageBudget n →
      Nonempty (FullChartMajorCorrelationWitness F b ω hF J (n + 1) fast basis
        Z H.outer.1 H.outer.2 N poly U pPhase Rrank C) →
      ∃ (q : ℕ) (K : Set ((X ⊕ (Σ j, J j)) → ℝ))
        (pair : VectorPolynomial (X ⊕ (Σ j, J j)) ℚ (ℝ ⊗[ℚ] (F.AssociatedGraded ⧸ fast)) ×
          VectorPolynomial (X ⊕ (Σ j, J j)) ℚ (ℝ ⊗[ℚ] (F.AssociatedGraded ⧸ fast))),
        FullChartAdmissibleStageCorrection F b ω hF J (n + 1) fast basis lift
          Z H.outer.1 H.outer.2 H.K U poly N ((pPhase + C) ^ C) q K pair ∧
        ∃ Hnext ∈ T.level (n + 1),
          AdmissibleChildAt F b ω hF J fast basis lift Z U poly N Bphase (stageBudget n) H Hnext ∧
          RepresentsCorrection F b ω hF J fast basis lift Z U poly N Bphase Hnext q K pair := by
  obtain ⟨C, hC, hsource⟩ :=
    exists_certified_full_chart_decomposition_of_major_correlation_witness m (n + 1) (by omega)
  refine ⟨C, hC, ?_⟩
  intro X L ι η _ _ _ _ _ s F b ω hF J _ fast basis lift hfast hsection
    Z U poly N Bphase pTree pPhase Rrank stageBudget depth T H hn hH hbudget hcorrelation
  have hlower : ∀ t ∈ H.K, ∀ j < n + 1,
      F.realSymbolGradeEvaluation b ω hF (fullTaggedVariableWeight J) j t
        (H.outer.1⁻¹ * Z * H.outer.2⁻¹).coord ∈ fast.baseChange ℝ := by
    intro t ht j hj
    exact H.invariant_outer t ht j (by omega)
  have hdecomposition := hsource F b ω hF J fast basis lift hfast hsection
    Z H.outer.1 H.outer.2 H.K H.dilation hlower N poly U pPhase Rrank hcorrelation
  obtain ⟨q, K, pair, hpair⟩ :=
    CertifiedFullChartDetectedDecomposition.exists_admissible_stage
      F b ω hF J (n + 1) fast basis lift Z H.outer.1 H.outer.2 H.K U poly N
      ((pPhase + C) ^ C) hdecomposition
  refine ⟨q, K, pair, hpair, ?_⟩
  have hpairB := FullChartAdmissibleStageCorrection.mono_budget hpair hbudget
  exact T.exists_representative_child hn hH q K pair hpairB

end Erdos3.NilpotentLieFiltration.CertifiedFullChartFiniteHistory

end

section

namespace Erdos3.NilpotentLieFiltration
open Module VectorPolynomial
open scoped TensorProduct Classical

attribute [local irreducible] FullChartAdmissibleStageCorrection realSymbolGradeEvaluation restrictedMajorCorrection CertifiedFullChartFiniteHistory.outer

theorem exists_certified_budgeted_tree_terminal_constants (s m a : ℕ) :
    ∃ Ccontrol : ℕ, 2 ≤ Ccontrol ∧ ∃ Cphase : ℕ → ℕ,
      (∀ n, 2 ≤ Cphase n) ∧
    ∀ {X L ι η : Type} [Fintype X] [DecidableEq X] [Fintype ι] [Fintype η]
      [LieRing L] [LieAlgebra ℚ L]
      (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
      (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
      (J : Fin m → Type) [∀ j, Fintype (J j)]
      (fast : Submodule ℚ F.AssociatedGraded)
      (basis : Basis η ℝ (ℝ ⊗[ℚ] (F.AssociatedGraded ⧸ fast)))
      (lift : (F.AssociatedGraded ⧸ fast) →ₗ[ℚ] F.AssociatedGraded),
      BasisGradedSubmodule (F.associatedGradedBasis b ω hF) ω fast →
      (∀ y, fast.mkQ (lift y) = y) →
    ∀ (Z : F.RealPolynomialSymbolGroup (fullTaggedVariableWeight (X := X) J))
      (Utag : ∀ j, Submodule ℝ (J j → ℝ))
      (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)) (N : X → ℕ)
      (Bphase B pTree Rrank : ℝ) (H qS : ℕ)
      (cap cumulative pControl pPhase : ℕ → ℝ)
      (T : CertifiedFullChartFiniteHistory.BudgetedBranchTree F b ω hF J fast basis lift
        Z Utag poly N Bphase cap s pTree),
      1 ≤ H → 0 < qS →
      (∀ n ≤ s, 0 ≤ pControl n) →
      (∀ n ≤ s, 0 ≤ cumulative n) →
      (∀ n < s, cumulative n ≤ cumulative (n + 1)) →
      (∀ n < s, cap n ≤ cumulative (n + 1)) →
      (∀ n ≤ s, ∀ j < n, cap j ≤ cumulative n) →
      (∀ n < s, (pPhase n + Cphase n) ^ Cphase n ≤ cap n) →
      (∀ n ≤ s, (Fintype.card ι : ℝ) ≤ pControl n) →
      (∀ n ≤ s, (Fintype.card (X ⊕ (Σ j, J j)) : ℝ) ≤ pControl n) →
      (∀ n ≤ s, (H : ℝ) ≤ Real.exp (pControl n)) →
      (∀ i j z, RationalHeightLE ((F.associatedGradedBasis b ω hF).repr
        ⁅F.associatedGradedBasis b ω hF i, F.associatedGradedBasis b ω hF j⁆ z) H) →
      (∀ n ≤ s, (qS : ℝ) * Real.exp ((s : ℝ) * (Fintype.card η : ℝ) * cumulative n) ≤
        Real.exp (pControl n)) →
      (∀ n ≤ s, (Fintype.card η : ℝ) * B * Real.exp (cumulative n) ≤
        Real.exp ((pControl n + 2) ^ a)) →
      (∀ i j, |((F.associatedGradedBasis b ω hF).baseChange ℝ).repr
        (lift.baseChange ℝ (basis j)) i| ≤ B) →
      (∀ j, (fun i => ((F.associatedGradedBasis b ω hF).baseChange ℝ).repr
        (lift.baseChange ℝ (basis j)) i) ∈ realDenominatorGrid qS) →
      (∀ n, n ≤ s → ∀ history ∈ T.level n,
        FullChartControlledFactors F b ω hF J poly N history.outer.1 history.outer.2
          ((pControl n + Ccontrol) ^ Ccontrol)) ∧
      ((∀ n, n < s → ∀ history ∈ T.level n,
        Nonempty (FullChartMajorCorrelationWitness F b ω hF J (n + 1) fast basis
          Z history.outer.1 history.outer.2 N poly Utag (pPhase n) Rrank (Cphase n))) →
    ∃ history ∈ T.level s,
      FullChartControlledFactors F b ω hF J poly N history.outer.1 history.outer.2
        ((pControl s + Ccontrol) ^ Ccontrol) ∧
      RationalTaggedConstraintCertificate J Set.univ history.K (cumulative s)
        (s * (Fintype.card η * m)) ∧
      ∀ point ∈ history.K,
        eval₂ point (F.realGradedSymbolPolynomial b ω hF (fullTaggedVariableWeight J)
          (history.outer.1⁻¹ * Z * history.outer.2⁻¹).coord) ∈ fast.baseChange ℝ) := by
  obtain ⟨Ccontrol, hCcontrol, hcontrol⟩ := exists_certified_full_chart_history_control s a
  let Cphase : ℕ → ℕ := fun n => Classical.choose
    (CertifiedFullChartFiniteHistory.exists_budgeted_reached_child_of_major_correlation_witness m n)
  have hphase (n : ℕ) := Classical.choose_spec
    (CertifiedFullChartFiniteHistory.exists_budgeted_reached_child_of_major_correlation_witness m n)
  refine ⟨Ccontrol, hCcontrol, Cphase, fun n => (hphase n).1, ?_⟩
  intro X L ι η _ _ _ _ _ _ F b ω hF J _ fast basis lift hfast hsection
    Z Utag poly N Bphase B pTree Rrank H qS cap cumulative pControl pPhase T hH hqS
    hp hcumulative hmono hcap hprefix hdetect hι hσ hHp hstructure hden hcost hentry hgrid
  have hbounds := T.stage_bounds hmono hcap
  have hcontrolled (n : ℕ) (hn : n ≤ s)
      (history : CertifiedFullChartFiniteHistory F b ω hF J fast basis lift
        Z Set.univ Utag poly N Bphase n) (hmem : history ∈ T.level n) :
      FullChartControlledFactors F b ω hF J poly N history.outer.1 history.outer.2
        ((pControl n + Ccontrol) ^ Ccontrol) := by
    let hsmall := (hbounds n hn history hmem).to_budget (hprefix n hn)
    have hactual := hcontrol F b ω hF J fast basis lift Z Set.univ Utag poly N
      (cumulative n) B (pControl n) H qS n hH (hp n hn) (hcumulative n hn) hqS hn
      (hι n hn) (hσ n hn) (hHp n hn) hstructure (hden n hn) (hcost n hn)
      hentry hgrid hsmall
    dsimp only [hsmall] at hactual
    rw [(hbounds n hn history hmem).to_budget_outer (hprefix n hn)] at hactual
    exact hactual
  refine ⟨hcontrolled, ?_⟩
  intro hsource
  have hreached : ∀ n, n ≤ s → (T.level n).Nonempty := by
    intro n
    induction n with
    | zero =>
      intro _
      exact ⟨CertifiedFullChartFiniteHistory.univInitialHistory F b ω hF J fast basis lift
        Z Utag poly N Bphase, by
          change _ ∈ finiteGradedBranchLevel _ _ 0
          exact (finiteGradedBranchLevel_mem_zero _ _ _).mpr rfl⟩
    | succ n ih =>
      intro hn
      have hns : n < s := Nat.lt_of_succ_le hn
      obtain ⟨history, hmem⟩ := ih (Nat.le_of_succ_le hn)
      have hcorr := hsource n hns history hmem
      obtain ⟨q, K, pair, _, next, hnext, _, _⟩ := (hphase n).2
        F b ω hF J fast basis lift hfast hsection Z Utag poly N Bphase pTree
        (pPhase n) Rrank cap s T history hns hmem (hdetect n hns) hcorr
      exact ⟨next, hnext⟩
  obtain ⟨history, hmem⟩ := hreached s le_rfl
  exact ⟨history, hmem, hcontrolled s le_rfl history hmem,
    (hbounds s le_rfl history hmem).certificate, history.terminal_mem_fast hfast⟩

end Erdos3.NilpotentLieFiltration

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.AllocatedCandidateBudgetedTreeTerminal
namespace OAI

section

namespace Erdos3.VectorPolynomial
open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped Classical TensorProduct BigOperators

noncomputable def allocatedCandidateTerminalControlConstant (s m a : ℕ) : ℕ :=
  Classical.choose (exists_certified_budgeted_tree_terminal_constants s m a)

noncomputable def allocatedCandidateTerminalPhaseConstant (s m a : ℕ) : ℕ → ℕ :=
  Classical.choose (Classical.choose_spec
    (exists_certified_budgeted_tree_terminal_constants s m a)).2

attribute [local irreducible] weightedAdaptedRealChartHom realPolynomialSymbolHom realSymbolHomogeneousPullbackHom realSymbolGradeEvaluation CertifiedFullChartFiniteHistory.outer

variable {m : ℕ}
  {G X : Type}
  [Fintype G]
  [Fintype X]
  [DecidableEq X]
  {I Deck J : Fin m → Type}
  [∀ j, Fintype (I j)]
  [∀ j, Fintype (J j)]
  {n : Fin m → ℕ}
  {B : LayerSamplerAxis I n → Type}
  [∀ a, Fintype (B a)]
  {U : ∀ j, Submodule ℝ (J j → ℝ)}
  {btag : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
  {Rad σ : Fin m → ℝ}
  {S : LayerSamplerScale (G := G) B U btag Rad σ}
  {hb : ∀ j, span ℤ (Set.range (btag j)) = projectedIntegerLattice (euclideanSubspace (U j))}
  {o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j))}
  {hRad : ∀ j, 0 < Rad j}
  {hσ : ∀ j, 0 < σ j}
  {N : X → ℕ}
  {poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)}
  {hm : ∀ j e, coefficients (poly j) e ∈ U j}
  {τ ξ : ℝ}
  {stride : X → ℕ}
  {cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride)}
  {center : CoefficientTorus (K := LayerSamplerVariables G I n B) U}
  [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
  {L M : Type}
  [LieRing L]
  [LieAlgebra ℚ L]
  [LieRing M]
  [LieAlgebra ℚ M]
  {s d : ℕ}
  {D : RationalFilteredNilmanifold L s d}
  {Fmark : NilpotentLieFiltration M s}
  {φ : L →ₗ⁅ℚ⁆ M}
  {marked : Fmark.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)}
  {observable : (X → ℤ) → D.Space → ℂ}
  {weight : (X → ℤ) → ℂ}

namespace AllocatedExternalCandidateProblem

variable {cost massThreshold scoreThreshold : ℝ}
  (keep : LayerSamplerVariables G I n B → Prop)
  {ι κ χ η : Type}
  [Fintype ι]
  [Fintype κ]
  [Fintype χ]
  [Fintype η]
  (bD : Basis ι ℚ L)
  (ω : ι → ℕ)
  (hD : ∀ j, D.filtration.layer j = span ℚ (bD '' {i | j ≤ ω i}))
  (bF : Basis κ ℚ M)
  (ν : κ → ℕ)
  (hF : ∀ j, Fmark.layer j = span ℚ (bF '' {i | j ≤ ν i}))
  (hφ : ∀ j, ∀ x ∈ D.filtration.layer j, φ x ∈ Fmark.layer j)
  (W : LieSubalgebra ℚ D.filtration.AssociatedGraded)

local notation "fast" => W.map (D.filtration.associatedGradedMap Fmark φ hφ)
local notation "gmark" => Fmark.realification.polynomialOrbitCoordinates (fullTaggedVariableWeight J) marked
local notation "Z" => Fmark.realPolynomialSymbolHom bF ν hF (fullTaggedVariableWeight J) gmark

end AllocatedExternalCandidateProblem
end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.CertifiedFullChartForwardEarlyTree
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration.CertifiedFullChartFiniteHistory

open Module VectorPolynomial
open scoped TensorProduct Classical

attribute [local irreducible] FullChartAdmissibleStageCorrection realSymbolGradeEvaluation restrictedMajorCorrection outer fullChartStageCountConstant

variable {m : ℕ} {X : Type} [Fintype X] {ι L η : Type*}
  [LieRing L] [LieAlgebra ℚ L] [Fintype η] {s : ℕ}
  {F : NilpotentLieFiltration L s} {b : Basis ι ℚ L} {ω : ι → ℕ}
  {hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i})}
  {J : Fin m → Type} [∀ j, Fintype (J j)]
  {fast : Submodule ℚ F.AssociatedGraded}
  {basis : Basis η ℝ (ℝ ⊗[ℚ] (F.AssociatedGraded ⧸ fast))}
  {lift : (F.AssociatedGraded ⧸ fast) →ₗ[ℚ] F.AssociatedGraded}
  {Z : F.RealPolynomialSymbolGroup (fullTaggedVariableWeight (X := X) J)}
  {Utag : ∀ j, Submodule ℝ (J j → ℝ)}
  {poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)} {N : X → ℕ} {Bphase : ℝ}

local notation "State" => CertifiedFullChartFiniteHistory F b ω hF J fast basis lift Z
  Set.univ Utag poly N Bphase

theorem exists_finite_children_of_stage_bounds {n : ℕ} (H : State n)
    {cap cumulative : ℕ → ℝ} (hH : StageBounds cap cumulative H)
    (hcap : cap n ≤ Bphase)
    {p : ℝ} (hp : 0 ≤ p) (hpast : cumulative n ≤ p) (hbudget : cap n ≤ p)
    (hX : (Fintype.card X : ℝ) ≤ p) (hm : (m : ℝ) ≤ p)
    (hJ : (Fintype.card (Σ j, J j) : ℝ) ≤ p)
    (hη : (Fintype.card η : ℝ) ≤ p)
    (hblocks : (((n + 1) * (Fintype.card η * m) : ℕ) : ℝ) ≤ p)
    (hpoly : ∀ j ex, ex ≠ 0 → coefficients (poly j) ex ∈ Utag j)
    (hN : ∀ i, 1 ≤ N i) :
    ∃ children : Finset (State (n + 1)),
      (children.card : ℝ) ≤ Real.exp
        ((Fintype.card η : ℝ) * cap n + (p + 8) ^ 8 +
          (p + fullChartStageCountConstant (n + 1) 254) ^
            fullChartStageCountConstant (n + 1) 254) ∧
      (∀ Hnext ∈ children, AdmissibleChildAt F b ω hF J fast basis lift Z
        Utag poly N Bphase (cap n) H Hnext) ∧
      ∀ q K' pair, FullChartAdmissibleStageCorrection F b ω hF J (n + 1)
        fast basis lift Z H.outer.1 H.outer.2 H.K Utag poly N (cap n) q K' pair →
        ∃ Hnext ∈ children, RepresentsCorrection F b ω hF J fast basis lift Z
          Utag poly N Bphase Hnext q K' pair := by
  obtain ⟨count, hcount, candidate, hgood, hcover⟩ :=
    exists_full_chart_finite_stage_branches F b ω hF J (n + 1) fast basis lift
      Z H.outer.1 H.outer.2 H.K Utag poly N (cap n) 254 (by omega)
      hH.certificate hp hpast hbudget hX hm hJ hη
      (by simpa only [Nat.succ_mul] using hblocks)
      (fun point hpoint => H.retained point (Set.mem_univ _) hpoint) hpoly hN
  let next (i : Fin count) : State (n + 1) :=
    H.append_admissible (cap n) hcap (candidate i).1.1 (candidate i).1.2
      (candidate i).2 (hgood i)
  refine ⟨Finset.univ.image next, ?_, ?_, ?_⟩
  · exact (Nat.cast_le.mpr ((Finset.card_image_le).trans_eq
      (Finset.card_fin count))).trans hcount
  · intro Hnext hmem
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hmem
    exact append_admissible_is_child_at H (cap n) hcap _ _ _ (hgood i)
  · intro q K' pair hpair
    obtain ⟨i, hlabel, heval⟩ := hcover q K' pair hpair
    refine ⟨next i, Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩, ?_⟩
    have hentry := append_admissible_entry H (cap n) hcap
      (candidate i).1.1 (candidate i).1.2 (candidate i).2 (hgood i)
    refine ⟨hentry.2.2.trans (congrArg Prod.fst hlabel), ?_, ?_⟩
    · exact (append_admissible_K H (cap n) hcap _ _ _ (hgood i)).trans
        (congrArg Prod.snd hlabel)
    · intro t ht
      change eval₂ t ((next i).slow n) = _ ∧ _
      dsimp only [next]
      rw [hentry.1, hentry.2.1]
      with_reducible exact heval t ht

end Erdos3.NilpotentLieFiltration.CertifiedFullChartFiniteHistory

end

section

namespace Erdos3.NilpotentLieFiltration.CertifiedFullChartFiniteHistory
open Module VectorPolynomial
open scoped TensorProduct Classical BigOperators

attribute [local irreducible] FullChartAdmissibleStageCorrection realSymbolGradeEvaluation restrictedMajorCorrection outer fullChartStageCountConstant

noncomputable def stageBranchLog (dim n : ℕ) (cap p : ℝ) : ℝ :=
  (dim : ℝ) * cap + (p + 8) ^ 8 +
    (p + fullChartStageCountConstant (n + 1) 254) ^
      fullChartStageCountConstant (n + 1) 254

theorem stageBranchLog_mono (dim n : ℕ) (cap : ℝ) {p q : ℝ}
    (hp : 0 ≤ p) (hpq : p ≤ q) : stageBranchLog dim n cap p ≤ stageBranchLog dim n cap q := by
  unfold stageBranchLog
  have hfirst : (p + 8) ^ 8 ≤ (q + 8) ^ 8 := by gcongr
  have hlast : (p + fullChartStageCountConstant (n + 1) 254) ^
      fullChartStageCountConstant (n + 1) 254 ≤
      (q + fullChartStageCountConstant (n + 1) 254) ^
        fullChartStageCountConstant (n + 1) 254 := by gcongr
  exact add_le_add (add_le_add le_rfl hfirst) hlast

variable {m : ℕ} {X : Type} [Fintype X] {ι L η : Type*}
  [LieRing L] [LieAlgebra ℚ L] [Fintype η] {s : ℕ}
  {F : NilpotentLieFiltration L s} {b : Basis ι ℚ L} {ω : ι → ℕ}
  {hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i})}
  {J : Fin m → Type} [∀ j, Fintype (J j)]
  {fast : Submodule ℚ F.AssociatedGraded}
  {basis : Basis η ℝ (ℝ ⊗[ℚ] (F.AssociatedGraded ⧸ fast))}
  {lift : (F.AssociatedGraded ⧸ fast) →ₗ[ℚ] F.AssociatedGraded}
  {Z : F.RealPolynomialSymbolGroup (fullTaggedVariableWeight (X := X) J)}
  {Utag : ∀ j, Submodule ℝ (J j → ℝ)}
  {poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)} {N : X → ℕ} {Bphase : ℝ}

local notation "State" => CertifiedFullChartFiniteHistory F b ω hF J fast basis lift Z
  Set.univ Utag poly N Bphase

theorem exists_prefix_counted_budgeted_branch_tree (depth : ℕ)
    (cap cumulative pCount : ℕ → ℝ) (pTree : ℝ)
    (hpTree : 0 ≤ pTree) (hstorage : Bphase ≤ pTree)
    (hcaps : ∀ n < depth, cap n ≤ Bphase)
    (hmono : ∀ n < depth, cumulative n ≤ cumulative (n + 1))
    (hcap : ∀ n < depth, cap n ≤ cumulative (n + 1))
    (hcount : ∀ n < depth, 0 ≤ pCount n)
    (hpast : ∀ n < depth, cumulative n ≤ pCount n)
    (hbudget : ∀ n < depth, cap n ≤ pCount n)
    (hcountTree : ∀ n < depth, pCount n ≤ pTree)
    (hX : (Fintype.card X : ℝ) ≤ pTree) (hm : (m : ℝ) ≤ pTree)
    (hJ : (Fintype.card (Σ j, J j) : ℝ) ≤ pTree)
    (hη : (Fintype.card η : ℝ) ≤ pTree)
    (hblocks : ((depth * (Fintype.card η * m) : ℕ) : ℝ) ≤ pTree)
    (hXlocal : ∀ n < depth, (Fintype.card X : ℝ) ≤ pCount n)
    (hmlocal : ∀ n < depth, (m : ℝ) ≤ pCount n)
    (hJlocal : ∀ n < depth, (Fintype.card (Σ j, J j) : ℝ) ≤ pCount n)
    (hηlocal : ∀ n < depth, (Fintype.card η : ℝ) ≤ pCount n)
    (hblockslocal : ∀ n < depth, (((n + 1) * (Fintype.card η * m) : ℕ) : ℝ) ≤ pCount n)
    (hpoly : ∀ j ex, ex ≠ 0 → coefficients (poly j) ex ∈ Utag j)
    (hN : ∀ i, 1 ≤ N i) :
    ∃ T : BudgetedBranchTree F b ω hF J fast basis lift Z Utag poly N Bphase cap depth pTree,
      ∀ n, n < depth → ∀ history ∈ T.level n,
        ((T.children n history).card : ℝ) ≤
          Real.exp (stageBranchLog (Fintype.card η) n (cap n) (pCount n)) := by
  have hchildren (n : ℕ) (hn : n < depth) (history : State n) :
      ∃ children : Finset (State (n + 1)),
        (children.card : ℝ) ≤ Real.exp (stageBranchLog (Fintype.card η) n (cap n) pTree) ∧
        (∀ next ∈ children, AdmissibleChildAt F b ω hF J fast basis lift Z
          Utag poly N Bphase (cap n) history next) ∧
        (∀ q K pair, FullChartAdmissibleStageCorrection F b ω hF J (n + 1) fast basis lift
          Z history.outer.1 history.outer.2 history.K Utag poly N (cap n) q K pair →
          ∃ next ∈ children, RepresentsCorrection F b ω hF J fast basis lift Z
            Utag poly N Bphase next q K pair) ∧
        (StageBounds cap cumulative history → (children.card : ℝ) ≤
          Real.exp (stageBranchLog (Fintype.card η) n (cap n) (pCount n))) := by
    by_cases hvalid : StageBounds cap cumulative history
    · obtain ⟨children, hcard, hadmissible, hcomplete⟩ :=
        exists_finite_children_of_stage_bounds history hvalid (hcaps n hn)
          (hcount n hn) (hpast n hn) (hbudget n hn) (hXlocal n hn) (hmlocal n hn)
          (hJlocal n hn) (hηlocal n hn) (hblockslocal n hn) hpoly hN
      refine ⟨children, ?_, hadmissible, hcomplete, fun _ => hcard⟩
      exact hcard.trans (Real.exp_le_exp.mpr
        (stageBranchLog_mono _ _ _ (hcount n hn) (hcountTree n hn)))
    · obtain ⟨children, hcard, hadmissible, hcomplete⟩ :=
        exists_finite_children_at_budget history (cap n) (hcaps n hn) hpTree hstorage
          ((hcaps n hn).trans hstorage) hX hm hJ hη
          ((Nat.cast_le.mpr (Nat.mul_le_mul_right (Fintype.card η * m)
            (Nat.succ_le_of_lt hn))).trans hblocks) hpoly hN
      exact ⟨children, hcard, hadmissible, hcomplete, fun h => (hvalid h).elim⟩
  let children : ∀ n, State n → Finset (State (n + 1)) := fun n history =>
    if hn : n < depth then Classical.choose (hchildren n hn history) else ∅
  let T : BudgetedBranchTree F b ω hF J fast basis lift Z Utag poly N Bphase cap depth pTree := {
    children := children
    card := by
      intro n hn history
      dsimp only [children]
      rw [dif_pos hn]
      exact_mod_cast (Classical.choose_spec (hchildren n hn history)).1.trans (Nat.le_ceil _)
    admissible := by
      intro n hn history next hmem
      have hm' : next ∈ Classical.choose (hchildren n hn history) := by
        simpa only [children, dif_pos hn] using hmem
      exact (Classical.choose_spec (hchildren n hn history)).2.1 next hm'
    complete := by
      intro n hn history q K pair hpair
      obtain ⟨next, hmem, hrep⟩ :=
        (Classical.choose_spec (hchildren n hn history)).2.2.1 q K pair hpair
      exact ⟨next, by simpa only [children, dif_pos hn] using hmem, hrep⟩ }
  refine ⟨T, ?_⟩
  intro n hn history hmem
  have hvalid := T.stage_bounds hmono hcap n (Nat.le_of_lt hn) history hmem
  have hsharp := (Classical.choose_spec (hchildren n hn history)).2.2.2 hvalid
  simpa only [T, children, dif_pos hn] using hsharp

omit [Fintype X] in

theorem BudgetedBranchTree.card_level_le_prefix_exp
    {cap : ℕ → ℝ} {depth : ℕ} {pTree : ℝ}
    (T : BudgetedBranchTree F b ω hF J fast basis lift Z Utag poly N Bphase cap depth pTree)
    (pCount : ℕ → ℝ)
    (hsharp : ∀ n, n < depth → ∀ history ∈ T.level n,
      ((T.children n history).card : ℝ) ≤
        Real.exp (stageBranchLog (Fintype.card η) n (cap n) (pCount n)))
    (n : ℕ) (hn : n ≤ depth) :
    ((T.level n).card : ℝ) ≤ Real.exp
      (∑ j ∈ Finset.range n, stageBranchLog (Fintype.card η) j (cap j) (pCount j)) :=
  finiteGradedBranchLevel_card_le_exp_sum _ T.children depth
    (fun j => stageBranchLog (Fintype.card η) j (cap j) (pCount j)) hsharp n hn

end Erdos3.NilpotentLieFiltration.CertifiedFullChartFiniteHistory

end

section

namespace Erdos3.NilpotentLieFiltration.CertifiedFullChartFiniteHistory
open Module VectorPolynomial
open scoped TensorProduct Classical BigOperators

attribute [local irreducible] FullChartAdmissibleStageCorrection realSymbolGradeEvaluation restrictedMajorCorrection outer fullChartStageCountConstant

variable {m : ℕ} {X : Type} {ι L η : Type*}
  [LieRing L] [LieAlgebra ℚ L] [Fintype η] {s : ℕ}
  {F : NilpotentLieFiltration L s} {b : Basis ι ℚ L} {ω : ι → ℕ}
  {hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i})}
  {J : Fin m → Type} [∀ j, Fintype (J j)]
  {fast : Submodule ℚ F.AssociatedGraded}
  {basis : Basis η ℝ (ℝ ⊗[ℚ] (F.AssociatedGraded ⧸ fast))}
  {lift : (F.AssociatedGraded ⧸ fast) →ₗ[ℚ] F.AssociatedGraded}
  {Z : F.RealPolynomialSymbolGroup (fullTaggedVariableWeight (X := X) J)}
  {Utag : ∀ j, Submodule ℝ (J j → ℝ)}
  {poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)} {N : X → ℕ} {Bphase : ℝ}
  {depth : ℕ} {pTree : ℝ}

local notation "Cstage" => fun n => fullChartStageCountConstant (n + 1) 254

theorem BudgetedBranchTree.card_level_le_forward_prefix
    (A : ℕ) {x : ℝ} (hx : 0 ≤ x) (hd : (Fintype.card η : ℝ) ≤ x)
    (T : BudgetedBranchTree F b ω hF J fast basis lift Z Utag poly N Bphase
      (fun n => preparedFiniteForwardCap A Cstage n x) depth pTree)
    (hsharp : ∀ n, n < depth → ∀ history ∈ T.level n,
      ((T.children n history).card : ℝ) ≤ Real.exp
        (stageBranchLog (Fintype.card η) n (preparedFiniteForwardCap A Cstage n x)
          (preparedFiniteForwardCount A Cstage n x)))
    (n : ℕ) (hn : n ≤ depth) :
    ((T.level n).card : ℝ) ≤ Real.exp (preparedFiniteForwardPrefixLog A Cstage n x) := by
  apply (T.card_level_le_prefix_exp
    (fun j => preparedFiniteForwardCount A Cstage j x) hsharp n hn).trans
  apply Real.exp_le_exp.mpr
  exact Finset.sum_le_sum (fun j _ =>
    preparedFiniteForward_branch_count_log A Cstage j hx hd)

end Erdos3.NilpotentLieFiltration.CertifiedFullChartFiniteHistory

end

section

namespace Erdos3.NilpotentLieFiltration.CertifiedFullChartFiniteHistory
open Module VectorPolynomial
open scoped TensorProduct Classical BigOperators

attribute [local irreducible] FullChartAdmissibleStageCorrection realSymbolGradeEvaluation restrictedMajorCorrection outer fullChartStageCountConstant

variable {m : ℕ} {X : Type} [Fintype X] {ι L η : Type*}
  [LieRing L] [LieAlgebra ℚ L] [Fintype η] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
  (J : Fin m → Type) [∀ j, Fintype (J j)]
  (fast : Submodule ℚ F.AssociatedGraded)
  (basis : Basis η ℝ (ℝ ⊗[ℚ] (F.AssociatedGraded ⧸ fast)))
  (lift : (F.AssociatedGraded ⧸ fast) →ₗ[ℚ] F.AssociatedGraded)
  (Z : F.RealPolynomialSymbolGroup (fullTaggedVariableWeight (X := X) J))
  (Utag : ∀ j, Submodule ℝ (J j → ℝ))
  (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)) (N : X → ℕ)

local notation "countConstants" => (fun n => fullChartStageCountConstant (n + 1) 254)

variable (depth scheduleExponent : ℕ) (x : ℝ)
    (hx : 0 ≤ x)
    (hX : (Fintype.card X : ℝ) ≤ x) (hm : (m : ℝ) ≤ x)
    (hJ : (Fintype.card (Σ j, J j) : ℝ) ≤ x)
    (hη : (Fintype.card η : ℝ) ≤ x)
    (hblocks : ((depth * (Fintype.card η * m) : ℕ) : ℝ) ≤ x)
    (hpoly : ∀ j ex, ex ≠ 0 → coefficients (poly j) ex ∈ Utag j)
    (hN : ∀ i, 1 ≤ N i)

local notation "cap" => fun n => preparedFiniteForwardCap scheduleExponent countConstants n x
local notation "cumulative" => fun n => preparedFiniteForwardCumulative scheduleExponent countConstants n x
local notation "count" => fun n => preparedFiniteForwardCount scheduleExponent countConstants n x
local notation "storage" => preparedFiniteForwardParameter scheduleExponent countConstants depth x
local notation "Tree" => BudgetedBranchTree F b ω hF J fast basis lift Z Utag poly N
  (cumulative depth) cap depth storage

include hx hX hm hJ hη hblocks hpoly hN

theorem exists_early_forward_branch_tree :
    ∃ T : Tree,
      (∀ n, n < depth → ∀ history ∈ T.level n,
        ((T.children n history).card : ℝ) ≤
          Real.exp (stageBranchLog (Fintype.card η) n (cap n) (count n))) ∧
      (∀ n, n ≤ depth → ((T.level n).card : ℝ) ≤
        Real.exp (preparedFiniteForwardPrefixLog scheduleExponent countConstants n x)) := by
  have hstorage0 := preparedFiniteForwardParameter_nonneg scheduleExponent countConstants depth hx
  have hstorage := (preparedFiniteForward_prefix_bounds scheduleExponent countConstants depth hx).1.2
  have hxtoStorage := le_preparedFiniteForwardParameter scheduleExponent countConstants depth hx
  have hxtoCount (n : ℕ) : x ≤ count n :=
    le_preparedFiniteForwardCount scheduleExponent countConstants n hx
  have hcountTree (n : ℕ) (hn : n < depth) : count n ≤ storage :=
    preparedFiniteForwardCount_le_parameter scheduleExponent countConstants hx hn
  obtain ⟨T, hsharp⟩ := exists_prefix_counted_budgeted_branch_tree
    (F := F) (b := b) (ω := ω) (hF := hF) (J := J)
    (fast := fast) (basis := basis) (lift := lift) (Z := Z)
    depth cap cumulative count storage hstorage0 hstorage
    (fun _ hn => preparedFiniteForwardCap_le_cumulative scheduleExponent countConstants hx hn)
    (fun n _ => preparedFiniteForwardCumulative_le_succ scheduleExponent countConstants n hx)
    (fun n _ => preparedFiniteForwardCap_le_cumulative_succ scheduleExponent countConstants n hx)
    (fun n _ => preparedFiniteForwardCount_nonneg scheduleExponent countConstants n hx)
    (fun n _ => ((preparedFiniteForward_prefix_bounds scheduleExponent countConstants n hx).1.2).trans
      (preparedFiniteForwardParameter_le_count scheduleExponent countConstants n hx))
    (fun n _ => preparedFiniteForwardCap_le_count scheduleExponent countConstants n hx)
    hcountTree (hX.trans hxtoStorage) (hm.trans hxtoStorage) (hJ.trans hxtoStorage)
    (hη.trans hxtoStorage) (hblocks.trans hxtoStorage)
    (fun n _ => hX.trans (hxtoCount n)) (fun n _ => hm.trans (hxtoCount n))
    (fun n _ => hJ.trans (hxtoCount n)) (fun n _ => hη.trans (hxtoCount n))
    (fun n hn => (Nat.cast_le.mpr (Nat.mul_le_mul_right (Fintype.card η * m)
      (Nat.succ_le_of_lt hn))).trans (hblocks.trans (hxtoCount n))) hpoly hN
  exact ⟨T, hsharp, fun n hn =>
    T.card_level_le_forward_prefix scheduleExponent hx hη hsharp n hn⟩

noncomputable def earlyForwardBranchTree : Tree :=
  Classical.choose (exists_early_forward_branch_tree F b ω hF J fast basis lift Z Utag poly N
    depth scheduleExponent x hx hX hm hJ hη hblocks hpoly hN)


end Erdos3.NilpotentLieFiltration.CertifiedFullChartFiniteHistory

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.NativePairChartSymbol
namespace OAI

universe universeLevel

section

namespace Erdos3.RationalFilteredNilmanifold

open Module VectorPolynomial NilpotentLieFiltration
open scoped TensorProduct BigOperators

attribute [local instance_reducible] BoolLieFamily

variable {L M : Type universeLevel} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
    {s d e : ℕ} (D : RationalFilteredNilmanifold L s d)
    (E : RationalFilteredNilmanifold M s e)
    {σ τ ι : Type*} {w : σ → ℕ} {v : τ → ℕ}

attribute [local irreducible] realChartSubstitute polynomialOrbitRealChart weightedAdaptedRealChartHom realPolynomialSymbolHom realSymbolHomogeneousPullbackHom

theorem pairOrbit_polynomialOrbitRealChart_log
    (p : D.filtration.realification.PolynomialOrbit w)
    (q : E.filtration.realification.PolynomialOrbit w)
    (β : σ → MvPolynomial τ ℝ)
    (hβ : ∀ i, β i ∈ weightedSupportLE v (w i)) :
    (pairOrbit D E (D.filtration.polynomialOrbitRealChart w v β hβ p)
      (E.filtration.polynomialOrbitRealChart w v β hβ q)).log =
        realChartSubstitute β (pairOrbit D E p q).log := by
  simp only [pairOrbit, piRealOrbit, PolynomialOrbit.log, polynomialOrbitOfLog, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  cases i
  · change VectorPolynomial.map
      ((realProductSingle (L := BoolLieFamily L M) false).restrictScalars ℚ)
      (E.filtration.polynomialOrbitRealChart w v β hβ q).log =
      realChartSubstitute β (VectorPolynomial.map
        ((realProductSingle (L := BoolLieFamily L M) false).restrictScalars ℚ) q.log)
    rw [polynomialOrbitRealChart_log]
    exact (realChartSubstitute_map β
      (realProductSingle (L := BoolLieFamily L M) false) q.log).symm
  · change VectorPolynomial.map
      ((realProductSingle (L := BoolLieFamily L M) true).restrictScalars ℚ)
      (D.filtration.polynomialOrbitRealChart w v β hβ p).log =
      realChartSubstitute β (VectorPolynomial.map
        ((realProductSingle (L := BoolLieFamily L M) true).restrictScalars ℚ) p.log)
    rw [polynomialOrbitRealChart_log]
    exact (realChartSubstitute_map β
      (realProductSingle (L := BoolLieFamily L M) true) p.log).symm

attribute [local irreducible] pairOrbit

theorem pairOrbitSymbol_polynomialOrbitRealChart
    (p : D.filtration.realification.PolynomialOrbit w)
    (q : E.filtration.realification.PolynomialOrbit w)
    (b : Basis ι ℚ (PairAlgebra L M)) (ω : ι → ℕ)
    (hF : ∀ k, (pi (pairModels D E)).filtration.layer k =
      Submodule.span ℚ (b '' {i | k ≤ ω i}))
    (β : σ → MvPolynomial τ ℝ)
    (hβ : ∀ i, β i ∈ weightedSupportLE v (w i)) :
    pairOrbitSymbol D E (D.filtration.polynomialOrbitRealChart w v β hβ p)
      (E.filtration.polynomialOrbitRealChart w v β hβ q) b ω hF =
        (pi (pairModels D E)).filtration.realPolynomialSymbolHom b ω hF v
          ((pi (pairModels D E)).filtration.weightedAdaptedRealChartHom w v β hβ
            ⟨⟨(pairOrbit D E p q).log, (pairOrbit D E p q).property⟩⟩) := by
  unfold pairOrbitSymbol
  apply congrArg ((pi (pairModels D E)).filtration.realPolynomialSymbolHom b ω hF v)
  apply NilpotentLieBCHGroup.ext
  apply Subtype.ext
  exact (pairOrbit_polynomialOrbitRealChart_log D E p q β hβ).trans
    ((pi (pairModels D E)).filtration.weightedAdaptedRealChartHom_coord
      w v β hβ ⟨⟨(pairOrbit D E p q).log, (pairOrbit D E p q).property⟩⟩).symm

theorem pairOrbitSymbol_chart_eq_of_homogeneous_eq
    (p : D.filtration.realification.PolynomialOrbit w)
    (q : E.filtration.realification.PolynomialOrbit w)
    (b : Basis ι ℚ (PairAlgebra L M)) (ω : ι → ℕ)
    (hF : ∀ k, (pi (pairModels D E)).filtration.layer k =
      Submodule.span ℚ (b '' {i | k ≤ ω i}))
    (β : σ → MvPolynomial τ ℝ)
    (hβ : ∀ i, β i ∈ weightedSupportLE v (w i))
    (β' : σ → MvPolynomial τ ℝ)
    (hβ' : ∀ i, β' i ∈ weightedSupportLE v (w i))
    (htop : (fun i => MvPolynomial.weightedHomogeneousComponent v (w i) (β i)) =
      (fun i => MvPolynomial.weightedHomogeneousComponent v (w i) (β' i))) :
    pairOrbitSymbol D E (D.filtration.polynomialOrbitRealChart w v β hβ p)
      (E.filtration.polynomialOrbitRealChart w v β hβ q) b ω hF =
    pairOrbitSymbol D E (D.filtration.polynomialOrbitRealChart w v β' hβ' p)
      (E.filtration.polynomialOrbitRealChart w v β' hβ' q) b ω hF := by
  rw [pairOrbitSymbol_polynomialOrbitRealChart, pairOrbitSymbol_polynomialOrbitRealChart,
    realPolynomialSymbolHom_weightedAdaptedRealChart,
    realPolynomialSymbolHom_weightedAdaptedRealChart]
  congr 1
  congr 1

end Erdos3.RationalFilteredNilmanifold

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.ScalarReferenceNativeDetectionCoordinateEquiv
namespace OAI

section

namespace Erdos3
open scoped BigOperators Classical

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {K K' X : Type*}

def scalarNoiseIndexEquiv (e : K ≃ K') : Option K × X ≃ Option K' × X :=
  (Equiv.optionCongr e).prodCongr (Equiv.refl X)

@[simp] theorem scalarNoiseIndexEquiv_none (e : K ≃ K') (x : X) :
    scalarNoiseIndexEquiv e (none, x) = (none, x) := rfl

@[simp] theorem scalarNoiseIndexEquiv_some (e : K ≃ K') (k : K) (x : X) :
    scalarNoiseIndexEquiv e (some k, x) = (some (e k), x) := rfl

@[simp] theorem scalarNoiseIndexEquiv_symm (e : K ≃ K') :
    (scalarNoiseIndexEquiv (X := X) e).symm = scalarNoiseIndexEquiv e.symm := rfl

@[simp] theorem trimmedSpatialWidths_scalarNoiseIndexEquiv
    (e : K ≃ K') (B τ : ℝ) (N : X → ℕ) (i : Option K × X) :
    trimmedSpatialWidths B τ N (scalarNoiseIndexEquiv e i) =
      trimmedSpatialWidths B τ N i := by
  rcases i with ⟨k, x⟩
  cases k <;> rfl

variable [Fintype K] [Fintype K'] [Fintype X]

noncomputable def scalarNoiseSupportEquiv (e : K ≃ K') (B τ : ℝ) (N : X → ℕ) :
    rectangularWeightIndices 0 (trimmedSpatialWidths (K := K) B τ N) 1 ≃
      rectangularWeightIndices 0 (trimmedSpatialWidths (K := K') B τ N) 1 where
  toFun z := ⟨fun j => z.val ((scalarNoiseIndexEquiv e).symm j), by
    apply (mem_rectangularWeightIndices_zero_iff _ _).mpr
    intro j
    simpa only [scalarNoiseIndexEquiv_symm,
      trimmedSpatialWidths_scalarNoiseIndexEquiv] using
      (mem_rectangularWeightIndices_zero_iff _ _).mp z.property
        ((scalarNoiseIndexEquiv e).symm j)⟩
  invFun z := ⟨fun i => z.val (scalarNoiseIndexEquiv e i), by
    apply (mem_rectangularWeightIndices_zero_iff _ _).mpr
    intro i
    simpa only [trimmedSpatialWidths_scalarNoiseIndexEquiv] using
      (mem_rectangularWeightIndices_zero_iff _ _).mp z.property
        (scalarNoiseIndexEquiv e i)⟩
  left_inv z := by
    apply Subtype.ext
    funext i
    exact congrArg z.val ((scalarNoiseIndexEquiv e).symm_apply_apply i)
  right_inv z := by
    apply Subtype.ext
    funext j
    exact congrArg z.val ((scalarNoiseIndexEquiv e).apply_symm_apply j)

@[simp] theorem scalarNoiseSupportEquiv_val (e : K ≃ K') (B τ : ℝ)
    (N : X → ℕ)
    (z : rectangularWeightIndices 0 (trimmedSpatialWidths (K := K) B τ N) 1) :
    (scalarNoiseSupportEquiv e B τ N z).val =
      fun j => z.val ((scalarNoiseIndexEquiv e).symm j) := rfl

@[simp] theorem scalarNoiseSupportEquiv_symm_val (e : K ≃ K') (B τ : ℝ)
    (N : X → ℕ)
    (z : rectangularWeightIndices 0 (trimmedSpatialWidths (K := K') B τ N) 1) :
    ((scalarNoiseSupportEquiv e B τ N).symm z).val =
      fun i => z.val (scalarNoiseIndexEquiv e i) := rfl

noncomputable def scalarJointPathEquiv (e : K ≃ K') (B τ : ℝ) (N : X → ℕ)
    (A : Type*) :
    A × rectangularWeightIndices 0 (trimmedSpatialWidths (K := K) B τ N) 1 ≃
      A × rectangularWeightIndices 0 (trimmedSpatialWidths (K := K') B τ N) 1 :=
  (Equiv.refl A).prodCongr (scalarNoiseSupportEquiv e B τ N)

@[simp] theorem scalarJointPathEquiv_fst (e : K ≃ K') (B τ : ℝ) (N : X → ℕ)
    (A : Type*)
    (z : A × rectangularWeightIndices 0 (trimmedSpatialWidths (K := K) B τ N) 1) :
    (scalarJointPathEquiv e B τ N A z).1 = z.1 := rfl

@[simp] theorem scalarJointPathEquiv_snd_val (e : K ≃ K') (B τ : ℝ) (N : X → ℕ)
    (A : Type*)
    (z : A × rectangularWeightIndices 0 (trimmedSpatialWidths (K := K) B τ N) 1) :
    (scalarJointPathEquiv e B τ N A z).2.val =
      fun j => z.2.val ((scalarNoiseIndexEquiv e).symm j) := rfl

namespace BooleanCubeKernel

end BooleanCubeKernel
end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

variable {K K' X : Type*} [Fintype K] [Fintype K'] [Fintype X]
    (e : K ≃ K') (B τ : ℝ) (N : X → ℕ)

local notation "W" => trimmedSpatialWidths (K := K) B τ N

variable (hW : ∀ i : Option K × X, 0 < trimmedSpatialWidths B τ N i)
    (hW' : ∀ i : Option K' × X, 0 < trimmedSpatialWidths B τ N i)
    (hZ : 0 < ∑' z, selectedResidueSmoothWeight (fun _ : X => 1) {0}
      (trimmedSpatialWidths (K := K) B τ N) z)
    (hZ' : 0 < ∑' z, selectedResidueSmoothWeight (fun _ : X => 1) {0}
      (trimmedSpatialWidths (K := K') B τ N) z)

include hW hW' hZ hZ'

variable {Y : Type*} (A : Finset Y) (hA : A.Nonempty)

end Erdos3

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule BooleanCubeKernel
open scoped Classical BigOperators NNReal TensorProduct

def OrdinarySliceNativeDetection
    {m degree : ℕ} {X K Ω : Type} [Fintype X] [DecidableEq X] [Fintype K] [DecidableEq K] [Fintype Ω]
    (J : Fin m → Type) [∀ j, Fintype (J j)]
    (N : X → ℕ) (hbox : (integerBox N).Nonempty)
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (sides : K → ℕ) (law : FiniteProbabilityWeights Ω)
    (physical : Ω → integerBox sides → X → ℤ) (pSlice pTest pNative α : ℝ) : Prop :=
  ∀ {Tests : Ω → Type} [∀ z, Nonempty (Tests z)]
    {Ldetect : ∀ z, Tests z → Type} [∀ z j, LieRing (Ldetect z j)]
    [∀ z j, LieAlgebra ℚ (Ldetect z j)] {dims : ∀ z, Tests z → ℕ}
    [∀ z j, TopologicalSpace (ℝ ⊗[ℚ] Ldetect z j)]
    [∀ z j, IsTopologicalAddGroup (ℝ ⊗[ℚ] Ldetect z j)]
    [∀ z j, ContinuousSMul ℝ (ℝ ⊗[ℚ] Ldetect z j)] [∀ z j, T2Space (ℝ ⊗[ℚ] Ldetect z j)]
    (Ddetect : ∀ z j, RationalFilteredNilmanifold (Ldetect z j) degree (dims z j))
    (Vdetect : ∀ z j, (Ddetect z j).Niltest (fun _ : K => 1))
    (slices : ∀ z, Tests z → Finset (integerBox sides))
    (origin : ∀ z, Tests z → K → ℤ) (step : ∀ z, Tests z → ℕ)
    (length : ∀ z, Tests z → K → ℕ),
    (∀ z j, 0 < step z j) →
    (∀ z j, (slices z j).image Subtype.val = commonStrideBox (origin z j) (step z j) (length z j)) →
    (∀ z j, IsDenseCommonStrideBox sides pSlice ((slices z j).image Subtype.val)) →
    (∀ z j, (Vdetect z j).ComplexityLE pTest) →
    (∀ z j, ((Vdetect z j).normBound : ℝ) ≤ 1) →
    SampledSliceNativeDetection J N hbox poly law physical slices
      (fun z j t => star ((Vdetect z j).eval (commonStrideIndex (origin z j) (step z j) t.val)))
      degree pNative α

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule BooleanCubeKernel
open scoped Classical BigOperators NNReal TensorProduct

def ScalarReferenceNativeDetection
    {m degree : ℕ} {X K : Type} [Fintype X] [DecidableEq X]
    [Fintype K] [DecidableEq K]
    (J : Fin m → Type) [∀ j, Fintype (J j)]
    (N : X → ℕ) (hbox : (integerBox N).Nonempty)
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (S : ℕ) (W τ : ℝ)
    (hbase : (trimmedIntegerBox N (spatialTrimMargin τ N)).Nonempty)
    (hW : ∀ z : Option K × X, 0 < trimmedSpatialWidths W τ N z)
    (hZ : 0 < ∑' z, selectedResidueSmoothWeight (fun _ : X => 1) {0}
      (trimmedSpatialWidths (K := K) W τ N) z)
    (pSlice pTest pNative α : ℝ) : Prop :=
  OrdinarySliceNativeDetection (degree := degree) J N hbox poly (fun _ : K => S)
    (selectedJointReference _ hbase (fun _ : X => 1) {0}
      (trimmedSpatialWidths W τ N) hW hZ)
    (fun z t => jointIntegerPhysicalSite t.val (z.1.val, z.2.val))
    pSlice pTest pNative α

end Erdos3.VectorPolynomial

end

end OAI

end


