-- Prove2me | Definitions.Def_StabPauli1264_Grouped_Measurements
-- name    : StabPauli1264_Grouped_Measurements
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T16:24:28.835456+00:00
-- url     : https://prove2.me/theorems/c07020a4-c0eb-4b88-8bed-e3230ef45d7a
-- title:
--   Joint Born measurements and unrestricted learner procedures
-- statement:
--   A joint sharp measurement of a commuting context $C$ on a fresh copy of $\rho$ has the full-vector Born probabilities
--
--   $$\Pr_\rho[s]=\operatorname{Re}\operatorname{tr}\!\left(\rho\prod_{i\in C}\frac{I+s_iP_i}{2}\right),\qquad s\in\{\pm1\}^{C}.$$
--
--   Dependencies between commuting Paulis may correlate the coordinates and give zero probability to some vectors. The product uses increasing window order. A grouped procedure chooses a context by an arbitrary real probability law conditional on the entire previous history, measures a fresh copy, and eventually returns a randomized tableau. A permitted procedure uses commuting contexts and valid output tableaux. Its transcript law multiplies the conditional choice probabilities and the actual joint Born probabilities. Its success probability sums this law over outputs with excess risk at most $\varepsilon$.
--
--   A proper collective procedure is an arbitrary finite POVM on $\rho^{\otimes N}$ indexed by all tableaux, with positive effects summing to the identity and zero effect for invalid tableaux. All classical randomization and postprocessing are included in these effects. A second, unrestricted-output interface is a countably additive positive operator-valued Borel measure on $[-1,1]^m$. Its success probability is the Born probability of the Borel set of successful bounded predictions.
--
--   These interfaces impose no circuit, coefficient, purity or computability restriction. They supply actual physical procedures for both the upper and lower bounds.
--
--   **Formalization Note** A joint outcome is stored as a full window Boolean vector, canonically false outside $C$; false means $+1$. General grouped randomness has the equivalent behavioral-kernel representation on finite histories. The tensor product is indexed by $N$ tuples of computational basis vectors; at $N=0$ its empty product is the scalar identity. Borel POVM outcomes directly absorb arbitrary measurable postprocessing.
--
--   The general finite and measurable POVM interfaces are imported from the published library; only the proper-tableau restriction is paper specific.
-- source:
--   Yingjian Liu, Xiaoyi Yang, Zhaohui Yang, STOC 2027 submission #1264 (October 2026), Definition 5.3(c,d), p. 13; §1.1 pp. 3–4; collective testing setup, pp. 16–17; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1264.pdf

import Definitions.Def_StabPauli1264_Grouped_Domain
import Definitions.Def_QAlgorithms_Defs_GeneralPOVMs
import Definitions.Def_EntAssistOneWay_Separation_POVM
set_option autoImplicit false

namespace StabPauli1264.Grouped

open QAlgorithms.Stabilizer
open scoped BigOperators Classical ComplexOrder

abbrev Outcome (m : ℕ) := Fin m → Bool
abbrev Record (m : ℕ) := Finset (Fin m) × Outcome m

def sign (b : Bool) : ℝ := if b then -1 else 1

/-- Joint spectral projector. Outside C the full-window outcome is canonically false.
No independence of coordinates in C is asserted, even when labels are dependent. -/
noncomputable def jointEffect {n m : ℕ} (M : Window n m)
    (C : Finset (Fin m)) (s : Outcome m) : Mat n :=
  if ∀ i, i ∉ C → s i = false then
    (List.ofFn fun i : Fin m => if i ∈ C then
      (2⁻¹ : ℂ) • (1 + (sign (s i) : ℂ) • operator M i) else 1).prod
  else 0

noncomputable def jointWeight {n m : ℕ} (M : Window n m) (ρ : Mat n)
    (C : Finset (Fin m)) (s : Outcome m) : ℝ :=
  (Matrix.trace (ρ * jointEffect M C s)).re

/-- An arbitrary randomized adaptive decision rule, with exactly N available fresh copies.
The history includes contexts and entire joint outcomes. -/
structure GroupedProcedure (n m N : ℕ) where
  choose : List (Record m) → OAI.ThorpCompatibility.Law (Finset (Fin m))
  output : List (Record m) → OAI.ThorpCompatibility.Law (Tableau n)

def GroupedPermitted {n m N : ℕ} (M : Window n m) (A : GroupedProcedure n m N) : Prop :=
  (∀ h C, (A.choose h).mass C ≠ 0 → IsContext M C) ∧
  (∀ h T, (A.output h).mass T ≠ 0 → IsValidTableau T)

/-- Sequential Born law: every factor uses the same original rho, on a fresh copy.
The conditional choice may depend on the history; fresh does not forbid adaptive contexts. -/
noncomputable def transcriptWeight {n m N : ℕ} (M : Window n m)
    (A : GroupedProcedure n m N) (ρ : Mat n) (h : Fin N → Record m) : ℝ :=
  ∏ t : Fin N,
    (A.choose (List.ofFn fun j : Fin t.val => h ⟨j.val, lt_trans j.isLt t.isLt⟩)).mass (h t).1 *
      jointWeight M ρ (h t).1 (h t).2

noncomputable def groupedSuccess {n m N : ℕ} (M : Window n m)
    (p : EvalLaw m) (A : GroupedProcedure n m N) (ρ : Mat n) (ε : ℝ) : ℝ :=
  ∑ h : Fin N → Record m, transcriptWeight M A ρ h *
    ∑ T : Tableau n, (A.output (List.ofFn h)).mass T *
      if IsValidTableau T ∧ excess M p ρ (response M T) ≤ ε then 1 else 0

abbrev CopyMat (n N : ℕ) := Matrix (Fin N → Bits n) (Fin N → Bits n) ℂ

noncomputable def tensorCopies {n : ℕ} (ρ : Mat n) (N : ℕ) : CopyMat n N :=
  fun x y => ∏ t, ρ (x t) (y t)

/-- A proper collective procedure is precisely a finite POVM with tableau outcomes.
Arbitrary classical randomness and postprocessing are absorbed into its effects. -/
structure CollectiveProcedure (n N : ℕ) where
  measurement : EntAssistOneWay.Separation.POVM (Fin N → Bits n) (Tableau n)
  proper : ∀ T, ¬ IsValidTableau T → measurement.op T = 0

noncomputable def CollectiveProcedure.effect {n N : ℕ} (A : CollectiveProcedure n N) :=
  A.measurement.op

noncomputable def collectiveSuccess {n m N : ℕ} (M : Window n m)
    (p : EvalLaw m) (A : CollectiveProcedure n N) (ρ : Mat n) (ε : ℝ) : ℝ :=
  ∑ T, if IsValidTableau T ∧ excess M p ρ (response M T) ≤ ε then
    (Matrix.trace (tensorCopies ρ N * A.effect T)).re else 0

/-- Borel space of every bounded real prediction vector, including nonproper predictions. -/
abbrev Predictor (m : ℕ) := Fin m → Set.Icc (-1 : ℝ) 1

/-- General operator-valued Borel probability measure on bounded prediction vectors.
This directly incorporates any measurable randomized postprocessing of any POVM.
Countable additivity is in the finite-dimensional matrix topology. -/
abbrev BoundedCollective (n m N : ℕ) :=
  QAlgorithms.Measurements.OperatorPOVM (Fin N → Bits n) (Predictor m)

noncomputable def boundedSuccess {n m N : ℕ} (M : Window n m)
    (p : EvalLaw m) (A : BoundedCollective n m N) (ρ : Mat n) (ε : ℝ) : ℝ :=
  (Matrix.trace (tensorCopies ρ N *
    A.operator {h | excess M p ρ (fun i => (h i).val) ≤ ε})).re

end StabPauli1264.Grouped


