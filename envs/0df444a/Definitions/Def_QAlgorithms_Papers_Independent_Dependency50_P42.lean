-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P42
-- name    : QAlgorithms_Papers_Independent_Dependency50_P42
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-19T16:53:07.056595+00:00
-- url     : https://prove2.me/theorems/45bdce9a-e8d8-4d0e-aac4-e74e41bb4c55
-- title:
--   Definitions for The asymptotic entanglement cost of preparing a quantum state
-- statement:
--   The objects the formalized statements of *The asymptotic entanglement cost of preparing a quantum state* (arXiv:quant-ph/0008134) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `copyIndex`: PDF pp.1--3: a fixed local basis identification of n copies with dimension a^n. The same identification is used for all states and both matrix indices.
--   - `dimensionedPower`: PDF pp.1--3: dimension adapter for the imported grouped tensor power. This wrapper only relabels each local basis to Fin(a^n) or Fin(b^n), as required by the accepted FiniteLOCC endpoints; it does not redefine the tensor product.
--   - `singletVector`: PDF p.1: the singlet (|01> - |10>)/sqrt(2); sqrt(2)/2 is the same coefficient.
--   - `singletState`: PDF pp.1--2: the normalized two-qubit singlet density.
--   - `singlets`: PDF p.2, Eq.(6): a deterministic natural number m of shared singlets. At m=0 this is the scalar trace-one state, with no shared entanglement.
--   - `StateDistance`: PDF pp.2,5: state distances for every finite bipartite dimension. Physical arguments are normalized density matrices in positive local dimensions.
--   - `paperBures`: PDF p.2: D=2 sqrt(1-F), with the accepted root fidelity F. This differs in scale from the accepted Bures--Wasserstein convention.
--   - `halfTraceDistance`: PDF p.5, Eq.(24): precisely half the trace norm.
--   - `FiniteBlockFormationRate`: PDF p.2, Eq.(6): paper-specific finite-block formation feasibility. The accepted AchievableRate predicates concern channel codes and cannot replace this state-formation definition. The protocol class is the accepted finite adaptive LOCC tree, with complete local rectangular Kraus instruments and outcome-dependent continuations. Its output is the sum over all branches, hence normalized on normalized inputs. Local ancillas, disposal, and unrestricted two-way classical messages are allowed; there is no postselection. Both m and the positive block length n are selected after both tolerances.
--   - `entanglementCost`: PDF p.2, Eq.(6): infimum of the actual operational feasible rates. For density inputs in positive finite dimensions and the state metrics used below, the set is nonempty (finite exact preparation by teleportation) and bounded below by zero. Values on nonphysical matrices are not used.
--   - `EventuallyAchievableRate`: PDF p.5, Eq.(21): eventual feasibility. For every pair of tolerances there is a threshold, then for every n>N a possibly different m and LOCC protocol. The strict threshold automatically excludes n=0.
--   - `alternativeCost`: PDF p.5, Eq.(21): infimum of eventually achievable rates, separately from Eq.(6). For the physical inputs and distances in the theorems, exact preparation gives a nonempty rate set and every feasible rate is nonnegative.
--   - `formationSequence`: PDF pp.1,3, Eqs.(1),(8): the positive-copy formation quotients. Index n denotes n+1 copies, so the denominator is never zero. Entropy is in bits.
--   - `regularizedFormation`: PDF pp.1,3: a total representative of regularized formation, using the infimum of all positive-copy quotients. The regularization_limit theorem asserts convergence to this value; no existence of a limit is assumed. On density inputs the nonempty set is bounded below by zero.
--   - `IsOptimalEnsemble`: PDF p.3, Lemma 2: the supplied finite pure ensemble is optimal for formation. The accepted ensemble includes unit vectors and nonnegative weights summing to one. No restriction excludes pure states or zero weights.
--   - `IsStateMetric`: PDF p.5, final paragraph: genuine metrics on the normalized density states in each positive finite local dimension. Values on nonstates are unrestricted.
--   - `UniformlyEquivalentToBures`: PDF p.5, final paragraph: dimension-independent equivalence at zero, interpreted as uniform control in both directions. Each eta is chosen before all dimensions and all normalized state pairs. This is stronger than merely having the same topology separately in every dimension.
-- source:
--   The asymptotic entanglement cost of preparing a quantum state, arXiv:quant-ph/0008134v1, https://arxiv.org/abs/quant-ph/0008134v1

import Mathlib
import Definitions.Def_QAlgorithms_Defs_QuantumOutputMetrics
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P08
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P21
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P80

/-!
Statements of Hayden--Horodecki--Terhal, arXiv:quant-ph/0008134v1.
Only pinned accepted library modules are imported. Paper-local definitions adapt
accepted finite adaptive LOCC and grouped tensor powers to natural dimensions.
All costs use deterministic, unconditional finite LOCC protocols. No closure of
LOCC, separable-operation relaxation, or channel simulation is assumed.
-/

namespace QAlgorithms.Papers.Independent.Dependency50.P42

open scoped Matrix ComplexConjugate ComplexOrder
open Information100.P21 (Op)

noncomputable section

/-- PDF pp.1--3: a fixed local basis identification of n copies with dimension a^n.
The same identification is used for all states and both matrix indices. -/
def copyIndex (a n : ℕ) : (Fin n → Fin a) ≃ Fin (a ^ n) :=
  Fintype.equivFinOfCardEq (by simp)

/-- PDF pp.1--3: dimension adapter for the imported grouped tensor power.
This wrapper only relabels each local basis to Fin(a^n) or Fin(b^n), as required
by the accepted FiniteLOCC endpoints; it does not redefine the tensor product. -/
def dimensionedPower {a b : ℕ} (rho : Op (Fin a × Fin b)) (n : ℕ) : Op (Fin (a ^ n) × Fin (b ^ n)) :=
  fun p q => Information100.P80.groupedPower rho n
    ((copyIndex a n).symm p.1, (copyIndex b n).symm p.2)
    ((copyIndex a n).symm q.1, (copyIndex b n).symm q.2)

/-- PDF p.1: the singlet (|01> - |10>)/sqrt(2); sqrt(2)/2 is the same coefficient. -/
def singletVector : EuclideanSpace ℂ (Fin 2 × Fin 2) :=
  WithLp.toLp 2 fun p =>
    if p = (0, 1) then ((Real.sqrt 2 / 2 : ℝ) : ℂ)
    else if p = (1, 0) then -((Real.sqrt 2 / 2 : ℝ) : ℂ) else 0

/-- PDF pp.1--2: the normalized two-qubit singlet density. -/
def singletState : Op (Fin 2 × Fin 2) := pureDensity singletVector

/-- PDF p.2, Eq.(6): a deterministic natural number m of shared singlets.
At m=0 this is the scalar trace-one state, with no shared entanglement. -/
def singlets (m : ℕ) : Op (Fin (2 ^ m) × Fin (2 ^ m)) := dimensionedPower singletState m

/-- PDF pp.2,5: state distances for every finite bipartite dimension.
Physical arguments are normalized density matrices in positive local dimensions. -/
abbrev StateDistance := (a b : ℕ) → Op (Fin a × Fin b) → Op (Fin a × Fin b) → ℝ

/-- PDF p.2: D=2 sqrt(1-F), with the accepted root fidelity F.
This differs in scale from the accepted Bures--Wasserstein convention. -/
def paperBures : StateDistance :=
  fun _ _ rho sigma => 2 * Real.sqrt (1 - rootFidelity rho sigma)

/-- PDF p.5, Eq.(24): precisely half the trace norm. -/
def halfTraceDistance : StateDistance := fun _ _ rho sigma => traceDistance rho sigma

/-- PDF p.2, Eq.(6): paper-specific finite-block formation feasibility.
The accepted AchievableRate predicates concern channel codes and cannot
replace this state-formation definition. The protocol class is the
accepted finite adaptive LOCC tree, with complete local rectangular Kraus
instruments and outcome-dependent continuations. Its output is the sum over
all branches, hence normalized on normalized inputs. Local ancillas, disposal,
and unrestricted two-way classical messages are allowed; there is no postselection.
Both m and the positive block length n are selected after both tolerances. -/
def FiniteBlockFormationRate {a b : ℕ} (M : StateDistance) (rho : Op (Fin a × Fin b)) (E : ℝ) : Prop :=
  ∀ epsilon > (0 : ℝ), ∀ delta > (0 : ℝ),
    ∃ m n : ℕ, 0 < n ∧
      ∃ L : Superop (Fin (2 ^ m) × Fin (2 ^ m)) (Fin (a ^ n) × Fin (b ^ n)),
        Information100.P21.FiniteLOCC L ∧
        |E - (m : ℝ) / (n : ℝ)| ≤ delta ∧
        M (a ^ n) (b ^ n) (L (singlets m)) (dimensionedPower rho n) ≤ epsilon

/-- PDF p.2, Eq.(6): infimum of the actual operational feasible rates.
For density inputs in positive finite dimensions and the state metrics used
below, the set is nonempty (finite exact preparation by teleportation) and
bounded below by zero. Values on nonphysical matrices are not used. -/
def entanglementCost {a b : ℕ} (M : StateDistance) (rho : Op (Fin a × Fin b)) : ℝ :=
  sInf {E : ℝ | FiniteBlockFormationRate M rho E}

/-- PDF p.5, Eq.(21): eventual feasibility. For every pair of tolerances there
is a threshold, then for every n>N a possibly different m and LOCC protocol.
The strict threshold automatically excludes n=0. -/
def EventuallyAchievableRate {a b : ℕ} (M : StateDistance) (rho : Op (Fin a × Fin b))
    (E : ℝ) : Prop :=
  ∀ epsilon > (0 : ℝ), ∀ delta > (0 : ℝ), ∃ N : ℕ,
    ∀ n : ℕ, N < n → ∃ m : ℕ,
      ∃ L : Superop (Fin (2 ^ m) × Fin (2 ^ m)) (Fin (a ^ n) × Fin (b ^ n)),
        Information100.P21.FiniteLOCC L ∧
        |E - (m : ℝ) / (n : ℝ)| ≤ delta ∧
        M (a ^ n) (b ^ n) (L (singlets m)) (dimensionedPower rho n) ≤ epsilon

/-- PDF p.5, Eq.(21): infimum of eventually achievable rates, separately from
Eq.(6). For the physical inputs and distances in the theorems, exact preparation
gives a nonempty rate set and every feasible rate is nonnegative. -/
def alternativeCost {a b : ℕ} (M : StateDistance) (rho : Op (Fin a × Fin b)) : ℝ :=
  sInf {E : ℝ | EventuallyAchievableRate M rho E}

/-- PDF pp.1,3, Eqs.(1),(8): the positive-copy formation quotients.
Index n denotes n+1 copies, so the denominator is never zero. Entropy is in bits. -/
def formationSequence {a b : ℕ} (rho : Op (Fin a × Fin b)) (n : ℕ) : ℝ :=
  Information100.P08.formation (dimensionedPower rho (n + 1)) / ((n + 1 : ℕ) : ℝ)

/-- PDF pp.1,3: a total representative of regularized formation, using the
infimum of all positive-copy quotients. The regularization_limit theorem asserts
convergence to this value; no existence of a limit is assumed. On density inputs
the nonempty set is bounded below by zero. -/
def regularizedFormation {a b : ℕ} (rho : Op (Fin a × Fin b)) : ℝ :=
  sInf (Set.range (formationSequence rho))

/-- PDF p.3, Lemma 2: the supplied finite pure ensemble is optimal for formation.
The accepted ensemble includes unit vectors and nonnegative weights summing to
one. No restriction excludes pure states or zero weights. -/
def IsOptimalEnsemble {a b : ℕ} (rho : Op (Fin a × Fin b))
    (e : Information100.P08.PureEnsemble (Fin a × Fin b)) : Prop :=
  Information100.P08.pureAverage e = rho ∧
    (∑ i, e.prob i * vnEntropy (traceRight (pureDensity (e.vector i)))) =
      Information100.P08.formation rho

/-- PDF p.5, final paragraph: genuine metrics on the normalized density states
in each positive finite local dimension. Values on nonstates are unrestricted. -/
def IsStateMetric (M : StateDistance) : Prop :=
  (∀ a b : ℕ, 0 < a → 0 < b → ∀ rho sigma : Op (Fin a × Fin b),
    IsDensityMatrix rho → IsDensityMatrix sigma →
      0 ≤ M a b rho sigma ∧ (M a b rho sigma = 0 ↔ rho = sigma) ∧
        M a b rho sigma = M a b sigma rho) ∧
  (∀ a b : ℕ, 0 < a → 0 < b → ∀ rho sigma tau : Op (Fin a × Fin b),
    IsDensityMatrix rho → IsDensityMatrix sigma → IsDensityMatrix tau →
      M a b rho tau ≤ M a b rho sigma + M a b sigma tau)

/-- PDF p.5, final paragraph: dimension-independent equivalence at zero,
interpreted as uniform control in both directions. Each eta is chosen before
all dimensions and all normalized state pairs. This is stronger than merely
having the same topology separately in every dimension. -/
def UniformlyEquivalentToBures (M : StateDistance) : Prop :=
  (∀ epsilon > (0 : ℝ), ∃ eta > (0 : ℝ),
    ∀ a b : ℕ, 0 < a → 0 < b → ∀ rho sigma : Op (Fin a × Fin b),
      IsDensityMatrix rho → IsDensityMatrix sigma →
        M a b rho sigma ≤ eta → paperBures a b rho sigma ≤ epsilon) ∧
  (∀ epsilon > (0 : ℝ), ∃ eta > (0 : ℝ),
    ∀ a b : ℕ, 0 < a → 0 < b → ∀ rho sigma : Op (Fin a × Fin b),
      IsDensityMatrix rho → IsDensityMatrix sigma →
        paperBures a b rho sigma ≤ eta → M a b rho sigma ≤ epsilon)

/-- Sanity: the transported copy matrix is exactly the grouped entry product. -/
example {a b : ℕ} (rho : Op (Fin a × Fin b)) (n : ℕ)
    (x y : (Fin n → Fin a) × (Fin n → Fin b)) :
    dimensionedPower rho n (copyIndex a n x.1, copyIndex b n x.2)
      (copyIndex a n y.1, copyIndex b n y.2) =
        ∏ i, rho (x.1 i, x.2 i) (y.1 i, y.2 i) := by
  simp [dimensionedPower, Information100.P80.groupedPower]

/-- Sanity: zero copies give the scalar trace-one matrix. -/
example {a b : ℕ} (rho : Op (Fin a × Fin b)) : dimensionedPower rho 0 = 1 := by
  letI : Subsingleton (Fin (a ^ 0) × Fin (b ^ 0)) := by
    simp only [pow_zero]
    infer_instance
  ext p q
  have hpq : p = q := Subsingleton.elim _ _
  subst q
  simp [dimensionedPower, Information100.P80.groupedPower]

/-- Sanity: the singlet has negative off-diagonal coherence. -/
example : singletState (0, 1) (1, 0) = (-1 / 2 : ℂ) := by
  have h : (Real.sqrt 2 / 2) * (Real.sqrt 2 / 2) = (1 / 2 : ℝ) := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  change ((Real.sqrt 2 / 2 : ℝ) : ℂ) *
    conj (-((Real.sqrt 2 / 2 : ℝ) : ℂ)) = (-1 / 2 : ℂ)
  rw [map_neg, Complex.conj_ofReal, mul_neg, ← Complex.ofReal_mul, h]
  norm_num

/-- Sanity: the source singlet density has trace one. -/
example : singletState.trace = 1 := by
  have h : (Real.sqrt 2 / 2) * (Real.sqrt 2 / 2) = (1 / 2 : ℝ) := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  change (∑ p : Fin 2 × Fin 2, singletVector p * conj (singletVector p)) = 1
  rw [Fintype.sum_prod_type]
  simp only [Fin.sum_univ_two]
  change ((0 : ℂ) * conj 0 + ((Real.sqrt 2 / 2 : ℝ) : ℂ) *
      conj ((Real.sqrt 2 / 2 : ℝ) : ℂ)) +
    (-((Real.sqrt 2 / 2 : ℝ) : ℂ) * conj (-((Real.sqrt 2 / 2 : ℝ) : ℂ)) +
      0 * conj 0) = 1
  simp only [map_neg, Complex.conj_ofReal, map_zero, mul_zero,
    zero_add, add_zero, neg_mul_neg, ← Complex.ofReal_mul, h]
  norm_num

/-- Sanity: zero singlets permit zero-rate preparation of a one-dimensional
product state by the identity finite LOCC protocol. -/
example : FiniteBlockFormationRate paperBures (1 : Op (Fin 1 × Fin 1)) 0 := by
  intro epsilon hepsilon delta hdelta
  refine ⟨0, 1, by norm_num, (fun X => X),
    Information100.P21.FiniteLOCC.identity 1 1, ?_, ?_⟩
  · simpa using hdelta.le
  · have hs : singlets 0 = 1 := by
      letI : Subsingleton (Fin (2 ^ 0) × Fin (2 ^ 0)) := by
        simp only [pow_zero]
        infer_instance
      ext p q
      have hpq : p = q := Subsingleton.elim _ _
      subst q
      simp [singlets, dimensionedPower, Information100.P80.groupedPower]
    have hc : dimensionedPower (1 : Op (Fin 1 × Fin 1)) 1 = 1 := by
      letI : Subsingleton (Fin (1 ^ 1) × Fin (1 ^ 1)) := by
        simp only [one_pow]
        infer_instance
      ext p q
      have hpq : p = q := Subsingleton.elim _ _
      subst q
      simp [dimensionedPower, Information100.P80.groupedPower]
    simpa [hs, hc, paperBures, rootFidelity, cfc_one] using hepsilon.le

/-- Sanity: the trace-distance specialization has the exact half factor. -/
example {a b : ℕ} (rho sigma : Op (Fin a × Fin b)) :
    halfTraceDistance a b rho sigma = (1 / 2 : ℝ) * traceNorm (rho - sigma) := by
  norm_num [halfTraceDistance, traceDistance]

end

end QAlgorithms.Papers.Independent.Dependency50.P42


