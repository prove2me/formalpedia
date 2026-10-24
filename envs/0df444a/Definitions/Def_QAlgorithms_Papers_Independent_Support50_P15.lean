-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Support50_P15
-- name    : QAlgorithms_Papers_Independent_Support50_P15
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-23T19:34:32.679257+00:00
-- url     : https://prove2.me/theorems/4c67b8a8-07fe-451a-aadf-6cf1346a4543
-- title:
--   Definitions for Tight bound on relative entropy by entropy difference
-- statement:
--   The objects the formalized statements of *Tight bound on relative entropy by entropy difference* (arXiv:1304.0036) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `EntropyState`: Density matrices, including singular ones (PDF p.3, §1.1).
--   - `stateRelativeNats`: Eq. (3), PDF p.3: audited Umegaki entropy, embedded into the signed extended reals.
--   - `difference`: Eq. (2), PDF p.3, with the argument order of the source.
--   - `klTerm`: One term of classical relative entropy; support failure is infinity (PDF p.3).
--   - `binaryRelative`: Binary relative entropy, Eq. (5), PDF p.3, with endpoint limits.
--   - `massLimit`: Largest admissible small-eigenvalue mass in Eq. (6), PDF p.4.
--   - `degenerateSpectrumEntropy`: Entropy of the spectrum (10), PDF pp.3--4.
--   - `entropyDifferenceFeasible`: The scalar feasible set in Eq. (6), PDF p.4.
--   - `tightBound`: Eq. (6), PDF p.4. Infimum of the empty feasible set is +infinity (PDF p.21).
--   - `minimizingPair`: Attainment of the actual scalar optimization (PDF pp.4,20--22).
--   - `familyProb`: The probabilities in the explicitly computed witness (10), PDF p.4.
--   - `family`: The diagonal witness (10), PDF p.4; meaningful for d>=2 and 0<=s<=1.
--   - `varianceObjective`: The function maximized in Eq. (7), PDF p.4; the optimization excludes endpoints.
--   - `maxVariance`: Eq. (7), PDF p.4. On d>=2 the value set is nonempty and bounded.
--   - `easyVariance`: Eq. (8), PDF p.4.
--   - `optimalMass`: The unique maximizing scalar, when d>=2 (PDF pp.8,25).
--   - `surprisalVariance`: Eq. (19), PDF p.7: zero eigenvalues have zero sampling weight.
--   - `stateObservableVariance`: Variance of a Hermitian observable (PDF pp.7--9).
--   - `exponentialBound`: The exponential lower bound in (11), PDF p.4.
--   - `cubicBound`: The cubic polynomial in (11), PDF p.4.
--   - `redundancyScale`: The common denominator L in (46)--(54), PDF pp.14--16.
--   - `redundancyBound`: The explicit lower bound in (51), (52), (54), PDF pp.14--16.
--   - `asymmetryConjecture`: The unproved asymmetry conjecture in a fixed dimension (PDF pp.14--15).
--   - `continuityEntropy`: h_d in (16), PDF p.6.
--   - `entropyInverse`: Inverse on the increasing branch [0,(d-1)/d], PDF p.6, (18).
--   - `inverseEstimate`: The explicit inverse estimate in (18), with its continuous extension at zero (PDF p.6).
--   - `thermalFinite`: Gibbs state at a positive finite temperature, (23), PDF p.8.
--   - `groundSpaceDensity`: Normalized projector onto the entire ground space, PDF p.9.
--   - `gibbsAtTemperature`: Thermal states for all T in [0,infinity], with both endpoint conventions (PDF p.9).
--   - `thermalExpectedEnergy`: Mean energy E(T), PDF p.9.
--   - `heatCapacity`: Heat capacity defined by dE/dT, not by the variance identity (24), PDF p.9.
--   - `optimalHamiltonian`: One fixed optimal Hamiltonian, PDF p.9, Remark 11.
--   - `fullRank`: Full rank on the already restricted finite-dimensional support, PDF p.10.
--   - `EntropyPathPartition`: An arbitrary strict partition, for (38)--(40), PDF p.12.
--   - `mesh`: Mesh controls all subdivisions, not just uniform ones (PDF p.12).
--   - `piecewiseC1`: Piecewise C1 means globally continuous with C1 restrictions on a finite subdivision (p.12).
--   - `entropyHeatSum`: The right-endpoint Riemann sum in (38), PDF p.12.
--   - `partitionHeat`: Actual heat divided by bath temperature, H_j=-T_j log rho(t_j), (27),(38), pp.10,12.
--   - `Process`: The actual finite sequence of states and step Hamiltonians (PDF pp.10,13).
--   - `isIsothermal`: Isothermal equilibration, with final Hamiltonian equal to the fixed external H (p.13).
--   - `processHeat`: Heat is computed from the Hamiltonians and state increments (27), PDF pp.10,13.
--   - `extractedWork`: Extracted work = heat - internal energy increase (41)--(42), PDF p.13.
--   - `helmholtzFreeEnergy`: Free energy at the fixed Hamiltonian and temperature (41), PDF p.13.
--   - `availableWork`: Available work computed from free energies, not defined as a process optimum (41), p.13.
--   - `extendedDomainInfimum`: A minimum over a specified domain in the complete extended real order (pp.14--16).
--   - `attainsMinimum`: Actual attainment, retained whenever the source writes min (PDF p.14).
--   - `minimaxRedundancy`: Minimal redundancy (47), PDF p.14, over quantum states as also asserted on p.15.
--   - `minEntropy`: Minimal entropy of the finite nonempty source family (PDF p.14).
--   - `sourceEntropyMaximum`: Maximal entropy of the finite nonempty source family (PDF p.14).
--   - `entropyRadius`: The intermediate objective in (48), PDF p.14.
--   - `isLaw`: A normalized classical law in the paper's fixed basis (PDF p.3).
--   - `shannonEntropyNats`: Natural-log Shannon entropy, matching the diagonal density matrix (PDF p.3).
--   - `FiniteOutputChannel`: Classical channel, as in Proposition 13, PDF p.15; X need not be finite.
--   - `finiteOutputCapacityNats`: Nats capacity: supremum of mutual information over all finite-support input laws (p.15). For finite output this covers arbitrary nonempty discrete input alphabets by approximation.
--   - `entropyConstraintDistance`: Eq. (53), PDF p.16, with a strict entropy constraint and empty-set value infinity.
--   - `chernoffCoefficient`: Chernoff coefficient infimum including one-sided endpoint limits, PDF p.16. Using 0<s<1 avoids the spurious 0^0=1 at singular endpoints.
--   - `chernoff`: Classical Chernoff information; disjoint support gives infinity (54), PDF p.16.
-- source:
--   Tight bound on relative entropy by entropy difference, arXiv:1304.0036v3, https://arxiv.org/abs/1304.0036v3

import Mathlib
import Definitions.Def_QAlgorithms_Defs_ExtendedQuantumEntropy
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P56

/-!
Reeb and Wolf, arXiv:1304.0036v3. All logarithms below are natural.
The accepted entropy in nats is imported from Information100.P56.
Distinct paper-local definitions have complete bodies; only result statements use `sorry`.
-/

noncomputable section

attribute [local instance] Classical.propDecidable

open scoped Matrix ComplexConjugate ENNReal Matrix.Norms.L2Operator
open Filter MeasureTheory

namespace QAlgorithms.Papers.Independent.Support50.P15

-- Exact accepted entropy in nats; no local redeclaration.
open QAlgorithms.Papers.Independent.Information100.P56 (entropy)

/-- Density matrices, including singular ones (PDF p.3, §1.1). -/
abbrev EntropyState (d : ℕ) := {a : Matrix (Fin d) (Fin d) ℂ // IsDensityMatrix a}

/-- Eq. (3), PDF p.3: audited Umegaki entropy, embedded into the signed extended reals. -/
def stateRelativeNats {d : ℕ} (a b : EntropyState d) : EReal :=
  (QuantumLoss.umegakiEntropy a.val b.val a.property b.property).toEReal

/-- Eq. (2), PDF p.3, with the argument order of the source. -/
def difference {d : ℕ} (a b : Matrix (Fin d) (Fin d) ℂ) : ℝ := entropy a - entropy b

/-- One term of classical relative entropy; support failure is infinity (PDF p.3). -/
def klTerm (p q : ℝ) : EReal :=
  if p = 0 then 0 else if q = 0 then ⊤ else (p * Real.log (p / q) : ℝ)

/-- Binary relative entropy, Eq. (5), PDF p.3, with endpoint limits. -/
def binaryRelative (s r : ℝ) : EReal := klTerm s r + klTerm (1 - s) (1 - r)

/-- Largest admissible small-eigenvalue mass in Eq. (6), PDF p.4. -/
def massLimit (d : ℕ) : ℝ := ((d : ℝ) - 1) / d

/-- Entropy of the spectrum (10), PDF pp.3--4. -/
def degenerateSpectrumEntropy (d : ℕ) (s : ℝ) : ℝ := Real.binEntropy s + s * Real.log ((d : ℝ) - 1)

/-- The scalar feasible set in Eq. (6), PDF p.4. -/
def entropyDifferenceFeasible (d : ℕ) (delta s r : ℝ) : Prop :=
  s ∈ Set.Icc 0 (massLimit d) ∧ r ∈ Set.Icc 0 (massLimit d) ∧
    degenerateSpectrumEntropy d s - degenerateSpectrumEntropy d r = delta

/-- Eq. (6), PDF p.4. Infimum of the empty feasible set is +infinity (PDF p.21). -/
def tightBound (d : ℕ) (delta : ℝ) : EReal :=
  sInf {v | ∃ s r : ℝ, entropyDifferenceFeasible d delta s r ∧ v = binaryRelative s r}

/-- Attainment of the actual scalar optimization (PDF pp.4,20--22). -/
def minimizingPair (d : ℕ) (delta s r : ℝ) : Prop :=
  entropyDifferenceFeasible d delta s r ∧ binaryRelative s r = tightBound d delta

/-- The probabilities in the explicitly computed witness (10), PDF p.4. -/
def familyProb (d : ℕ) (s : ℝ) (i : Fin d) : ℝ :=
  if i.val = 0 then 1 - s else s / ((d : ℝ) - 1)

/-- The diagonal witness (10), PDF p.4; meaningful for d>=2 and 0<=s<=1. -/
def family (d : ℕ) (s : ℝ) : Matrix (Fin d) (Fin d) ℂ :=
  Matrix.diagonal (fun i => (familyProb d s i : ℂ))

/-- The function maximized in Eq. (7), PDF p.4; the optimization excludes endpoints. -/
def varianceObjective (d : ℕ) (r : ℝ) : ℝ :=
  r * (1 - r) * (Real.log ((1 - r) / r * ((d : ℝ) - 1))) ^ 2

/-- Eq. (7), PDF p.4. On d>=2 the value set is nonempty and bounded. -/
def maxVariance (d : ℕ) : ℝ :=
  sSup (varianceObjective d '' Set.Ioo 0 (1 / 2))

/-- Eq. (8), PDF p.4. -/
def easyVariance (d : ℕ) : ℝ := (Real.log ((d : ℝ) - 1)) ^ 2 / 4 + 1

/-- The unique maximizing scalar, when d>=2 (PDF pp.8,25). -/
def optimalMass (d : ℕ) : ℝ :=
  Classical.epsilon (fun r : ℝ => r ∈ Set.Ioo 0 (1 / 2) ∧ varianceObjective d r = maxVariance d)

/-- Eq. (19), PDF p.7: zero eigenvalues have zero sampling weight. -/
def surprisalVariance {d : ℕ} (a : Matrix (Fin d) (Fin d) ℂ) : ℝ :=
  (cfc (fun x : ℝ => x * (Real.log x) ^ 2) a).trace.re - (entropy a) ^ 2

/-- Variance of a Hermitian observable (PDF pp.7--9). -/
def stateObservableVariance {d : ℕ} (a h : Matrix (Fin d) (Fin d) ℂ) : ℝ :=
  (a * h ^ 2).trace.re - ((a * h).trace.re) ^ 2

/-- The exponential lower bound in (11), PDF p.4. -/
def exponentialBound (n delta : ℝ) : ℝ := n * (Real.exp (delta / n) - 1 - delta / n)

/-- The cubic polynomial in (11), PDF p.4. -/
def cubicBound (n delta : ℝ) : ℝ := delta ^ 2 / (2 * n) + delta ^ 3 / (6 * n ^ 2)

/-- The common denominator L in (46)--(54), PDF pp.14--16. -/
def redundancyScale (d : ℕ) : ℝ := (Real.log ((d : ℝ) - 1)) ^ 2 + 4

/-- The explicit lower bound in (51), (52), (54), PDF pp.14--16. -/
def redundancyBound (d : ℕ) (a : ℝ) : ℝ :=
  a ^ 2 / (2 * redundancyScale d) - a ^ 3 / (3 * (redundancyScale d) ^ 2)

/-- The unproved asymmetry conjecture in a fixed dimension (PDF pp.14--15). -/
def asymmetryConjecture (d : ℕ) : Prop :=
  ∀ a ∈ Set.Icc 0 (Real.log d), tightBound d (-a) ≤ tightBound d a

/-- h_d in (16), PDF p.6. -/
def continuityEntropy (d : ℕ) (t : ℝ) : ℝ := t * Real.log ((d : ℝ) - 1) + Real.binEntropy t

/-- Inverse on the increasing branch [0,(d-1)/d], PDF p.6, (18). -/
def entropyInverse (d : ℕ) (a : ℝ) : ℝ :=
  sInf {t | t ∈ Set.Icc 0 (massLimit d) ∧ a ≤ continuityEntropy d t}

/-- The explicit inverse estimate in (18), with its continuous extension at zero (PDF p.6). -/
def inverseEstimate (d : ℕ) (a : ℝ) : ℝ :=
  if a = 0 then 0 else (Real.exp 1 - 1) / Real.exp 1 * a /
    (1 + Real.log ((d : ℝ) - 1) - Real.log a)

/-- Gibbs state at a positive finite temperature, (23), PDF p.8. -/
def thermalFinite {d : ℕ} (h : Matrix (Fin d) (Fin d) ℂ) (t : ℝ) : Matrix (Fin d) (Fin d) ℂ :=
  gibbsState (-((t : ℂ)⁻¹) • h)

/-- Normalized projector onto the entire ground space, PDF p.9. -/
def groundSpaceDensity {d : ℕ} (h : Matrix (Fin d) (Fin d) ℂ) : Matrix (Fin d) (Fin d) ℂ :=
  if hd : 0 < d then
    let e := ascEigenvalues h ⟨0, by simpa only [Fintype.card_fin] using hd⟩
    let p := cfc (fun x : ℝ => if x = e then 1 else 0) h
    p.trace⁻¹ • p
  else 0

/-- Thermal states for all T in [0,infinity], with both endpoint conventions (PDF p.9). -/
def gibbsAtTemperature {d : ℕ} (h : Matrix (Fin d) (Fin d) ℂ) (t : ℝ≥0∞) : Matrix (Fin d) (Fin d) ℂ :=
  if t = ⊤ then (d : ℂ)⁻¹ • 1 else if t = 0 then groundSpaceDensity h else thermalFinite h t.toReal

/-- Mean energy E(T), PDF p.9. -/
def thermalExpectedEnergy {d : ℕ} (h : Matrix (Fin d) (Fin d) ℂ) (t : ℝ) : ℝ :=
  (h * thermalFinite h t).trace.re

/-- Heat capacity defined by dE/dT, not by the variance identity (24), PDF p.9. -/
def heatCapacity {d : ℕ} (h : Matrix (Fin d) (Fin d) ℂ) (t : ℝ≥0∞) : ℝ :=
  if t = 0 ∨ t = ⊤ then 0 else deriv (thermalExpectedEnergy h) t.toReal

/-- One fixed optimal Hamiltonian, PDF p.9, Remark 11. -/
def optimalHamiltonian (d : ℕ) : Matrix (Fin d) (Fin d) ℂ :=
  Matrix.diagonal (fun i => if i.val = 0 then -1 else 0)

/-- Full rank on the already restricted finite-dimensional support, PDF p.10. -/
def fullRank {d : ℕ} (a : Matrix (Fin d) (Fin d) ℂ) : Prop :=
  LinearMap.ker a.mulVecLin = ⊥

/-- An arbitrary strict partition, for (38)--(40), PDF p.12. -/
structure EntropyPathPartition where
  k : ℕ
  positive : 0 < k
  point : Fin (k + 1) → ℝ
  strict : StrictMono point
  first : point 0 = 0
  last : point (Fin.last k) = 1

/-- Mesh controls all subdivisions, not just uniform ones (PDF p.12). -/
def mesh (p : EntropyPathPartition) : ℝ :=
  sSup (Set.range (fun j : Fin p.k => p.point j.succ - p.point j.castSucc))

/-- Piecewise C1 means globally continuous with C1 restrictions on a finite subdivision (p.12). -/
def piecewiseC1 {d : ℕ} (a : ℝ → Matrix (Fin d) (Fin d) ℂ) : Prop :=
  ContinuousOn a (Set.Icc 0 1) ∧ ∃ p : EntropyPathPartition, ∀ j : Fin p.k,
    ContDiffOn ℝ 1 a (Set.Icc (p.point j.castSucc) (p.point j.succ))

/-- The right-endpoint Riemann sum in (38), PDF p.12. -/
def entropyHeatSum {d : ℕ} (a : ℝ → Matrix (Fin d) (Fin d) ℂ) (p : EntropyPathPartition) : ℝ :=
  ∑ j : Fin p.k, ((-cfc Real.log (a (p.point j.succ))) *
    (a (p.point j.succ) - a (p.point j.castSucc))).trace.re

/-- Actual heat divided by bath temperature, H_j=-T_j log rho(t_j), (27),(38), pp.10,12. -/
def partitionHeat {d : ℕ} (a : ℝ → Matrix (Fin d) (Fin d) ℂ) (p : EntropyPathPartition)
    (t : Fin p.k → ℝ) : ℝ :=
  ∑ j : Fin p.k, ((-((t j : ℂ)) • cfc Real.log (a (p.point j.succ))) *
    (a (p.point j.succ) - a (p.point j.castSucc))).trace.re / t j

/-- The actual finite sequence of states and step Hamiltonians (PDF pp.10,13). -/
structure Process (d : ℕ) where
  k : ℕ
  positive : 0 < k
  state : Fin (k + 1) → EntropyState d
  hamiltonian : Fin k → Matrix (Fin d) (Fin d) ℂ

/-- Isothermal equilibration, with final Hamiltonian equal to the fixed external H (p.13). -/
def isIsothermal {d : ℕ} (p : Process d) (h : Matrix (Fin d) (Fin d) ℂ) (t : ℝ)
    (a : EntropyState d) : Prop :=
  p.state 0 = a ∧ (∀ j, fullRank (p.state j).val) ∧
  (∀ j, (p.hamiltonian j).IsHermitian ∧
    (p.state j.succ).val = thermalFinite (p.hamiltonian j) t) ∧
  p.hamiltonian ⟨p.k - 1, Nat.sub_lt p.positive (by decide)⟩ = h

/-- Heat is computed from the Hamiltonians and state increments (27), PDF pp.10,13. -/
def processHeat {d : ℕ} (p : Process d) : ℝ :=
  ∑ j : Fin p.k, (p.hamiltonian j * ((p.state j.succ).val - (p.state j.castSucc).val)).trace.re

/-- Extracted work = heat - internal energy increase (41)--(42), PDF p.13. -/
def extractedWork {d : ℕ} (p : Process d) (h : Matrix (Fin d) (Fin d) ℂ) : ℝ :=
  processHeat p - (h * ((p.state (Fin.last p.k)).val - (p.state 0).val)).trace.re

/-- Free energy at the fixed Hamiltonian and temperature (41), PDF p.13. -/
def helmholtzFreeEnergy {d : ℕ} (h a : Matrix (Fin d) (Fin d) ℂ) (t : ℝ) : ℝ :=
  (h * a).trace.re - t * entropy a

/-- Available work computed from free energies, not defined as a process optimum (41), p.13. -/
def availableWork {d : ℕ} (h : Matrix (Fin d) (Fin d) ℂ) (t : ℝ) (a : EntropyState d) : ℝ :=
  helmholtzFreeEnergy h a.val t - helmholtzFreeEnergy h (thermalFinite h t) t

/-- A minimum over a specified domain in the complete extended real order (pp.14--16). -/
def extendedDomainInfimum {α : Type*} (a : Set α) (f : α → EReal) : EReal := sInf (f '' a)

/-- Actual attainment, retained whenever the source writes min (PDF p.14). -/
def attainsMinimum {α : Type*} (a : Set α) (f : α → EReal) : Prop :=
  ∃ x ∈ a, f x = extendedDomainInfimum a f

/-- Minimal redundancy (47), PDF p.14, over quantum states as also asserted on p.15. -/
def minimaxRedundancy {d m : ℕ} (a : Fin m → EntropyState d) : EReal :=
  ⨅ b : EntropyState d, ⨆ j, stateRelativeNats (a j) b

/-- Minimal entropy of the finite nonempty source family (PDF p.14). -/
def minEntropy {d m : ℕ} (a : Fin m → EntropyState d) : ℝ := sInf (Set.range (fun j => entropy (a j).val))

/-- Maximal entropy of the finite nonempty source family (PDF p.14). -/
def sourceEntropyMaximum {d m : ℕ} (a : Fin m → EntropyState d) : ℝ := sSup (Set.range (fun j => entropy (a j).val))

/-- The intermediate objective in (48), PDF p.14. -/
def entropyRadius {d m : ℕ} (a : Fin m → EntropyState d) (s : ℝ) : EReal :=
  ⨆ j, tightBound d (entropy (a j).val - s)

/-- A normalized classical law in the paper's fixed basis (PDF p.3). -/
def isLaw {d : ℕ} (p : Fin d → ℝ) : Prop := (∀ i, 0 ≤ p i) ∧ ∑ i, p i = 1

/-- Natural-log Shannon entropy, matching the diagonal density matrix (PDF p.3). -/
def shannonEntropyNats {d : ℕ} (p : Fin d → ℝ) : ℝ := -∑ i, p i * Real.log (p i)

/-- Classical channel, as in Proposition 13, PDF p.15; X need not be finite. -/
structure FiniteOutputChannel (X : Type*) (d : ℕ) where
  prob : X → Fin d → ℝ
  normalized : ∀ x, isLaw (prob x)

/-- Nats capacity: supremum of mutual information over all finite-support input laws (p.15).
For finite output this covers arbitrary nonempty discrete input alphabets by approximation. -/
def finiteOutputCapacityNats {X : Type*} {d : ℕ} (c : FiniteOutputChannel X d) : ℝ :=
  sSup {v | ∃ (m : ℕ) (x : Fin m → X) (q : Fin m → ℝ), isLaw q ∧
    v = shannonEntropyNats (fun y => ∑ j, q j * c.prob (x j) y) -
      ∑ j, q j * shannonEntropyNats (c.prob (x j))}

/-- Eq. (53), PDF p.16, with a strict entropy constraint and empty-set value infinity. -/
def entropyConstraintDistance {d : ℕ} (r : ℝ) (a : EntropyState d) : EReal :=
  ⨅ b : {b : EntropyState d // r < entropy b.val}, stateRelativeNats b.val a

/-- Chernoff coefficient infimum including one-sided endpoint limits, PDF p.16.
Using 0<s<1 avoids the spurious 0^0=1 at singular endpoints. -/
def chernoffCoefficient {d : ℕ} (p q : Fin d → ℝ) : ℝ :=
  sInf ((fun s : ℝ => ∑ i, (p i) ^ s * (q i) ^ (1 - s)) '' Set.Ioo 0 1)

/-- Classical Chernoff information; disjoint support gives infinity (54), PDF p.16. -/
def chernoff {d : ℕ} (p q : Fin d → ℝ) : EReal :=
  let z := chernoffCoefficient p q
  if z = 0 then ⊤ else (-Real.log z : ℝ)

/-! Definition-level boundary sanity tests. -/

example {d : ℕ} : entropy (1 : Matrix (Fin d) (Fin d) ℂ) = 0 := by
  simp [entropy, cfc_one]

example (q : ℝ) : klTerm 0 q = 0 := by simp [klTerm]

example : binaryRelative 0 0 = 0 := by simp [binaryRelative, klTerm]

example {s : ℝ} (hs : s ≠ 0) : klTerm s 0 = ⊤ := by simp [klTerm, hs]

example : familyProb 2 (1 / 2) 0 = 1 / 2 := by norm_num [familyProb]

example (d : ℕ) : degenerateSpectrumEntropy d 0 = 0 := by simp [degenerateSpectrumEntropy]

example : easyVariance 2 = 1 := by norm_num [easyVariance]

example (n : ℝ) : exponentialBound n 0 = 0 ∧ cubicBound n 0 = 0 := by
  simp [exponentialBound, cubicBound]

example (d : ℕ) : inverseEstimate d 0 = 0 := by simp [inverseEstimate]

example {d : ℕ} (h : Matrix (Fin d) (Fin d) ℂ) :
    gibbsAtTemperature h ⊤ = (d : ℂ)⁻¹ • 1 ∧ gibbsAtTemperature h 0 = groundSpaceDensity h := by simp [gibbsAtTemperature]

example {d : ℕ} (h : Matrix (Fin d) (Fin d) ℂ) :
    heatCapacity h 0 = 0 ∧ heatCapacity h ⊤ = 0 := by simp [heatCapacity]

example {α : Type*} (f : α → EReal) : extendedDomainInfimum ∅ f = ⊤ := by simp [extendedDomainInfimum]

example (d : ℕ) : redundancyBound d 0 = 0 := by simp [redundancyBound]

open scoped ComplexOrder in
example : IsDensityMatrix (1 : Matrix (Fin 1) (Fin 1) ℂ) :=
  ⟨Matrix.PosSemidef.one, by simp⟩

example {d : ℕ} (a : EntropyState d) : difference a.val a.val = 0 := by
  simp [difference]

example : surprisalVariance (1 : Matrix (Fin 1) (Fin 1) ℂ) = 0 := by
  simp [surprisalVariance, entropy, cfc_one]

example {d : ℕ} (a : Matrix (Fin d) (Fin d) ℂ) (p : EntropyPathPartition) :
    entropyHeatSum (fun _ => a) p = 0 := by
  simp [entropyHeatSum]

example : isLaw (fun _ : Fin 1 => (1 : ℝ)) := by simp [isLaw]

example : ¬ isLaw (fun i : Fin 0 => (Fin.elim0 i : ℝ)) := by simp [isLaw]

example : shannonEntropyNats (fun _ : Fin 1 => (1 : ℝ)) = 0 := by
  simp [shannonEntropyNats]

end QAlgorithms.Papers.Independent.Support50.P15


