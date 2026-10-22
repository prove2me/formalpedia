-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Gap20_P05
-- name    : QAlgorithms_Papers_Independent_Gap20_P05
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-21T23:04:40.977276+00:00
-- url     : https://prove2.me/theorems/7809d93f-9119-442d-b44c-9ed18c0acf7f
-- title:
--   Definitions for On the quantification of entanglement in infinite-dimensional quantum systems
-- statement:
--   The objects the formalized statements of *On the quantification of entanglement in infinite-dimensional quantum systems* (arXiv:quant-ph/0112064) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `HamiltonianData`: PDF pp.2--3, (1)--(2): ordered local eigenvalues, with multiplicity, and finite joint Gibbs partition sum at every positive inverse temperature. These real eigenvalues retain an arbitrary finite ground energy.
--   - `levelEnergy`: PDF p.2: the energy of the sum Hamiltonian in the product eigenbasis.
--   - `spectralHamiltonian`: PDF pp.2--4: adapt the ordered sum spectrum to the frozen semibounded Hamiltonian. Its frozen meanEnergy retains the finite ground energy and infinity.
--   - `energyBound`: PDF p.4, (10): the STRICT energy sublevel in the entire trace-norm state space.
--   - `marginalEntropy`: PDF p.3, (3): entropy of the A marginal, also used for mixed states.
--   - `exampleDelta`: PDF p.3, Example 1: delta_k = 1/log_2 k, used only for k>=2.
--   - `exampleVector`: PDF p.3, (4): the specified vector in the fixed energy eigenbasis. The theorem shifts the index to k+2 to remove the undefined printed k=1.
--   - `copyLevelEnergy`: PDF pp.6--8: printed H^{tensor n}; changed to the additive n-copy Hamiltonian. The energy n*M and the product Gibbs state used by the proof require the sum of the single-copy Hamiltonians, not a product of their eigenvalues.
--   - `copySpectralHamiltonian`: PDF pp.6--8: additive copy spectrum adapted to the frozen Hamiltonian; its lower bound is n times the original finite ground energy.
--   - `copyMeanEnergy`: PDF pp.6--8: use frozen meanEnergy for the additive copy Hamiltonian. The argument is a normalized state; divergent expectations remain infinity.
--   - `FiniteRank`: PDF p.6, Lemma 5: finite operator rank, without restriction to energy coordinates. This is a finite sum of rank-one operators on the full one-system Hilbert space.
--   - `FiniteSchmidtRank`: PDF pp.6,10,12: printed finite-dimensional subspace of S(H); changed to finite LOCAL support, equivalently finite Schmidt rank. The finite-dimensional systems in the preamble and Lemma 5 applied to the A marginal pin this reading. Global rank one would make the condition automatic; no energy-basis cutoff is used.
--   - `countableFormationBits`: PDF pp.8--9, (31)--(32): frozen countable trace-norm pure-state roof, converted from nats to bits. Frozen Information100.P08.formation uses finite ensembles on finite-dimensional spaces and cannot represent this domain. No energy constraint on components or optimal decomposition is assumed.
--   - `ComparisonState`: PDF p.11: both expressly allowed comparison sets. false selects the closed convex hull D of products; true selects the trace-norm closure P of PPT states.
--   - `comparisonRelativeEntropyBits`: PDF p.11, (45): infimum over ALL comparison states, without an energy bound. The generalized relative entropy has the usual value on normalized states; converting nats to bits preserves infinity and support failure.
-- source:
--   On the quantification of entanglement in infinite-dimensional quantum systems, arXiv:quant-ph/0112064v3, https://arxiv.org/abs/quant-ph/0112064v3

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P33
import Definitions.Def_QAlgorithms_Papers_Independent_Frontier18_P01
import Definitions.Def_QAlgorithms_Defs_BipartiteSeparability
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P07
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P63
import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P26
import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P42

/-!
On the quantification of entanglement in infinite-dimensional quantum systems,
arXiv:quant-ph/0112064v3. The explicitly authorized pinned accepted library
supplies nuclear trace class and the full trace norm on completed l2 spaces.
Both local systems have basis N; no cutoff is imposed. Entropy is in bits.
The two deferred intermediate assertions (24) and (27) are not premises.
Compilation is pending the batch mechanical handoff.
-/

noncomputable section

open Filter
open scoped ENNReal BigOperators Topology

attribute [local instance] Classical.propDecidable Classical.decEq

namespace QAlgorithms.Papers.Independent.Gap20.P05

open QAlgorithms.RealRegisters (Hilbert)
open QAlgorithms.Papers.Independent.Dependency50.P33
  (State PureState IsDensity rankOne traceSize traceClosure IsSeparable)
open QAlgorithms.Papers.Independent.Frontier18.P01
  (generalizedRelativeEntropy traceSecond)
open QAlgorithms.Entanglement (partialTransposeFirst)
open QAlgorithms.Papers.Independent.Dependency50.P07 (bipartitePower)
open QAlgorithms.Papers.Independent.Information100.P63 (tensorPower)
open QAlgorithms.Papers.Independent.Gap48.P26 (entropyBits)

/-- PDF pp.2--3, (1)--(2): ordered local eigenvalues, with multiplicity, and
finite joint Gibbs partition sum at every positive inverse temperature.
These real eigenvalues retain an arbitrary finite ground energy. -/
structure HamiltonianData where
  energyA : ℕ → ℝ
  energyB : ℕ → ℝ
  orderedA : Monotone energyA
  orderedB : Monotone energyB
  gibbs : ∀ beta : ℝ, 0 < beta →
    Summable (fun p : ℕ × ℕ => Real.exp (-beta * (energyA p.1 + energyB p.2)))

/-- PDF p.2: the energy of the sum Hamiltonian in the product eigenbasis. -/
def levelEnergy (h : HamiltonianData) (p : ℕ × ℕ) : ℝ :=
  h.energyA p.1 + h.energyB p.2

/-- PDF pp.2--4: adapt the ordered sum spectrum to the frozen semibounded
Hamiltonian. Its frozen meanEnergy retains the finite ground energy and infinity. -/
def spectralHamiltonian (h : HamiltonianData) :
    QAlgorithms.Papers.Independent.Frontier18.P01.Hamiltonian (ℕ × ℕ) where
  energy := levelEnergy h
  lower := levelEnergy h (0, 0)
  bounded_below := by
    intro p
    exact add_le_add (h.orderedA (Nat.zero_le p.1)) (h.orderedB (Nat.zero_le p.2))

/-- PDF p.4, (10): the STRICT energy sublevel in the entire trace-norm state space. -/
def energyBound (h : HamiltonianData) (M : ℝ) : Set (State (ℕ × ℕ)) :=
  {rho | (spectralHamiltonian h).meanEnergy rho < (M : EReal)}

/-- PDF p.3, (3): entropy of the A marginal, also used for mixed states. -/
def marginalEntropy {I J : Type} (X : Matrix (I × J) (I × J) ℂ) : ℝ≥0∞ :=
  entropyBits (traceSecond X)

/-- PDF p.3, Example 1: delta_k = 1/log_2 k, used only for k>=2. -/
def exampleDelta (k : ℕ) : ℝ := Real.log 2 / Real.log (k : ℝ)

/-- PDF p.3, (4): the specified vector in the fixed energy eigenbasis.
The theorem shifts the index to k+2 to remove the undefined printed k=1. -/
def exampleVector (k : ℕ) : Hilbert (ℕ × ℕ) :=
  (Real.sqrt (1 - exampleDelta k) : ℂ) • lp.single 2 (0, 0) 1 +
    (Real.sqrt (exampleDelta k / (k : ℝ)) : ℂ) •
      ∑ j ∈ Finset.range k, lp.single 2 (j + 1, j + 1) 1

/-- PDF pp.6--8: printed H^{tensor n}; changed to the additive n-copy Hamiltonian.
The energy n*M and the product Gibbs state used by the proof require the sum
of the single-copy Hamiltonians, not a product of their eigenvalues. -/
def copyLevelEnergy (h : HamiltonianData) (n : ℕ)
    (p : (Fin n → ℕ) × (Fin n → ℕ)) : ℝ :=
  ∑ t : Fin n, levelEnergy h (p.1 t, p.2 t)

/-- PDF pp.6--8: additive copy spectrum adapted to the frozen Hamiltonian;
its lower bound is n times the original finite ground energy. -/
def copySpectralHamiltonian (h : HamiltonianData) (n : ℕ) :
    QAlgorithms.Papers.Independent.Frontier18.P01.Hamiltonian
      ((Fin n → ℕ) × (Fin n → ℕ)) where
  energy := copyLevelEnergy h n
  lower := (n : ℝ) * levelEnergy h (0, 0)
  bounded_below := by
    intro p
    calc
      (n : ℝ) * levelEnergy h (0, 0) =
          ∑ _t : Fin n, levelEnergy h (0, 0) := by simp
      _ ≤ copyLevelEnergy h n p := by
        apply Finset.sum_le_sum
        intro t _ht
        exact add_le_add (h.orderedA (Nat.zero_le (p.1 t)))
          (h.orderedB (Nat.zero_le (p.2 t)))

/-- PDF pp.6--8: use frozen meanEnergy for the additive copy Hamiltonian.
The argument is a normalized state; divergent expectations remain infinity. -/
def copyMeanEnergy (h : HamiltonianData) (n : ℕ)
    (rho : State ((Fin n → ℕ) × (Fin n → ℕ))) : EReal :=
  (copySpectralHamiltonian h n).meanEnergy rho

/-- PDF p.6, Lemma 5: finite operator rank, without restriction to energy coordinates.
This is a finite sum of rank-one operators on the full one-system Hilbert space. -/
def FiniteRank {I : Type} (X : Matrix I I ℂ) : Prop :=
  ∃ (r : ℕ) (u v : Fin r → Hilbert I),
    ∀ i j, X i j = ∑ t : Fin r, u t i * star (v t j)

/-- PDF pp.6,10,12: printed finite-dimensional subspace of S(H); changed to
finite LOCAL support, equivalently finite Schmidt rank. The finite-dimensional
systems in the preamble and Lemma 5 applied to the A marginal pin this reading.
Global rank one would make the condition automatic; no energy-basis cutoff is used. -/
def FiniteSchmidtRank {I J : Type} (rho : PureState (I × J)) : Prop :=
  ∃ (u : Hilbert (I × J)), ‖u‖ = 1 ∧ rho.val.coefficients = rankOne u ∧
    ∃ (r : ℕ) (a : Fin r → Hilbert I) (b : Fin r → Hilbert J),
      ∀ i j, u (i, j) = ∑ t : Fin r, a t i * b t j

/-- PDF pp.8--9, (31)--(32): frozen countable trace-norm pure-state roof,
converted from nats to bits. Frozen Information100.P08.formation uses finite
ensembles on finite-dimensional spaces and cannot represent this domain.
No energy constraint on components or optimal decomposition is assumed. -/
def countableFormationBits {I J : Type} (X : Matrix (I × J) (I × J) ℂ) : ℝ≥0∞ :=
  QAlgorithms.Papers.Independent.Next46.P42.countableEof X /
    ENNReal.ofReal (Real.log 2)

/-- PDF p.11: both expressly allowed comparison sets. false selects the closed
convex hull D of products; true selects the trace-norm closure P of PPT states. -/
def ComparisonState {I J : Type} (ppt : Bool) (rho : State (I × J)) : Prop :=
  if ppt then rho.coefficients ∈ traceClosure
    {X : Matrix (I × J) (I × J) ℂ | IsDensity X ∧ IsDensity (partialTransposeFirst X)}
  else IsSeparable rho.coefficients

/-- PDF p.11, (45): infimum over ALL comparison states, without an energy bound.
The generalized relative entropy has the usual value on normalized states;
converting nats to bits preserves infinity and support failure. -/
def comparisonRelativeEntropyBits {I J : Type} (ppt : Bool)
    (X : Matrix (I × J) (I × J) ℂ) : ℝ≥0∞ :=
  ⨅ rho : {rho : State (I × J) // ComparisonState ppt rho},
    generalizedRelativeEntropy X rho.val.coefficients / ENNReal.ofReal (Real.log 2)

/-! Sanity checks pin signs, the inclusive diagonal-vector tail, and regrouping.
Tensor powers, partial transpose, entropy and countable decompositions are imported
from the pinned library rather than redeclared. -/

example : exampleDelta 2 = 1 := by
  simp [exampleDelta, (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne']

example : exampleVector 2 (1, 1) = (Real.sqrt (1 / 2) : ℂ) := by
  have htail :
      (∑ j ∈ Finset.range 2, lp.single 2 (j + 1, j + 1) (1 : ℂ) :
        Hilbert (ℕ × ℕ)) (1, 1) = 1 := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
    change ((Pi.single (1, 1) (1 : ℂ) : (ℕ × ℕ) → ℂ) (1, 1) +
      (Pi.single (2, 2) (1 : ℂ) : (ℕ × ℕ) → ℂ) (1, 1)) = 1
    simp
  change (Real.sqrt (1 - exampleDelta 2) : ℂ) *
      (lp.single 2 (0, 0) (1 : ℂ) : Hilbert (ℕ × ℕ)) (1, 1) +
    (Real.sqrt (exampleDelta 2 / (2 : ℝ)) : ℂ) *
      (∑ j ∈ Finset.range 2, lp.single 2 (j + 1, j + 1) (1 : ℂ) :
        Hilbert (ℕ × ℕ)) (1, 1) = (Real.sqrt (1 / 2) : ℂ)
  rw [htail]
  simp [exampleDelta, lp.single_apply,
    (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne']

example (h : HamiltonianData) : levelEnergy h (0, 0) = h.energyA 0 + h.energyB 0 := rfl

example (h : HamiltonianData) :
    (spectralHamiltonian h).lower = levelEnergy h (0, 0) := rfl

example (h : HamiltonianData) (n : ℕ) :
    (copySpectralHamiltonian h n).lower = (n : ℝ) * levelEnergy h (0, 0) := rfl

example (h : HamiltonianData) (n : ℕ)
    (rho : State ((Fin n → ℕ) × (Fin n → ℕ))) :
    copyMeanEnergy h n rho = (copySpectralHamiltonian h n).meanEnergy rho := rfl

example (h : HamiltonianData) (p : (Fin 0 → ℕ) × (Fin 0 → ℕ)) :
    copyLevelEnergy h 0 p = 0 := by simp [copyLevelEnergy]

example (h : HamiltonianData) (p : (Fin 1 → ℕ) × (Fin 1 → ℕ)) :
    copyLevelEnergy h 1 p = levelEnergy h (p.1 0, p.2 0) := by
  simp [copyLevelEnergy]

example {I : Type} (X : Matrix I I ℂ) (p q : Fin 1 → I) :
    tensorPower 1 X p q = X (p 0) (q 0) := by simp [tensorPower]

example {I J : Type} (X : Matrix (I × J) (I × J) ℂ) :
    partialTransposeFirst (partialTransposeFirst X) = X := rfl

example {I J : Type} (X : Matrix (I × J) (I × J) ℂ) (n : ℕ)
    (p q : (Fin n → I) × (Fin n → J)) :
    bipartitePower X n p q = tensorPower n X
      (fun t => (p.1 t, p.2 t)) (fun t => (q.1 t, q.2 t)) := rfl

end QAlgorithms.Papers.Independent.Gap20.P05


