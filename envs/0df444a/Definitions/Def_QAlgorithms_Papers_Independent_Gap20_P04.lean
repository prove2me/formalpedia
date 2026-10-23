-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Gap20_P04
-- name    : QAlgorithms_Papers_Independent_Gap20_P04
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-22T06:34:56.485764+00:00
-- url     : https://prove2.me/theorems/545c557d-00da-4224-913c-60ad831978f3
-- title:
--   Definitions for Trade-off capacities of the quantum Hadamard channels
-- statement:
--   The objects the formalized statements of *Trade-off capacities of the quantum Hadamard channels* (arXiv:1001.1732) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `product`: PDF pp.10,19: distinct channels; receiver and environment factors are regrouped.
--   - `PurifiedInputFamily`: PDF p.7, (15): arbitrary finite alphabet and reference; validity is separate.
--   - `PurifiedInputFamily.Valid`: PDF pp.3,7: normalized distribution; every conditional vector has norm one.
--   - `PurifiedInputFamily.input`: PDF p.7: input marginal of the conditional PURE reference-input state.
--   - `PurifiedInputFamily.average`: PDF pp.3--4: average input.
--   - `inputEntropy`: PDF p.4: H(A|X)=H(A'|X), by purity of each input.
--   - `ensembleReceiverEntropy`: PDF p.4: H(B).
--   - `conditionalReceiverEntropy`: PDF p.4: H(B|X).
--   - `conditionalEnvironmentEntropy`: PDF p.4: H(E|X), using the same isometry.
--   - `ensembleCoherentBits`: PDF pp.4,9: q=I(A>B X), using conditional ABE purity.
--   - `jointInfo`: PDF pp.4,8: j=I(AX;B), using conditional ABE purity.
--   - `cqScore`: PDF p.9, (21): CQ support objective.
--   - `ceScore`: PDF p.11, (23): CE support objective, with MINUS consumption.
--   - `purifiedValues`: PDF p.7, (15): physical ensembles only.
--   - `PureInputs`: PDF pp.10,20: pure channel-input ensembles in the Holevo maximum.
--   - `holevoValues`: PDF pp.10,20: one-use Holevo values, not regularized classical capacity.
--   - `RepeatedMax`: Positive-block homogeneity with attainment.
--   - `oneCQ`: PDF p.7: literal one-use CQ union, with ONE ensemble.
--   - `oneCE`: PDF p.8: CE rectangle union, E>=0 denotes consumption and may be wasted.
--   - `oneCQE`: PDF p.8, (17)--(19): all THREE inequalities use ONE ensemble.
--   - `capacityCQ`: PDF p.7, (14): closure OUTSIDE the positive-block union.
--   - `capacityCE`: PDF p.8, (16): unrestricted block-input CE region.
--   - `capacityCQE`: PDF p.8: regularized positive-consumption CQE region.
--   - `CQSupport`: PDF pp.9--11: full supporting CQ face, retaining optimizer ties.
--   - `CEUpper`: PDF pp.11,19: upper C at the given consumption budget, allowing flat portions.
--   - `cqHull`: PDF p.21: nonnegative resource-monotone CQ hull, with convex combinations and limits.
--   - `ceHull`: PDF pp.8,21: CE hull permits lowering C and increasing consumption E.
--   - `binaryEnsemble`: PDF pp.13,22: actual purifications with the specified swapped diagonal marginals.
--   - `binaryCQ`: PDF pp.12--13: CQ coordinates of the purified binary ensemble.
--   - `binaryCE`: PDF pp.15,23: CE coordinates of the same purified ensemble.
--   - `gdDilation`: PDF p.5, (10): generalized-dephasing parent isometry when each v_i is unit.
--   - `measureBasis`: PDF p.5: basis measurement, storing its classical outcome diagonally.
--   - `basisStatePreparation`: PDF p.5: basisStatePreparation the conditional environment state.
--   - `degradingKraus`: PDF p.5: rank-one degrading Kraus |xi_b><b|.
--   - `hadamardCoefficient`: PDF p.5, (9): explicit coefficient fixes the conjugations.
--   - `DephasedReplacement`: PDF pp.21,23: same probabilities, dephased INPUT marginals, NEW purifications.
--   - `dephasingCQ`: PDF p.12, Theorem 4: CQ generating family.
--   - `dephasingCE`: PDF p.12, Theorem 4: CE generating family.
--   - `cloneDelta`: PDF pp.6,12: normalization, in real arithmetic.
--   - `cloneLambda`: PDF p.12: lambda_i for i=0,...,N; subtraction is in reals.
--   - `cloneEta`: PDF p.12: eta_i for i=0,...,N-1; subtraction is in reals.
--   - `entropyVector`: PDF p.12: finite Shannon entropy, bits; 0 log 0=0.
--   - `cloningCQ`: PDF p.12, Theorem 5: cloning CQ coordinates.
--   - `cloningCE`: PDF p.12, Theorem 5: cloning CE coordinates.
--   - `CESupport`: PDF pp.11,21: CE supporting face, distinct from choosing one optimizer.
--   - `selectedCQHull`: PDF p.21: CQ hull from one selection per support face and the resource endpoints. Endpoints are represented by their full axis intervals; resource monotonicity is explicit.
--   - `selectedCEHull`: PDF p.21: CE selection hull, including the zero-consumption endpoint and limits.
-- source:
--   Trade-off capacities of the quantum Hadamard channels, arXiv:1001.1732v2, https://arxiv.org/abs/1001.1732v2

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Ensemble
import Definitions.Def_QAlgorithms_Defs_Channel
import Definitions.Def_QAlgorithms_Defs_BipartiteSeparability
import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P24
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P67
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P32
import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P44
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P24

/-!
Bradler--Hayden--Touchette--Wilde, arXiv:1001.1732v2, statement draft.
Entropies are bits; E>=0 is consumption. Capacity sets are the source's
regularized entropy-region definitions (14)--(19), whose operational meaning
is recalled in Section III. No signed-rate region or Unruh cutoff is substituted.
-/

noncomputable section

namespace QAlgorithms.Papers.Independent.Gap20.P04

open QAlgorithms
open QAlgorithms.Papers.Independent.Claimed50.P24
  (Dilation PhysicalDilation ChannelEB Hadamard EqualMax AdditiveMax
   dephasingDilation dephasingGamma cloningDilation)
open QAlgorithms.Papers.Independent.Information100.P67
  (receiverChannel complementaryChannel dilationPower)
open QAlgorithms.Papers.Independent.Information100.P32 (diagonal)
open QAlgorithms.Papers.Independent.Dependency50.P24 (ensembleHolevoBits)
open QAlgorithms.Papers.Independent.Gap48.P44 (cqTimeSharing ceTimeSharing)
open scoped BigOperators Matrix ComplexConjugate

attribute [local instance] Classical.propDecidable Classical.decEq

/-!
Repair provenance: frozen Stinespring primitives, Hadamard/EB predicates,
attained-maximum relations, explicit qubit dilations, diagonal map and endpoint
time sharing are imported from the pinned accepted library. No signed-rate
capacity theorem is imported or asserted equivalent to the consumption theorem.

The remaining distinctly named interfaces have different domains from their
frozen namesakes: PurifiedInputFamily stores arbitrary finite reference-input
unit vectors with validity separate, whereas Information100.P58.InputEnsemble
stores mixed erasure-block inputs. ensembleReceiverEntropy is finite base-two
matrix entropy, not Information100.P49.outputEntropy's Gaussian scalar formula;
conditionalReceiverEntropy accepts those purified inputs rather than a
multi-sender product law. The Holevo coordinate reuses Dependency50.P24.ensembleHolevoBits
on the probabilities and conditional receiver densities. ensembleCoherentBits is
a real entropy coordinate, unlike the frozen Hamiltonian commutator coherent.
purifiedValues ranges over this raw family's Valid members, not P24's mixed
two-label ensembles. basisStatePreparation is the linear basis-controlled
preparation map, not Frontier30.P06.FeedbackExecution.prepare's next-input encoding.
-/

variable {I B E J D F : Type}
variable [Fintype I] [Fintype B] [Fintype E]
variable [Fintype J] [Fintype D] [Fintype F]
variable [DecidableEq I] [DecidableEq B] [DecidableEq E]
variable [DecidableEq J] [DecidableEq D] [DecidableEq F]
variable [Nonempty I] [Nonempty B] [Nonempty E]
variable [Nonempty J] [Nonempty D] [Nonempty F]

/-- PDF pp.10,19: distinct channels; receiver and environment factors are regrouped. -/
def product (U : Dilation I B E) (V : Dilation J D F) :
    Dilation (I × J) (B × D) (E × F) :=
  fun be i => U (be.1.1,be.2.1) i.1 * V (be.1.2,be.2.2) i.2

/-- PDF p.7, (15): arbitrary finite alphabet and reference; validity is separate. -/
structure PurifiedInputFamily (I : Type) where
  labels : ℕ
  reference : ℕ
  prob : Fin labels → ℝ
  psi : Fin labels → EuclideanSpace ℂ (Fin reference × I)

/-- PDF pp.3,7: normalized distribution; every conditional vector has norm one. -/
def PurifiedInputFamily.Valid (e : PurifiedInputFamily I) : Prop :=
  0 < e.labels ∧ 0 < e.reference ∧ (∀ x, 0 ≤ e.prob x) ∧
    (∑ x, e.prob x) = 1 ∧ ∀ x, ‖e.psi x‖ = 1

/-- PDF p.7: input marginal of the conditional PURE reference-input state. -/
def PurifiedInputFamily.input (e : PurifiedInputFamily I) (x : Fin e.labels) : Matrix I I ℂ :=
  traceLeft (pureDensity (e.psi x))

/-- PDF pp.3--4: average input. -/
def PurifiedInputFamily.average (e : PurifiedInputFamily I) : Matrix I I ℂ :=
  ∑ x, (e.prob x : ℂ) • e.input x

/-- PDF p.4: H(A|X)=H(A'|X), by purity of each input. -/
def inputEntropy (e : PurifiedInputFamily I) : ℝ :=
  ∑ x, e.prob x * vnEntropy (e.input x)

/-- PDF p.4: H(B). -/
def ensembleReceiverEntropy (U : Dilation I B E) (e : PurifiedInputFamily I) : ℝ :=
  vnEntropy (receiverChannel U e.average)

/-- PDF p.4: H(B|X). -/
def conditionalReceiverEntropy (U : Dilation I B E) (e : PurifiedInputFamily I) : ℝ :=
  ∑ x, e.prob x * vnEntropy (receiverChannel U (e.input x))

/-- PDF p.4: H(E|X), using the same isometry. -/
def conditionalEnvironmentEntropy (U : Dilation I B E) (e : PurifiedInputFamily I) : ℝ :=
  ∑ x, e.prob x * vnEntropy (complementaryChannel U (e.input x))

/-- PDF pp.4,9: q=I(A>B X), using conditional ABE purity. -/
def ensembleCoherentBits (U : Dilation I B E) (e : PurifiedInputFamily I) : ℝ :=
  conditionalReceiverEntropy U e - conditionalEnvironmentEntropy U e

/-- PDF pp.4,8: j=I(AX;B), using conditional ABE purity. -/
def jointInfo (U : Dilation I B E) (e : PurifiedInputFamily I) : ℝ :=
  inputEntropy e + ensembleReceiverEntropy U e - conditionalEnvironmentEntropy U e

/-- PDF p.9, (21): CQ support objective. -/
def cqScore (U : Dilation I B E) (lam : ℝ) (e : PurifiedInputFamily I) : ℝ :=
  ensembleHolevoBits e.prob (fun x => receiverChannel U (e.input x)) + lam * ensembleCoherentBits U e

/-- PDF p.11, (23): CE support objective, with MINUS consumption. -/
def ceScore (U : Dilation I B E) (lam : ℝ) (e : PurifiedInputFamily I) : ℝ :=
  jointInfo U e - lam * inputEntropy e

/-- PDF p.7, (15): physical ensembles only. -/
def purifiedValues (f : PurifiedInputFamily I → ℝ) : Set ℝ :=
  {v | ∃ e, e.Valid ∧ v = f e}

/-- PDF pp.10,20: pure channel-input ensembles in the Holevo maximum. -/
def PureInputs (e : PurifiedInputFamily I) : Prop :=
  ∀ x, ∃ v : EuclideanSpace ℂ I, ‖v‖ = 1 ∧ e.input x = pureDensity v

/-- PDF pp.10,20: one-use Holevo values, not regularized classical capacity. -/
def holevoValues (U : Dilation I B E) : Set ℝ :=
  {v | ∃ e, e.Valid ∧ PureInputs e ∧ v = ensembleHolevoBits e.prob (fun x => receiverChannel U (e.input x))}

/-- Positive-block homogeneity with attainment. -/
def RepeatedMax (n : ℕ) (S T : Set ℝ) : Prop :=
  ∃ v, IsGreatest S v ∧ IsGreatest T ((n : ℝ)*v)

/-- PDF p.7: literal one-use CQ union, with ONE ensemble. -/
def oneCQ (U : Dilation I B E) : Set (ℝ × ℝ) :=
  {r | 0 ≤ r.1 ∧ 0 ≤ r.2 ∧ ∃ e, e.Valid ∧ r.1 ≤ ensembleHolevoBits e.prob (fun x => receiverChannel U (e.input x)) ∧ r.2 ≤ ensembleCoherentBits U e}

/-- PDF p.8: CE rectangle union, E>=0 denotes consumption and may be wasted. -/
def oneCE (U : Dilation I B E) : Set (ℝ × ℝ) :=
  {r | 0 ≤ r.1 ∧ 0 ≤ r.2 ∧ ∃ e, e.Valid ∧ r.1 ≤ jointInfo U e ∧ inputEntropy e ≤ r.2}

/-- PDF p.8, (17)--(19): all THREE inequalities use ONE ensemble. -/
def oneCQE (U : Dilation I B E) : Set (Fin 3 → ℝ) :=
  {r | (∀ i, 0 ≤ r i) ∧ ∃ e, e.Valid ∧
    r 0 + 2*r 1 ≤ jointInfo U e ∧ r 1 ≤ ensembleCoherentBits U e + r 2 ∧
      r 0 + r 1 ≤ ensembleHolevoBits e.prob (fun x => receiverChannel U (e.input x)) + ensembleCoherentBits U e + r 2}

/-- PDF p.7, (14): closure OUTSIDE the positive-block union. -/
def capacityCQ (U : Dilation I B E) : Set (ℝ × ℝ) :=
  closure {r | ∃ n : ℕ, 0 < n ∧ (n : ℝ) • r ∈ oneCQ (dilationPower U n)}

/-- PDF p.8, (16): unrestricted block-input CE region. -/
def capacityCE (U : Dilation I B E) : Set (ℝ × ℝ) :=
  closure {r | ∃ n : ℕ, 0 < n ∧ (n : ℝ) • r ∈ oneCE (dilationPower U n)}

/-- PDF p.8: regularized positive-consumption CQE region. -/
def capacityCQE (U : Dilation I B E) : Set (Fin 3 → ℝ) :=
  closure {r | ∃ n : ℕ, 0 < n ∧ (n : ℝ) • r ∈ oneCQE (dilationPower U n)}

/-- PDF pp.9--11: full supporting CQ face, retaining optimizer ties. -/
def CQSupport (S : Set (ℝ × ℝ)) (lam : ℝ) (r : ℝ × ℝ) : Prop :=
  r ∈ S ∧ ∀ s ∈ S, s.1 + lam*s.2 ≤ r.1 + lam*r.2

/-- PDF pp.11,19: upper C at the given consumption budget, allowing flat portions. -/
def CEUpper (S : Set (ℝ × ℝ)) (r : ℝ × ℝ) : Prop :=
  r ∈ S ∧ ∀ s ∈ S, s.2 ≤ r.2 → s.1 ≤ r.1

/-- PDF p.21: nonnegative resource-monotone CQ hull, with convex combinations and limits. -/
def cqHull (f : ℝ → ℝ × ℝ) : Set (ℝ × ℝ) :=
  closure (convexHull ℝ {r | 0 ≤ r.1 ∧ 0 ≤ r.2 ∧
    ∃ mu ∈ Set.Icc (0 : ℝ) (1/2), r.1 ≤ (f mu).1 ∧ r.2 ≤ (f mu).2})

/-- PDF pp.8,21: CE hull permits lowering C and increasing consumption E. -/
def ceHull (f : ℝ → ℝ × ℝ) : Set (ℝ × ℝ) :=
  closure (convexHull ℝ {r | 0 ≤ r.1 ∧ 0 ≤ r.2 ∧
    ∃ mu ∈ Set.Icc (0 : ℝ) (1/2), r.1 ≤ (f mu).1 ∧ (f mu).2 ≤ r.2})

/-- PDF pp.13,22: actual purifications with the specified swapped diagonal marginals. -/
def binaryEnsemble (mu : ℝ) : PurifiedInputFamily (Fin 2) where
  labels := 2
  reference := 2
  prob := fun _ => 1/2
  psi := fun x => WithLp.toLp 2 fun ai =>
    if ai.1 = ai.2 then
      if ai.2 = x then (Real.sqrt mu : ℂ) else (Real.sqrt (1-mu) : ℂ)
    else 0

/-- PDF pp.12--13: CQ coordinates of the purified binary ensemble. -/
def binaryCQ (U : Dilation (Fin 2) B E) (mu : ℝ) : ℝ × ℝ :=
  (ensembleHolevoBits (binaryEnsemble mu).prob
    (fun x => receiverChannel U ((binaryEnsemble mu).input x)), ensembleCoherentBits U (binaryEnsemble mu))

/-- PDF pp.15,23: CE coordinates of the same purified ensemble. -/
def binaryCE (U : Dilation (Fin 2) B E) (mu : ℝ) : ℝ × ℝ :=
  (jointInfo U (binaryEnsemble mu), inputEntropy (binaryEnsemble mu))

/-- PDF p.5, (10): generalized-dephasing parent isometry when each v_i is unit. -/
def gdDilation (v : I → EuclideanSpace ℂ E) : Dilation I I E :=
  fun be i => if be.1 = i then v i be.2 else 0

/-- PDF p.5: basis measurement, storing its classical outcome diagonally. -/
def measureBasis : Superop B B := diagonal

/-- PDF p.5: basisStatePreparation the conditional environment state. -/
def basisStatePreparation (v : B → EuclideanSpace ℂ E) : Superop B E :=
  fun rho => ∑ b, rho b b • pureDensity (v b)

/-- PDF p.5: rank-one degrading Kraus |xi_b><b|. -/
def degradingKraus (v : B → EuclideanSpace ℂ E) (b : B) : Matrix E B ℂ :=
  fun e c => if c = b then v b e else 0

/-- PDF p.5, (9): explicit coefficient fixes the conjugations. -/
def hadamardCoefficient (zeta : B → EuclideanSpace ℂ I)
    (xi : B → EuclideanSpace ℂ E) (rho : Matrix I I ℂ) : Matrix B B ℂ :=
  fun b c => (∑ i, ∑ j, conj (zeta b i) * rho i j * zeta c j) *
    (∑ e, conj (xi c e) * xi b e)

/-- PDF pp.21,23: same probabilities, dephased INPUT marginals, NEW purifications. -/
def DephasedReplacement (e t : PurifiedInputFamily I) : Prop :=
  ∃ f : Fin e.labels ≃ Fin t.labels, ∀ x,
    t.prob (f x) = e.prob x ∧ t.input (f x) = diagonal (e.input x)

/-- PDF p.12, Theorem 4: CQ generating family. -/
def dephasingCQ (p mu : ℝ) : ℝ × ℝ :=
  (1-binEntropy2 mu, binEntropy2 mu-binEntropy2 (dephasingGamma mu p))

/-- PDF p.12, Theorem 4: CE generating family. -/
def dephasingCE (p mu : ℝ) : ℝ × ℝ :=
  (1+binEntropy2 mu-binEntropy2 (dephasingGamma mu p), binEntropy2 mu)

/-- PDF pp.6,12: normalization, in real arithmetic. -/
def cloneDelta (N : ℕ) : ℝ := (N : ℝ)*((N : ℝ)+1)/2

/-- PDF p.12: lambda_i for i=0,...,N; subtraction is in reals. -/
def cloneLambda (N : ℕ) (mu : ℝ) (i : Fin (N+1)) : ℝ :=
  ((N : ℝ)-2*(i.val : ℝ))*mu+(i.val : ℝ)

/-- PDF p.12: eta_i for i=0,...,N-1; subtraction is in reals. -/
def cloneEta (N : ℕ) (mu : ℝ) (i : Fin N) : ℝ :=
  ((N : ℝ)-1-2*(i.val : ℝ))*mu+(i.val : ℝ)+1

/-- PDF p.12: finite Shannon entropy, bits; 0 log 0=0. -/
def entropyVector {K : Type} [Fintype K] (p : K → ℝ) : ℝ :=
  -∑ i, p i * Real.logb 2 (p i)

/-- PDF p.12, Theorem 5: cloning CQ coordinates. -/
def cloningCQ (N : ℕ) (mu : ℝ) : ℝ × ℝ :=
  let hb := entropyVector (fun i => cloneLambda N mu i / cloneDelta N)
  let he := entropyVector (fun i => cloneEta N mu i / cloneDelta N)
  (Real.logb 2 ((N : ℝ)+1)-hb, hb-he)

/-- PDF p.12, Theorem 5: cloning CE coordinates. -/
def cloningCE (N : ℕ) (mu : ℝ) : ℝ × ℝ :=
  (Real.logb 2 ((N : ℝ)+1)+binEntropy2 mu-
    entropyVector (fun i => cloneEta N mu i / cloneDelta N), binEntropy2 mu)

/-- PDF pp.11,21: CE supporting face, distinct from choosing one optimizer. -/
def CESupport (S : Set (ℝ × ℝ)) (lam : ℝ) (r : ℝ × ℝ) : Prop :=
  r ∈ S ∧ ∀ s ∈ S, s.1-lam*s.2 ≤ r.1-lam*r.2

/-- PDF p.21: CQ hull from one selection per support face and the resource endpoints.
Endpoints are represented by their full axis intervals; resource monotonicity is explicit. -/
def selectedCQHull (S : Set (ℝ × ℝ)) (f : ℝ → ℝ × ℝ) : Set (ℝ × ℝ) :=
  closure (convexHull ℝ {r | 0 ≤ r.1 ∧ 0 ≤ r.2 ∧ ∃ s : ℝ × ℝ,
    ((∃ lam : ℝ, 1 ≤ lam ∧ s = f lam) ∨ (s ∈ S ∧ (s.1 = 0 ∨ s.2 = 0))) ∧
    r.1 ≤ s.1 ∧ r.2 ≤ s.2})

/-- PDF p.21: CE selection hull, including the zero-consumption endpoint and limits. -/
def selectedCEHull (S : Set (ℝ × ℝ)) (f : ℝ → ℝ × ℝ) : Set (ℝ × ℝ) :=
  closure (convexHull ℝ {r | 0 ≤ r.1 ∧ 0 ≤ r.2 ∧ ∃ s : ℝ × ℝ,
    ((∃ lam ∈ Set.Icc (0 : ℝ) 1, s = f lam) ∨ (s ∈ S ∧ s.2 = 0)) ∧
    r.1 ≤ s.1 ∧ s.2 ≤ r.2})

/-! Sanity tests for the local definitions. -/

example : cloneDelta 1 = 1 := by norm_num [cloneDelta]

example (mu : ℝ) : cloneEta 1 mu (0 : Fin 1) = 1 := by simp [cloneEta]

example (rho : Matrix I I ℂ) : diagonal (diagonal rho) = diagonal rho := by
  ext i j
  simp [diagonal]

example : dephasingGamma 0 0 = 1 := by norm_num [dephasingGamma]

example : (binaryEnsemble 0).psi (0 : Fin 2) ((1 : Fin 2), (1 : Fin 2)) = 1 := by
  change (if (1 : Fin 2) = 1 then
    if (1 : Fin 2) = 0 then (Real.sqrt (0 : ℝ) : ℂ)
    else (Real.sqrt (1 - (0 : ℝ)) : ℂ)
    else 0) = 1
  norm_num

example (U : Dilation I B E) : cqScore U 0 =
    (fun e => ensembleHolevoBits e.prob (fun x => receiverChannel U (e.input x))) := by
  funext e
  simp [cqScore]

end QAlgorithms.Papers.Independent.Gap20.P04


