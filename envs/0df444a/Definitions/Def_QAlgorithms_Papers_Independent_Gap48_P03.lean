-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P03
-- name    : QAlgorithms_Papers_Independent_Gap48_P03
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-21T20:51:16.798987+00:00
-- url     : https://prove2.me/theorems/5c549424-2bcc-4707-865e-b93478250a75
-- title:
--   Definitions for The capacity of the quantum depolarizing channel
-- statement:
--   The objects the formalized statements of *The capacity of the quantum depolarizing channel* (arXiv:quant-ph/0204172) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `productChannel`: PDF pp.3,18: tensor action on all operators, including entangled states; companion input and output dimensions may differ.
--   - `maximumOutputPNorm`: PDF p.3, (6): real-p output norm supremum over density matrices. For finite nonempty CPTP maps and p>=1 the set is nonempty and bounded by 1.
--   - `holevoScore`: PDF p.3, (8): Holevo score of an actual finite normalized ensemble, in nats.
--   - `holevoQuantity`: PDF p.3, (8): unregularized Holevo supremum. On finite nonempty CPTP maps its value set is nonempty and bounded above by log(dim output).
--   - `measuredInformation`: PDF pp.5-6, (14)-(16): mutual information of the actual ensemble/POVM joint law, converted from the accepted bit-valued primitive to nats.
--   - `quantumShannonCapacity`: PDF p.6, (16): optimize all finite ensembles and all finite output POVMs. On finite nonempty CPTP maps its value set is nonempty and bounded by log(dim output).
--   - `shannonBlockRate`: PDF p.6, (19): actual n-use Shannon capacity per use; the unused n=0 value is 0.
--   - `ultimateClassicalCapacity`: PDF p.6, (19): ordinary Shannon block limit, never defined to be a Holevo quantity. Theorem 1 explicitly asserts convergence and excludes the off-domain default.
--   - `depolarizingEntropy`: PDF p.4, (9): explicit minimum entropy, with 0 log 0=0.
--   - `depolarizingNormFactor`: PDF p.4, (10): explicit spectral factor, also used on the larger phase interval. There the raw depolarizing map need not be CPTP.
--   - `basisProjector`: PDF pp.4,9: rank-one projector from the actual column vector.
--   - `basisProb`: PDF p.4: the uniform basis probabilities; theorem dimensions are positive.
--   - `productBasisProjector`: PDF pp.1,7: products of basis projectors, used for encoding and measurement.
--   - `productBasisProb`: PDF pp.1,7: uniform independent basis input law at block length n.
--   - `productBasisInformation`: PDF pp.1,7: mutual information of this concrete product basis strategy.
--   - `IsUniformVector`: PDF p.9, Definition 5: equal coordinate magnitudes, without normalization.
--   - `IsUniformBasis`: PDF p.10, Definition 6: every column of the specified basis is uniform. Orthonormality is supplied separately, not built into the uniform-vector predicate.
--   - `phaseChannel`: PDF p.9, (27): transport the frozen bipartite phase-damping action along Fin d x Fin 1 = Fin d. Its accepted noise parameter is 1-lambda.
--   - `intermediateChannel`: PDF pp.12-13, (45): intermediate map with trace-linear depolarizing extension.
--   - `clockUnitary`: PDF p.13, (47)-(48): one-based diagonal clock matrix G.
--   - `quadraticPhaseUnitary`: PDF p.13, (51)-(52): one-based quadratic phase matrix H, denominator 2d^2.
--   - `constructedUniformBasis`: PDF p.14, (54): column k is G^(k+1) H^a theta, with the accepted uniform state. The source index a is one-based; finite sums below pass a.val+1.
--   - `constructedPhaseDamping`: PDF p.14, (56): the concrete constructed family, not a replacement basis.
--   - `qubitPauli`: PDF p.17: reindex accepted Pauli matrices from false,true to 0,1.
--   - `qubitTau`: PDF p.17, (81): tau, with opposite off-diagonal phases.
--   - `qubitTauConjugate`: PDF p.17, (81): entrywise conjugate of tau, not adjoint.
-- source:
--   The capacity of the quantum depolarizing channel, arXiv:quant-ph/0204172v2, https://arxiv.org/abs/quant-ph/0204172v2

import Mathlib
import Definitions.Def_QAlgorithms_Defs_ExtendedQuantumEntropy
import Definitions.Def_QAlgorithms_Defs_QuditChannelFidelities
import Definitions.Def_QAlgorithms_Defs_QuantumInformation
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P08
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P56
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P63
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P67
import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P43
import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P42

/-!
King, quant-ph/0204172v2. References are PDF pages; information units are nats.
Only pinned accepted libraries are imported, with no other chunk of this run.
All local definitions have complete bodies. Source theorem proofs are omitted.
-/

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder ENNReal
open Filter

namespace QAlgorithms.Papers.Independent.Gap48.P03

open QAlgorithms.Papers.Independent.Information100.P08 (Ensemble ensembleAverage depolarizing)
open QAlgorithms.Papers.Independent.Information100.P56 (entropy holevo IsLaw)
open QAlgorithms.Papers.Independent.Information100.P63 (schatten block)
open QAlgorithms.Papers.Independent.Information100.P67 (mapFirst)
open QAlgorithms.Papers.Independent.Claimed50.P43 (ordinaryLimit)
open QAlgorithms.Papers.Independent.Next46.P42 (minimumOutputEntropy)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF pp.3,18: tensor action on all operators, including entangled states;
companion input and output dimensions may differ. -/
def productChannel {A B C D : Type} [Fintype A] [Fintype B]
    [Fintype C] [Fintype D] [DecidableEq A] [DecidableEq B]
    [DecidableEq C] [DecidableEq D] (N : Superop A B) (M : Superop C D) :
    Superop (A × C) (B × D) :=
  fun rho => mapFirst N (idTensorSuperop M rho)

/-- PDF p.3, (6): real-p output norm supremum over density matrices.
For finite nonempty CPTP maps and p>=1 the set is nonempty and bounded by 1. -/
def maximumOutputPNorm {A B : Type} [Fintype A] [Fintype B] [DecidableEq B]
    (N : Superop A B) (p : ℝ) : ℝ :=
  sSup {s | ∃ rho : Matrix A A ℂ, IsDensityMatrix rho ∧ s = schatten p (N rho)}

/-- PDF p.3, (8): Holevo score of an actual finite normalized ensemble, in nats. -/
def holevoScore {A B : Type} [Fintype A] [Fintype B] [DecidableEq B]
    (N : Superop A B) (e : Ensemble A) : ℝ :=
  holevo e.prob (fun i => N (e.state i))

/-- PDF p.3, (8): unregularized Holevo supremum. On finite nonempty CPTP maps
its value set is nonempty and bounded above by log(dim output). -/
def holevoQuantity {A B : Type} [Fintype A] [Fintype B] [DecidableEq B]
    (N : Superop A B) : ℝ :=
  sSup {s | ∃ e : Ensemble A, s = holevoScore N e}

/-- PDF pp.5-6, (14)-(16): mutual information of the actual ensemble/POVM joint law,
converted from the accepted bit-valued primitive to nats. -/
def measuredInformation {A B X Y : Type} [Fintype A] [Fintype B]
    [Fintype X] [Fintype Y] (N : Superop A B) (prob : X → ℝ)
    (rho : X → Matrix A A ℂ) (M : Y → Matrix B B ℂ) : ℝ :=
  Real.log 2 * mutualInfoBits (fun xy => prob xy.1 * effectProb (M xy.2) (N (rho xy.1)))

/-- PDF p.6, (16): optimize all finite ensembles and all finite output POVMs.
On finite nonempty CPTP maps its value set is nonempty and bounded by log(dim output). -/
def quantumShannonCapacity {A B : Type} [Fintype A] [Fintype B] [DecidableEq B]
    (N : Superop A B) : ℝ :=
  sSup {s | ∃ (e : Ensemble A) (k : ℕ) (M : Fin k → Matrix B B ℂ),
    IsPOVM M ∧ s = measuredInformation N e.prob e.state M}

/-- PDF p.6, (19): actual n-use Shannon capacity per use; the unused n=0 value is 0. -/
def shannonBlockRate {A B : Type} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] (N : Superop A B) (n : ℕ) : ℝ :=
  quantumShannonCapacity (piSuperop (fun _ : Fin n => N)) / n

/-- PDF p.6, (19): ordinary Shannon block limit, never defined to be a Holevo quantity.
Theorem 1 explicitly asserts convergence and excludes the off-domain default. -/
def ultimateClassicalCapacity {A B : Type} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] (N : Superop A B) : ℝ :=
  ordinaryLimit (shannonBlockRate N)

/-- PDF p.4, (9): explicit minimum entropy, with 0 log 0=0. -/
def depolarizingEntropy (d : ℕ) (lam : ℝ) : ℝ :=
  let a : ℝ := lam + (1 - lam) / d;
  let b : ℝ := (1 - lam) / d;
  -a * Real.log a - ((d : ℝ) - 1) * b * Real.log b

/-- PDF p.4, (10): explicit spectral factor, also used on the larger phase interval.
There the raw depolarizing map need not be CPTP. -/
def depolarizingNormFactor (d : ℕ) (lam p : ℝ) : ℝ :=
  ((lam + (1 - lam) / d) ^ p + ((d : ℝ) - 1) * ((1 - lam) / d) ^ p) ^ (1 / p)

/-- PDF pp.4,9: rank-one projector from the actual column vector. -/
def basisProjector {d : ℕ} (B : Matrix (Fin d) (Fin d) ℂ) (k : Fin d) :
    Matrix (Fin d) (Fin d) ℂ :=
  pureDensity (act B (ket k))

/-- PDF p.4: the uniform basis probabilities; theorem dimensions are positive. -/
def basisProb (d : ℕ) : Fin d → ℝ := fun _ => (d : ℝ)⁻¹

/-- PDF pp.1,7: products of basis projectors, used for encoding and measurement. -/
def productBasisProjector {d : ℕ} (B : Matrix (Fin d) (Fin d) ℂ) (n : ℕ)
    (x : Fin n → Fin d) : Matrix (Fin n → Fin d) (Fin n → Fin d) ℂ :=
  fun y z => ∏ t, basisProjector B (x t) (y t) (z t)

/-- PDF pp.1,7: uniform independent basis input law at block length n. -/
def productBasisProb (d n : ℕ) : (Fin n → Fin d) → ℝ :=
  fun _ => ((d : ℝ) ^ n)⁻¹

/-- PDF pp.1,7: mutual information of this concrete product basis strategy. -/
def productBasisInformation {d : ℕ} (N : Superop (Fin d) (Fin d))
    (B : Matrix (Fin d) (Fin d) ℂ) (n : ℕ) : ℝ :=
  measuredInformation (piSuperop (fun _ : Fin n => N))
    (productBasisProb d n) (productBasisProjector B n) (productBasisProjector B n)

/-- PDF p.9, Definition 5: equal coordinate magnitudes, without normalization. -/
def IsUniformVector {d : ℕ} (v : EuclideanSpace ℂ (Fin d)) : Prop :=
  ∀ i j, ‖v i‖ = ‖v j‖

/-- PDF p.10, Definition 6: every column of the specified basis is uniform.
Orthonormality is supplied separately, not built into the uniform-vector predicate. -/
def IsUniformBasis {d : ℕ} (B : Matrix (Fin d) (Fin d) ℂ) : Prop :=
  ∀ k, IsUniformVector (act B (ket k))

/-- PDF p.9, (27): transport the frozen bipartite phase-damping action along
Fin d x Fin 1 = Fin d. Its accepted noise parameter is 1-lambda. -/
def phaseChannel {d : ℕ} (B : Matrix (Fin d) (Fin d) ℂ) (lam : ℝ) :
    Superop (Fin d) (Fin d) :=
  fun X i j => QAlgorithms.Papers.Independent.Information100.P63.phaseDamping
    (1 - lam) B (fun a b : Fin d × Fin 1 => X a.1 b.1) (i, 0) (j, 0)

/-- PDF pp.12-13, (45): intermediate map with trace-linear depolarizing extension. -/
def intermediateChannel (d : ℕ) [NeZero d] (lam : ℝ) : Superop (Fin d) (Fin d) :=
  fun X => depolarizing d (1 - lam) X + (((1 - lam) / d : ℝ) : ℂ) •
    (X - Matrix.diagonal (fun i => X i i))

/-- PDF p.13, (47)-(48): one-based diagonal clock matrix G. -/
def clockUnitary (d : ℕ) : Matrix (Fin d) (Fin d) ℂ :=
  Matrix.diagonal (fun k => Complex.exp
    (2 * (Real.pi : ℂ) * Complex.I * ((k.val + 1 : ℕ) : ℂ) / (d : ℂ)))

/-- PDF p.13, (51)-(52): one-based quadratic phase matrix H, denominator 2d^2. -/
def quadraticPhaseUnitary (d : ℕ) : Matrix (Fin d) (Fin d) ℂ :=
  Matrix.diagonal (fun k => Complex.exp
    (2 * (Real.pi : ℂ) * Complex.I * (((k.val + 1 : ℕ) : ℂ) ^ 2) /
      (2 * (d : ℂ) ^ 2)))

/-- PDF p.14, (54): column k is G^(k+1) H^a theta, with the accepted uniform state.
The source index a is one-based; finite sums below pass a.val+1. -/
def constructedUniformBasis (d a : ℕ) : Matrix (Fin d) (Fin d) ℂ :=
  fun i k => act (clockUnitary d ^ (k.val + 1) * quadraticPhaseUnitary d ^ a)
    (uniformState (Fin d)) i

/-- PDF p.14, (56): the concrete constructed family, not a replacement basis. -/
def constructedPhaseDamping (d : ℕ) (lam : ℝ) (a : ℕ) : Superop (Fin d) (Fin d) :=
  phaseChannel (constructedUniformBasis d a) lam

/-- PDF p.17: reindex accepted Pauli matrices from false,true to 0,1. -/
def qubitPauli (P : Matrix Bool Bool ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  P.submatrix (fun i => decide (i.val = 1)) (fun i => decide (i.val = 1))

/-- PDF p.17, (81): tau, with opposite off-diagonal phases. -/
def qubitTau : Matrix (Fin 2) (Fin 2) ℂ :=
  !![0, Complex.exp ((Real.pi : ℂ) * Complex.I / 4);
     Complex.exp (-(Real.pi : ℂ) * Complex.I / 4), 0]

/-- PDF p.17, (81): entrywise conjugate of tau, not adjoint. -/
def qubitTauConjugate : Matrix (Fin 2) (Fin 2) ℂ :=
  qubitTau.map conj

/-! Sanity examples, with proofs only for definitions, not source results. -/

example (d : ℕ) [NeZero d] (X : Matrix (Fin d) (Fin d) ℂ) :
    depolarizing d 0 X = X := by
  simp [depolarizing]

example {A B : Type} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (N : Superop A B) : shannonBlockRate N 0 = 0 := by
  simp [shannonBlockRate]

example {d : ℕ} (B : Matrix (Fin d) (Fin d) ℂ) (X : Matrix (Fin d) (Fin d) ℂ) :
    phaseChannel B 1 X = X := by
  funext i j
  change (((1 - (1 - (1 : ℝ)) : ℝ) : ℂ) * X i j +
    ((1 - (1 : ℝ) : ℝ) : ℂ) * _) = X i j
  simp

example {d : ℕ} : IsUniformVector (0 : EuclideanSpace ℂ (Fin d)) := by
  intro i j
  simp

example {d m : ℕ} (B : Matrix (Fin d) (Fin d) ℂ) (i : Fin d) :
    block B (0 : Matrix (Fin d × Fin m) (Fin d × Fin m) ℂ) i i = 0 := by
  ext a b
  simp [block]

example : depolarizingEntropy 2 1 = 0 := by
  norm_num [depolarizingEntropy]

example : qubitTauConjugate 0 1 = conj (qubitTau 0 1) := rfl

end QAlgorithms.Papers.Independent.Gap48.P03


