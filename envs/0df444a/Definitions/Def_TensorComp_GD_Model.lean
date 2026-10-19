-- Prove2me | Definitions.Def_TensorComp_GD_Model
-- name    : TensorComp_GD_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-19T04:16:47.202993+00:00
-- url     : https://prove2.me/theorems/583eecdb-6b65-4450-b483-a82b39bb3997
-- title:
--   §1.1–§3 and (20)–(23): symmetric noisy tensor model, loss, spectral initialization, factor retrieval, and gradient descent
-- statement:
--   This module represents the symmetric rank-$r$ tensor completion problem of Cai, Li, Poor and Chen. A factor matrix $U\in\mathbb R^{d\times r}$ determines the order-three tensor
--   $$T(U)_{ijk}=\sum_{s=1}^r U_{is}U_{js}U_{ks}.$$
--   Sampling decisions and noise are attached to sorted coordinate triples and extended to their permutations. The observation is $P_\Omega(T(U^\star)+E)$, and the loss is
--   $$f(U)=\frac{1}{6p}\|P_\Omega(T(U)-T)\|_F^2.$$
--   The module also defines Definition 2.1's incoherence parameters, the condition number, factor norms, distances minimized over column permutations, the sampled-noise probability model, and Algorithms 1–3. Spectral and pruning choices are relations; gradient descent is the recursion printed in Algorithm 1. The good-event predicates require an admissible execution to exist and bound every admissible execution.
--
--   **Formalization Note.** Indices are zero-based `Fin` types. The Gaussian restarts, Bernoulli indicators and noise variables live on one probability space and are jointly independent. The noise's ψ₂ norm uses the published extended-nonnegative definition. Supremum and infimum definitions agree with the paper when the theorem's nonempty index conditions hold; $r=0$ and $d=0$ lie outside every theorem. Real-valued powers use natural logarithms and the usual real-power operation.
-- source:
--   Cai, Li, Poor, Chen, Nonconvex Low-Rank Tensor Completion from Noisy Data, arXiv:1911.04436v2, pp. 3–14, §1.1, §2, §3, Definition 2.1, Assumption 2.3, Algorithms 1–3, (20)–(23)

import Mathlib
import Definitions.Def_HighDimProb_Concentration_SubgaussianNorm_v2

open MeasureTheory ProbabilityTheory
open scoped MatrixOrder

noncomputable section

namespace TensorComp.GD

abbrev Tensor3 (d : ℕ) := Fin d → Fin d → Fin d → ℝ
abbrev Factor (d r : ℕ) := Matrix (Fin d) (Fin r) ℝ
abbrev Triple (d : ℕ) := Fin d × Fin d × Fin d
abbrev SortedIdx (d : ℕ) := {x : Triple d // x.1 ≤ x.2.1 ∧ x.2.1 ≤ x.2.2}

/-- The sorted orbit representative of a tensor coordinate. -/
def sortKey {d : ℕ} (x : Triple d) : SortedIdx d :=
  ⟨(min (min x.1 x.2.1) x.2.2,
    max (min x.1 x.2.1) (min (max x.1 x.2.1) x.2.2),
    max (max x.1 x.2.1) x.2.2), by
      dsimp
      constructor
      · exact (min_le_left _ _).trans (le_max_left _ _)
      · exact max_le
          ((min_le_left _ _).trans ((le_max_left _ _).trans (le_max_left _ _)))
          ((min_le_left _ _).trans (le_max_left _ _))⟩

def cpTensor {d r : ℕ} (U : Factor d r) : Tensor3 d :=
  fun i j k => ∑ s : Fin r, U i s * U j s * U k s

def cube {d : ℕ} (u : Fin d → ℝ) : Tensor3 d :=
  fun i j k => u i * u j * u k

def inner3 {d : ℕ} (A B : Tensor3 d) : ℝ :=
  ∑ i, ∑ j, ∑ k, A i j k * B i j k

def frobSq3 {d : ℕ} (A : Tensor3 d) : ℝ := inner3 A A

def projOmega {d : ℕ} (Ω : Finset (Triple d)) (A : Tensor3 d) : Tensor3 d :=
  fun i j k => if (i, j, k) ∈ Ω then A i j k else 0

def mode3 {d : ℕ} (A : Tensor3 d) (u : Fin d → ℝ) : Matrix (Fin d) (Fin d) ℝ :=
  fun i j => ∑ k, A i j k * u k

def mode12 {d : ℕ} (A : Tensor3 d) (u v : Fin d → ℝ) : Fin d → ℝ :=
  fun k => ∑ i, ∑ j, A i j k * u i * v j

def seqProd {d r : ℕ} (A : Tensor3 d) (U V : Factor d r) : Factor d r :=
  fun k s => mode12 A (fun i => U i s) (fun i => V i s) k

def unfold1 {d : ℕ} (A : Tensor3 d) : Matrix (Fin d) (Fin d × Fin d) ℝ :=
  fun i jk => A i jk.1 jk.2

def offDiag {d : ℕ} (B : Matrix (Fin d) (Fin d) ℝ) : Matrix (Fin d) (Fin d) ℝ :=
  fun i j => if i = j then 0 else B i j

def omegaOf {d : ℕ} (χ : SortedIdx d → Bool) : Finset (Triple d) :=
  Finset.univ.filter (fun x => χ (sortKey x))

def noiseOf {d : ℕ} (E : SortedIdx d → ℝ) : Tensor3 d :=
  fun i j k => E (sortKey (i, j, k))

def obs {d r : ℕ} (Ustar : Factor d r) (χ : SortedIdx d → Bool)
    (E : SortedIdx d → ℝ) : Tensor3 d :=
  projOmega (omegaOf χ) (cpTensor Ustar + noiseOf E)

def loss {d r : ℕ} (p : ℝ) (Ω : Finset (Triple d))
    (T : Tensor3 d) (U : Factor d r) : ℝ :=
  frobSq3 (projOmega Ω (cpTensor U - T)) / (6 * p)

def cleanLoss {d r : ℕ} (p : ℝ) (Ω : Finset (Triple d))
    (Ustar U : Factor d r) : ℝ :=
  frobSq3 (projOmega Ω (cpTensor U - cpTensor Ustar)) / (6 * p)

def gdStep {d r : ℕ} (p η : ℝ) (Ω : Finset (Triple d))
    (T : Tensor3 d) (U : Factor d r) : Factor d r :=
  U - (η / p) • seqProd (projOmega Ω (cpTensor U - T)) U U

def gdIter {d r : ℕ} (p η : ℝ) (Ω : Finset (Triple d))
    (T : Tensor3 d) (U0 : Factor d r) : ℕ → Factor d r
  | 0 => U0
  | t + 1 => gdStep p η Ω T (gdIter p η Ω T U0 t)

def colNorm {d r : ℕ} (U : Factor d r) (s : Fin r) : ℝ :=
  Real.sqrt (∑ i, (U i s) ^ 2)

def frobNorm {d r : ℕ} (U : Factor d r) : ℝ :=
  Real.sqrt (∑ i, ∑ s, (U i s) ^ 2)

def twoInfNorm {d r : ℕ} (U : Factor d r) : ℝ :=
  sSup (Set.range fun i : Fin d => Real.sqrt (∑ s, (U i s) ^ 2))

def entryMaxNorm {d r : ℕ} (U : Factor d r) : ℝ :=
  sSup (Set.range fun x : Fin d × Fin r => |U x.1 x.2|)

def tensorMaxNorm {d : ℕ} (A : Tensor3 d) : ℝ :=
  sSup (Set.range fun x : Triple d => |A x.1 x.2.1 x.2.2|)

def permCols {d r : ℕ} (π : Equiv.Perm (Fin r)) (U : Factor d r) : Factor d r :=
  fun i s => U i (π s)

def distF {d r : ℕ} (U V : Factor d r) : ℝ :=
  sInf (Set.range fun π : Equiv.Perm (Fin r) => frobNorm (permCols π U - V))

def distInf {d r : ℕ} (U V : Factor d r) : ℝ :=
  sInf (Set.range fun π : Equiv.Perm (Fin r) => entryMaxNorm (permCols π U - V))

def distTwoInf {d r : ℕ} (U V : Factor d r) : ℝ :=
  sInf (Set.range fun π : Equiv.Perm (Fin r) => twoInfNorm (permCols π U - V))

def lamMin {d r : ℕ} (Ustar : Factor d r) : ℝ :=
  sInf (Set.range fun s : Fin r => colNorm Ustar s ^ 3)

def lamMax {d r : ℕ} (Ustar : Factor d r) : ℝ :=
  sSup (Set.range fun s : Fin r => colNorm Ustar s ^ 3)

def mu0 {d r : ℕ} (Ustar : Factor d r) : ℝ :=
  (d : ℝ) ^ 3 * tensorMaxNorm (cpTensor Ustar) ^ 2 /
    frobSq3 (cpTensor Ustar)

def mu1 {d r : ℕ} (Ustar : Factor d r) : ℝ :=
  sSup (Set.range fun s : Fin r =>
    (d : ℝ) * (sSup (Set.range fun i : Fin d => |Ustar i s|)) ^ 2 /
      colNorm Ustar s ^ 2)

def mu2 {d r : ℕ} (Ustar : Factor d r) : ℝ :=
  sSup ({0} ∪ Set.range (fun x : {x : Fin r × Fin r // x.1 ≠ x.2} =>
    (d : ℝ) * (∑ i, Ustar i x.1.1 * Ustar i x.1.2) ^ 2 /
      (colNorm Ustar x.1.1 ^ 2 * colNorm Ustar x.1.2 ^ 2)))

def mu {d r : ℕ} (Ustar : Factor d r) : ℝ :=
  max (mu0 Ustar) (max (mu1 Ustar) (mu2 Ustar))

def kappa {d r : ℕ} (Ustar : Factor d r) : ℝ :=
  (sSup (Set.range fun s : Fin r => colNorm Ustar s)) /
    (sInf (Set.range fun s : Fin r => colNorm Ustar s))

/-- Sampling on sorted triples, followed by symmetry to all tensor coordinates. -/
def SamplingModel {d : ℕ} {Ωp : Type} [MeasurableSpace Ωp]
    (P : Measure Ωp) (p : ℝ) (χ : SortedIdx d → Ωp → Bool) : Prop :=
  (∀ x, Measurable (χ x)) ∧
  (∀ x, P {ω | χ x ω = true} = ENNReal.ofReal p) ∧
  iIndepFun χ P

/-- The sampling and noisy observations, before Gaussian algorithm restarts. -/
def ObservationModel {d : ℕ} {Ωp : Type} [MeasurableSpace Ωp]
    (P : Measure Ωp) (p σ : ℝ) (χ : SortedIdx d → Ωp → Bool)
    (E : SortedIdx d → Ωp → ℝ) : Prop :=
  SamplingModel P p χ ∧
  (∀ x, Measurable (E x)) ∧
  (∀ x, Integrable (E x) P ∧ (∫ ω, E x ω ∂P) = 0 ∧
    ProbabilityTheory.variance (E x) P ≤ σ ^ 2 ∧
    HighDimProb.Concentration.subgaussianNorm P (E x) ≤ ENNReal.ofReal σ) ∧
  iIndepFun E P ∧
  IndepFun (fun ω x => χ x ω) (fun ω x => E x ω) P

/-- The paper's joint sampling, noise, and Gaussian restart model. -/
def Model {d L : ℕ} {Ωp : Type} [MeasurableSpace Ωp]
    (P : Measure Ωp) (p σ : ℝ) (χ : SortedIdx d → Ωp → Bool)
    (E : SortedIdx d → Ωp → ℝ)
    (g : Fin L → Ωp → EuclideanSpace ℝ (Fin d)) : Prop :=
  ObservationModel P p σ χ E ∧
  (∀ τ, Measurable (g τ)) ∧
  (∀ τ, P.map (g τ) = stdGaussian (EuclideanSpace ℝ (Fin d))) ∧
  iIndepFun (fun (z : Sum (SortedIdx d) (Sum (SortedIdx d) (Fin L))) ω =>
    match z with
    | .inl x => (Sum.inl (χ x ω) : Sum Bool (Sum ℝ (EuclideanSpace ℝ (Fin d))))
    | .inr (.inl x) => Sum.inr (Sum.inl (E x ω))
    | .inr (.inr τ) => Sum.inr (Sum.inr (g τ ω))) P

def spectralInput {d : ℕ} (T : Tensor3 d) (p : ℝ) : Matrix (Fin d) (Fin d) ℝ :=
  offDiag ((unfold1 (fun i j k => T i j k / p)) *
    (unfold1 (fun i j k => T i j k / p)).transpose)

/-- Top-r orthonormal eigenvectors, including arbitrary choices at tied eigenvalues. -/
def IsAlg2Output {d r : ℕ} (B : Matrix (Fin d) (Fin d) ℝ)
    (U : Factor d r) : Prop :=
  (∀ s t : Fin r, (∑ i, U i s * U i t) = if s = t then 1 else 0) ∧
  ∃ eigval : Fin r → ℝ, Antitone eigval ∧
    (∀ s i, (∑ j, B i j * U j s) = eigval s * U i s) ∧
    (∀ x : Fin d → ℝ, (∀ s, (∑ i, U i s * x i) = 0) →
      (∑ i, x i * (∑ j, B i j * x j)) ≤
        sInf (Set.range eigval) * (∑ i, x i ^ 2))

def projectedGaussian {d r : ℕ} (U : Factor d r)
    (g : Fin d → ℝ) : Fin d → ℝ :=
  fun i => ∑ s, U i s * (∑ j, U j s * g j)

def vectorSqNorm {d : ℕ} (v : Fin d → ℝ) : ℝ :=
  ∑ i, v i ^ 2

def vectorNorm {d : ℕ} (v : Fin d → ℝ) : ℝ :=
  Real.sqrt (vectorSqNorm v)

def matVecSqNorm {d : ℕ} (M : Matrix (Fin d) (Fin d) ℝ)
    (v : Fin d → ℝ) : ℝ :=
  ∑ i, (∑ j, M i j * v j) ^ 2

def IsRetrieveOutput {d r : ℕ} (T : Tensor3 d) (p : ℝ)
    (U : Factor d r) (g : Fin d → ℝ) (ν : Fin d → ℝ)
    (weight gap : ℝ) : Prop :=
  let θ := projectedGaussian U g
  let M := mode3 (fun i j k => T i j k / p) θ
  vectorSqNorm ν = 1 ∧
  (∀ v : Fin d → ℝ, vectorSqNorm v = 1 →
    matVecSqNorm M v ≤ matVecSqNorm M ν) ∧
  0 ≤ inner3 T (cube ν) ∧
  weight = inner3 (fun i j k => T i j k / p) (cube ν) ∧
  gap = (M.toEuclideanLin.singularValues 0 : ℝ) -
    (M.toEuclideanLin.singularValues 1 : ℝ)

/-- The surviving indices before the i-th greedy pruning choice. -/
def IsPruneOutput {d r L : ℕ} (ν : Fin L → Fin d → ℝ)
    (gap : Fin L → ℝ) (epsTh : ℝ) (picked : Fin r → Fin L) : Prop :=
  ∀ i : Fin r,
    (∀ j : Fin r, j < i →
      |∑ k, ν (picked j) k * ν (picked i) k| ≤ 1 - epsTh) ∧
    ∀ τ : Fin L,
      (∀ j : Fin r, j < i →
        |∑ k, ν (picked j) k * ν τ k| ≤ 1 - epsTh) →
      gap τ ≤ gap (picked i)

def IsFactorOutput {d r L : ℕ} (T : Tensor3 d) (p epsTh : ℝ)
    (g : Fin L → Fin d → ℝ)
    (w : Fin r → Fin d → ℝ) (weightOut : Fin r → ℝ) : Prop :=
  ∃ U : Factor d r, IsAlg2Output (spectralInput T p) U ∧
  ∃ (ν : Fin L → Fin d → ℝ) (weight gap : Fin L → ℝ)
      (picked : Fin r → Fin L),
    (∀ τ, IsRetrieveOutput T p U (g τ) (ν τ) (weight τ) (gap τ)) ∧
    IsPruneOutput ν gap epsTh picked ∧
    (∀ s, w s = ν (picked s) ∧ weightOut s = weight (picked s))

def IsInitOutput {d r L : ℕ} (T : Tensor3 d) (p epsTh : ℝ)
    (g : Fin L → Fin d → ℝ) (U0 : Factor d r) : Prop :=
  ∃ (w : Fin r → Fin d → ℝ) (weight : Fin r → ℝ),
    IsFactorOutput T p epsTh g w weight ∧
    U0 = fun i s => (weight s) ^ (1 / 3 : ℝ) * w s i

def gram {d r : ℕ} (U : Factor d r) : Matrix (Fin r) (Fin r) ℝ :=
  U.transpose * U

def orthTruth {d r : ℕ} (Ustar : Factor d r) : Factor d r :=
  Ustar * (CFC.sqrt (gram Ustar))⁻¹

def isAlignment {d r : ℕ} (U Ustar : Factor d r)
    (Q : Matrix (Fin r) (Fin r) ℝ) : Prop :=
  Q.transpose * Q = 1 ∧
  ∀ R : Matrix (Fin r) (Fin r) ℝ, R.transpose * R = 1 →
    frobNorm (U * Q - orthTruth Ustar) ≤ frobNorm (U * R - orthTruth Ustar)

def spectralNorm {d r : ℕ} (U : Factor d r) : ℝ :=
  sSup (Set.range fun v : Fin r → ℝ =>
    Real.sqrt (∑ i, (∑ s, U i s * v s) ^ 2) / Real.sqrt (∑ s, v s ^ 2))

def Ese {d r : ℕ} (Ustar : Factor d r) (p σ : ℝ) : ℝ :=
  let μ := mu Ustar
  let lam := lamMin Ustar
  μ ^ 2 * r * Real.log d / ((d : ℝ) ^ (3 / 2 : ℝ) * p) +
  Real.sqrt (μ ^ 2 * r * Real.log d / ((d : ℝ) ^ 2 * p)) +
  σ ^ 2 / lam ^ 2 * ((d : ℝ) ^ (3 / 2 : ℝ) * Real.log d / p) +
  σ / lam * Real.sqrt ((d : ℝ) * Real.log d / p) + μ * r / d

def GoodGD {d r L : ℕ} {Ωp : Type} (Ustar : Factor d r)
    (p σ η epsTh ρ C₁ C₂ C₃ C₄ : ℝ)
    (χ : SortedIdx d → Ωp → Bool) (E : SortedIdx d → Ωp → ℝ)
    (g : Fin L → Ωp → EuclideanSpace ℝ (Fin d)) (ω : Ωp) : Prop :=
  let T := obs Ustar (fun x => χ x ω) (fun x => E x ω)
  let Ω := omegaOf (fun x => χ x ω)
  let noise := σ / lamMin Ustar *
    Real.sqrt ((d : ℝ) * Real.log d / p)
  (∃ U0 : Factor d r, IsInitOutput T p epsTh (fun τ i => g τ ω i) U0) ∧
  ∀ U0 : Factor d r, IsInitOutput T p epsTh (fun τ i => g τ ω i) U0 →
    ∀ t : ℕ, t ≤ d ^ 5 →
      distF (gdIter p η Ω T U0 t) Ustar ≤
        (C₁ * ρ ^ t + C₂ * noise) * frobNorm Ustar ∧
      distInf (gdIter p η Ω T U0 t) Ustar ≤
        distTwoInf (gdIter p η Ω T U0 t) Ustar ∧
      distTwoInf (gdIter p η Ω T U0 t) Ustar ≤
        (C₃ * ρ ^ t + C₄ * noise) * twoInfNorm Ustar

def GoodSpec {d r : ℕ} {Ωp : Type} (Ustar : Factor d r)
    (p σ K₁ K₂ : ℝ) (χ : SortedIdx d → Ωp → Bool)
    (E : SortedIdx d → Ωp → ℝ) (ω : Ωp) : Prop :=
  let T := obs Ustar (fun x => χ x ω) (fun x => E x ω)
  let B := spectralInput T p
  (∃ U : Factor d r, IsAlg2Output B U) ∧
  ∀ U : Factor d r, IsAlg2Output B U →
    (∃ Q : Matrix (Fin r) (Fin r) ℝ, isAlignment U Ustar Q) ∧
    ∀ Q : Matrix (Fin r) (Fin r) ℝ, isAlignment U Ustar Q →
      spectralNorm (U * Q - orthTruth Ustar) ≤ K₁ * Ese Ustar p σ ∧
      twoInfNorm (U * Q - orthTruth Ustar) ≤
        K₂ * Ese Ustar p σ * Real.sqrt (mu Ustar * r / d)

def trueUnit {d r : ℕ} (Ustar : Factor d r) (s : Fin r) : Fin d → ℝ :=
  fun i => Ustar i s / colNorm Ustar s

def trueWeight {d r : ℕ} (Ustar : Factor d r) (s : Fin r) : ℝ :=
  colNorm Ustar s ^ 3

def vectorInfNorm {d : ℕ} (v : Fin d → ℝ) : ℝ :=
  sSup (Set.range fun i : Fin d => |v i|)

def factorError2 {d r : ℕ} (Ustar : Factor d r) (p σ : ℝ) : ℝ :=
  let μ := mu Ustar
  let lam := lamMin Ustar
  μ * r * Real.log d / ((d : ℝ) * Real.sqrt p) +
    σ / lam * Real.sqrt (r * (d : ℝ) * Real.log d ^ 2 / p) +
    Real.sqrt (μ * r * Real.log d / d)

def factorErrorInf {d r : ℕ} (Ustar : Factor d r) (p σ : ℝ) : ℝ :=
  let μ := mu Ustar
  let lam := lamMin Ustar
  μ ^ 2 * r * Real.log d ^ 4 / ((d : ℝ) ^ (3 / 2 : ℝ) * p) +
    μ * r * Real.log d ^ 3 / ((d : ℝ) * Real.sqrt p) +
    σ ^ 2 / lam ^ 2 * ((d : ℝ) ^ (3 / 2 : ℝ) * Real.log d ^ 4 / p) +
    σ / lam * Real.sqrt (r * (d : ℝ) * Real.log d ^ 6 / p) +
    Real.sqrt (μ * r * Real.log d ^ 2 / d)

def GoodFactors {d r L : ℕ} {Ωp : Type} (Ustar : Factor d r)
    (p σ epsTh K₂ Kinf Kweight : ℝ)
    (χ : SortedIdx d → Ωp → Bool) (E : SortedIdx d → Ωp → ℝ)
    (g : Fin L → Ωp → EuclideanSpace ℝ (Fin d)) (ω : Ωp) : Prop :=
  let T := obs Ustar (fun x => χ x ω) (fun x => E x ω)
  (∃ (w : Fin r → Fin d → ℝ) (weight : Fin r → ℝ),
      IsFactorOutput T p epsTh (fun τ i => g τ ω i) w weight) ∧
  ∀ (w : Fin r → Fin d → ℝ) (weight : Fin r → ℝ),
    IsFactorOutput T p epsTh (fun τ i => g τ ω i) w weight →
    ∃ π : Equiv.Perm (Fin r), ∀ s : Fin r,
      vectorNorm (w s - trueUnit Ustar (π s)) ≤
        K₂ * factorError2 Ustar p σ ∧
      vectorInfNorm (w s - trueUnit Ustar (π s)) ≤
        Kinf * factorErrorInf Ustar p σ *
          Real.sqrt (mu Ustar * r / d) ∧
      |weight s - trueWeight Ustar (π s)| ≤
        Kweight * factorError2 Ustar p σ * trueWeight Ustar (π s)

end TensorComp.GD


