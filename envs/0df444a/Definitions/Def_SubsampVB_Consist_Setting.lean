-- Prove2me | Definitions.Def_SubsampVB_Consist_Setting
-- name    : SubsampVB_Consist_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-20T12:45:28.818367+00:00
-- url     : https://prove2.me/theorems/c20ea572-385b-46e4-8b87-355de5b49913
-- title:
--   Input uncertainty and the proportionate subsampled variance bootstrap
-- statement:
--   The model has $m\ge1$ input laws $F_i$ on measurable spaces $\Xi_i$ and a real performance functional $\psi(P_1,\ldots,P_m)$. Each data row contains independent observations $X_{i,j}$ from $F_i$; observations are also independent across rows. The empirical law $\widehat F_i$ uses the first $n_i$ observations. Its **input variance** is
--
--   $$\sigma_I^2=\operatorname{Var}\!\left[\psi(\widehat F_1,\ldots,\widehat F_m)\right].$$
--
--   Given a subsample ratio $0<\theta\le1$, Algorithm 2 draws $s_i=\lfloor\theta n_i\rfloor$ observations with replacement from each row in each of $B$ groups, then simulates $R$ independent responses per group. If $\bar\psi^b$ is the mean response in group $b$, $\bar{\bar\psi}$ is the mean of the group means, and $V$ is the pooled within-group sample variance, its reported value is
--
--   $$\widehat\sigma_{SVB}^2=\theta\left\{\frac1{B-1}\sum_{b=1}^{B}(\bar\psi^b-\bar{\bar\psi})^2-\frac VR\right\},\qquad V=\frac1{B(R-1)}\sum_{b=1}^{B}\sum_{r=1}^{R}(\widehat\psi_r^b-\bar\psi^b)^2.$$
--
--   The corresponding bootstrap quantity without simulation error is $\sigma_{SVB}^2=\theta\operatorname{Var}_*\!\left[\psi(\widehat F_{s_1,1}^*,\ldots,\widehat F_{s_m,m}^*)\right]$. Conditional bootstrap expectations are finite uniform averages over all index maps. Conditional simulation laws are products of the one-replication law, so the responses are independent given the resamples.
--
--   The definitions also state Assumptions 1–7 from pp. 20–23. These cover comparable data sizes; centered first-order influence functions on the stated convex hulls of $F_i$ and point masses; small data and bootstrap expansion remainders; positive influence variances and fourth moments; and stability of simulation variance and fourth moments. The source uses $n=m^{-1}\sum_i n_i$. Its unspecified $s$ in Assumption 4 is represented by $\theta n$.
--
--   **Formalization Note** An infinite independent data array couples every sample size to one probability space. A measurable full-measure set $S_i$ supplies the paper's support points. Expectation and variance hypotheses include integrability guards. The fourth simulation moment takes values in extended nonnegative reals; a non-integrable fourth moment is therefore infinite, never a default zero. On a zero-size finite sample the empirical measure is zero, and the asymptotic hypotheses ensure positive sample and subsample sizes eventually.
-- source:
--   Lam & Qian, Subsampling to enhance efficiency in input uncertainty quantification, arXiv:1811.04500v2, pp. 6–23, (1), (4), (8), (13)–(15), Algorithm 2, Assumptions 1–7

import Mathlib
import Definitions.Def_SubsampVB_Consist_Empirical

namespace SubsampVB.Consist

open MeasureTheory Filter Finset

universe u v

noncomputable section

/-- A finite vector of input probability laws. -/
abbrev Inputs {m : ℕ} (Ξ : Fin m → Type u) [∀ i, MeasurableSpace (Ξ i)] :=
  ∀ i, Measure (Ξ i)

/-- A vector of finite data samples. -/
abbrev Sample {m : ℕ} (Ξ : Fin m → Type u) (n : Fin m → ℕ) :=
  ∀ i, Fin (n i) → Ξ i

/-- One simultaneous with-replacement resample of every input. -/
abbrev Resample {m : ℕ} (n s : Fin m → ℕ) :=
  ∀ i, Fin (s i) → Fin (n i)

/-- A finite mixture of the true law and Dirac masses at the support points. -/
def Pset {α : Type u} [MeasurableSpace α] (F : Measure α) (S : Set α) :
    Set (Measure α) :=
  {Q | ∃ (l : ℕ) (w : Fin (l + 1) → ENNReal) (x : Fin l → α),
    (∑ j, w j) = 1 ∧ (∀ j, x j ∈ S) ∧
    Q = (w 0) • F + ∑ j : Fin l, (w j.succ) • Measure.dirac (x j)}

/-- The empirical input models based on a sample. -/
def Fhat {m : ℕ} {Ξ : Fin m → Type u} [∀ i, MeasurableSpace (Ξ i)]
    {n : Fin m → ℕ} (x : Sample Ξ n) : Inputs Ξ :=
  fun i => empirical (x i)

/-- Empirical input models after replacing the coordinates in T by subsamples. -/
def Fbar {m : ℕ} {Ξ : Fin m → Type u} [∀ i, MeasurableSpace (Ξ i)]
    {n s : Fin m → ℕ} (T : Finset (Fin m)) (I : Resample n s)
    (x : Sample Ξ n) : Inputs Ξ :=
  fun i => if i ∈ T then empirical (fun j : Fin (s i) => x i (I i j)) else Fhat x i

/-- Uniform conditional expectation over all with-replacement index maps. -/
def bootAvg {m : ℕ} {n s : Fin m → ℕ} (f : Resample n s → ℝ) : ℝ :=
  (Fintype.card (Resample n s) : ℝ)⁻¹ * ∑ I : Resample n s, f I

/-- Extended-nonnegative conditional expectation over index maps. -/
def bootAvgENN {m : ℕ} {n s : Fin m → ℕ} (f : Resample n s → ENNReal) : ENNReal :=
  (Fintype.card (Resample n s) : ENNReal)⁻¹ * ∑ I : Resample n s, f I

/-- The subsample size in Algorithm 2. -/
def subsampleSize {m : ℕ} (θ : ℝ) (n : Fin m → ℕ) : Fin m → ℕ :=
  fun i => ⌊θ * n i⌋₊

/-- The sample from the first n_i observations of each infinite data row. -/
def dataSample {m : ℕ} {Ξ : Fin m → Type u} {Ω : Type v}
    (X : ∀ i : Fin m, ℕ → Ω → Ξ i) (n : Fin m → ℕ) (ω : Ω) : Sample Ξ n :=
  fun i j => X i j ω

/-- The simulation variance for a given vector of input models. -/
def tau2 {m : ℕ} {Ξ : Fin m → Type u} [∀ i, MeasurableSpace (Ξ i)]
    (ψ : Inputs Ξ → ℝ) (simLaw : Inputs Ξ → Measure ℝ) (Q : Inputs Ξ) : ℝ :=
  ∫ y, (y - ψ Q) ^ 2 ∂(simLaw Q)

/-- The fourth central simulation moment, retained in extended nonnegative reals. -/
def mu4 {m : ℕ} {Ξ : Fin m → Type u} [∀ i, MeasurableSpace (Ξ i)]
    (ψ : Inputs Ξ → ℝ) (simLaw : Inputs Ξ → Measure ℝ) (Q : Inputs Ξ) : ENNReal :=
  ∫⁻ y, ‖y - ψ Q‖ₑ ^ 4 ∂(simLaw Q)

/-- The exact conditional subsampled bootstrap variance, equation (8). -/
def sigmaSVB {m : ℕ} {Ξ : Fin m → Type u} [∀ i, MeasurableSpace (Ξ i)]
    (ψ : Inputs Ξ → ℝ) {n : Fin m → ℕ} (θ : ℝ) (x : Sample Ξ n) : ℝ :=
  let s := subsampleSize θ n
  let avg := bootAvg (n := n) (s := s) (fun I => ψ (Fbar univ I x))
  θ * bootAvg (n := n) (s := s) (fun I => (ψ (Fbar univ I x) - avg) ^ 2)

/-- Input variance, equation (1), over the original data law. -/
def sigmaI {m : ℕ} {Ξ : Fin m → Type u} [∀ i, MeasurableSpace (Ξ i)]
    {Ω : Type v} [MeasurableSpace Ω] (ψ : Inputs Ξ → ℝ)
    (P : Measure Ω) (X : ∀ i : Fin m, ℕ → Ω → Ξ i) (n : Fin m → ℕ) : ℝ :=
  ProbabilityTheory.variance (fun ω => ψ (Fhat (dataSample X n ω))) P

/-- Variance of the ith true influence function. -/
def sigma2 {m : ℕ} {Ξ : Fin m → Type u} [∀ i, MeasurableSpace (Ξ i)]
    (F : Inputs Ξ) (g : Inputs Ξ → ∀ i, Ξ i → ℝ) (i : Fin m) : ℝ :=
  ProbabilityTheory.variance (g F i) (F i)

/-- Empirical variance of the ith influence function at the empirical model. -/
def sigmaHat2 {m : ℕ} {Ξ : Fin m → Type u} [∀ i, MeasurableSpace (Ξ i)]
    (g : Inputs Ξ → ∀ i, Ξ i → ℝ) {n : Fin m → ℕ}
    (x : Sample Ξ n) (i : Fin m) : ℝ :=
  (n i : ℝ)⁻¹ * (∑ j : Fin (n i), (g (Fhat x) i (x i j)) ^ 2) -
    ((n i : ℝ)⁻¹ * (∑ j : Fin (n i), g (Fhat x) i (x i j))) ^ 2

/-- The mean of the R simulation responses within one resample. -/
def groupMean {B R : ℕ} (Y : Fin B → Fin R → ℝ) (b : Fin B) : ℝ :=
  (R : ℝ)⁻¹ * ∑ r : Fin R, Y b r

/-- The mean of the B group means. -/
def grandMean {B R : ℕ} (Y : Fin B → Fin R → ℝ) : ℝ :=
  (B : ℝ)⁻¹ * ∑ b : Fin B, groupMean Y b

/-- Pooled within-group variance V in Algorithm 2. -/
def withinV {B R : ℕ} (Y : Fin B → Fin R → ℝ) : ℝ :=
  ((B : ℝ) * ((R : ℝ) - 1))⁻¹ *
    ∑ b : Fin B, ∑ r : Fin R, (Y b r - groupMean Y b) ^ 2

/-- Algorithm 2's reported variance estimate. -/
def sigmaHatSVB {B R : ℕ} (θ : ℝ) (Y : Fin B → Fin R → ℝ) : ℝ :=
  θ * (((B : ℝ) - 1)⁻¹ * (∑ b : Fin B, (groupMean Y b - grandMean Y) ^ 2) -
    withinV Y / R)

/-- The product law of independent simulation replications conditional on resamples. -/
def outputLaw {m B R : ℕ} {Ξ : Fin m → Type u} [∀ i, MeasurableSpace (Ξ i)]
    (simLaw : Inputs Ξ → Measure ℝ) {n s : Fin m → ℕ}
    (I : Fin B → Resample n s) (x : Sample Ξ n) : Measure (Fin B → Fin R → ℝ) :=
  Measure.pi (fun b : Fin B =>
    Measure.pi (fun _ : Fin R => simLaw (Fbar univ (I b) x)))

/-- Conditional probability of an event in the B-by-R output array. -/
def outProb {m B R : ℕ} {Ξ : Fin m → Type u} [∀ i, MeasurableSpace (Ξ i)]
    (simLaw : Inputs Ξ → Measure ℝ) {n s : Fin m → ℕ}
    (x : Sample Ξ n) (A : Set (Fin B → Fin R → ℝ)) : ℝ :=
  (Fintype.card (Fin B → Resample n s) : ℝ)⁻¹ *
    ∑ I : Fin B → Resample n s, (outputLaw (R := R) simLaw I x A).toReal

/-- Conditional mean squared Monte Carlo error of Algorithm 2. -/
def outMSE {m B R : ℕ} {Ξ : Fin m → Type u} [∀ i, MeasurableSpace (Ξ i)]
    (ψ : Inputs Ξ → ℝ) (simLaw : Inputs Ξ → Measure ℝ)
    {n s : Fin m → ℕ} (θ : ℝ) (x : Sample Ξ n) : ℝ :=
  (Fintype.card (Fin B → Resample n s) : ℝ)⁻¹ *
    ∑ I : Fin B → Resample n s,
      ∫ Y, (sigmaHatSVB θ Y - sigmaSVB ψ θ x) ^ 2 ∂(outputLaw (R := R) simLaw I x)

/-- Average input sample size n in the paper. -/
def nbar {m : ℕ} (n : Fin m → ℕ) : ℝ :=
  (∑ i : Fin m, (n i : ℝ)) / m

/-- The first-order data expansion's remainder, equation (14). -/
def dataRemainder {m : ℕ} {Ξ : Fin m → Type u} [∀ i, MeasurableSpace (Ξ i)]
    (F : Inputs Ξ) (ψ : Inputs Ξ → ℝ) (g : Inputs Ξ → ∀ i, Ξ i → ℝ)
    {n : Fin m → ℕ} (x : Sample Ξ n) : ℝ :=
  ψ (Fhat x) - ψ F -
    ∑ i : Fin m, ((n i : ℝ)⁻¹ * ∑ j : Fin (n i), g F i (x i j) -
      ∫ z, g F i z ∂(F i))

/-- The bootstrap expansion's remainder, equation (15), for a choice T of resampled inputs. -/
def bootRemainder {m : ℕ} {Ξ : Fin m → Type u} [∀ i, MeasurableSpace (Ξ i)]
    (ψ : Inputs Ξ → ℝ) (g : Inputs Ξ → ∀ i, Ξ i → ℝ)
    {n s : Fin m → ℕ} (T : Finset (Fin m)) (I : Resample n s)
    (x : Sample Ξ n) : ℝ :=
  ψ (Fbar T I x) - ψ (Fhat x) -
    ∑ i : Fin m, if i ∈ T then
      ((s i : ℝ)⁻¹ * ∑ j : Fin (s i), g (Fhat x) i (x i (I i j))) -
      ((n i : ℝ)⁻¹ * ∑ j : Fin (n i), g (Fhat x) i (x i j))
    else 0

/-- An independently coupled infinite array of i.i.d. input observations. -/
def IIDData {m : ℕ} {Ξ : Fin m → Type u} [∀ i, MeasurableSpace (Ξ i)]
    {Ω : Type v} [MeasurableSpace Ω] (P : Measure Ω) (F : Inputs Ξ)
    (X : ∀ i : Fin m, ℕ → Ω → Ξ i) : Prop :=
  (∀ i j, Measurable (X i j) ∧ Measure.map (X i j) P = F i) ∧
    ProbabilityTheory.iIndepFun (fun p : (Σ i : Fin m, ℕ) => X p.1 p.2) P

/-- The conditional simulation oracle produces unbiased, independent replications. -/
def SimOracle {m : ℕ} {Ξ : Fin m → Type u} [∀ i, MeasurableSpace (Ξ i)]
    (ψ : Inputs Ξ → ℝ) (simLaw : Inputs Ξ → Measure ℝ) : Prop :=
  ∀ Q : Inputs Ξ, (∀ i, IsProbabilityMeasure (Q i)) →
    IsProbabilityMeasure (simLaw Q) ∧ Integrable id (simLaw Q) ∧
      (∫ y, y ∂(simLaw Q)) = ψ Q

/-- Assumption 1: all data sizes diverge along a balanced sequence. -/
def A1 {m : ℕ} (n : ℕ → Fin m → ℕ) : Prop :=
  (∀ i, Tendsto (fun k => (n k i : ℝ)) atTop atTop) ∧
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ k in atTop, ∀ i j, (n k i : ℝ) ≤ C * n k j

/-- Coordinatewise convex interpolation of two input-model vectors. -/
def interpolate {m : ℕ} {Ξ : Fin m → Type u} [∀ i, MeasurableSpace (Ξ i)]
    (P Q : Inputs Ξ) (ν : Fin m → ℝ) : Inputs Ξ :=
  fun i => (ENNReal.ofReal (1 - ν i)) • P i + (ENNReal.ofReal (ν i)) • Q i

/-- Assumption 2: centered influence functions and the first-order directional expansion. -/
def A2 {m : ℕ} {Ξ : Fin m → Type u} [∀ i, MeasurableSpace (Ξ i)]
    (F : Inputs Ξ) (S : ∀ i, Set (Ξ i)) (ψ : Inputs Ξ → ℝ)
    (g : Inputs Ξ → ∀ i, Ξ i → ℝ) : Prop :=
  (∀ P : Inputs Ξ, (∀ i, P i ∈ Pset (F i) (S i)) →
    ∀ i, Integrable (g P i) (P i) ∧ (∫ x, g P i x ∂(P i)) = 0) ∧
  (∀ P Q : Inputs Ξ,
    (∀ i, P i ∈ Pset (F i) (S i) ∧ Q i ∈ Pset (F i) (S i)) →
    (∀ i, Integrable (g P i) (Q i)) ∧
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ ν : Fin m → ℝ, (∀ i, 0 ≤ ν i ∧ ν i ≤ 1) →
        Real.sqrt (∑ i : Fin m, (ν i) ^ 2) < δ →
        |ψ (interpolate P Q ν) - ψ P -
          ∑ i : Fin m, ν i * ((∫ x, g P i x ∂(Q i)) -
            (∫ x, g P i x ∂(P i)))| ≤
          ε * Real.sqrt (∑ i : Fin m, (ν i) ^ 2))

/-- Assumption 3: square-integrable negligible true-model remainder and nondegenerate influences. -/
def A3 {m : ℕ} {Ξ : Fin m → Type u} [∀ i, MeasurableSpace (Ξ i)]
    {Ω : Type v} [MeasurableSpace Ω] (P : Measure Ω) (F : Inputs Ξ)
    (ψ : Inputs Ξ → ℝ) (g : Inputs Ξ → ∀ i, Ξ i → ℝ)
    (X : ∀ i : Fin m, ℕ → Ω → Ξ i) (n : ℕ → Fin m → ℕ) : Prop :=
  (∀ i, 0 < sigma2 F g i ∧ MemLp (g F i) 4 (F i)) ∧
  (∀ᶠ k in atTop, MemLp (fun ω => dataRemainder F ψ g (dataSample X (n k) ω)) 2 P ∧
    MemLp (fun ω => ψ (Fhat (dataSample X (n k) ω))) 2 P) ∧
  Tendsto (fun k => nbar (n k) *
    ∫ ω, (dataRemainder F ψ g (dataSample X (n k) ω)) ^ 2 ∂P) atTop (nhds 0)

/-- Assumption 4: empirical influence convergence and a small fourth bootstrap remainder. -/
def A4 {m : ℕ} {Ξ : Fin m → Type u} [∀ i, MeasurableSpace (Ξ i)]
    {Ω : Type v} [MeasurableSpace Ω] (P : Measure Ω) (F : Inputs Ξ)
    (ψ : Inputs Ξ → ℝ) (g : Inputs Ξ → ∀ i, Ξ i → ℝ)
    (X : ∀ i : Fin m, ℕ → Ω → Ξ i) (n : ℕ → Fin m → ℕ)
    (θ : ℕ → ℝ) : Prop :=
  (∀ i, (∀ᶠ k in atTop, Integrable (fun ω =>
      (g (Fhat (dataSample X (n k) ω)) i (X i 0 ω) - g F i (X i 0 ω)) ^ 4) P) ∧
    Tendsto (fun k => ∫ ω,
      (g (Fhat (dataSample X (n k) ω)) i (X i 0 ω) - g F i (X i 0 ω)) ^ 4 ∂P)
      atTop (nhds 0)) ∧
  ∀ T : Finset (Fin m),
    TendstoInMeasure P (fun k ω =>
      let x := dataSample X (n k) ω
      let s := subsampleSize (θ k) (n k)
      ((θ k * nbar (n k)) ^ 2) *
        bootAvg (n := n k) (s := s) (fun I => (bootRemainder ψ g T I x) ^ 4))
      atTop (fun _ => 0)

/-- Assumption 5: empirical simulation variance converges to its true-model value. -/
def A5 {m : ℕ} {Ξ : Fin m → Type u} [∀ i, MeasurableSpace (Ξ i)]
    {Ω : Type v} [MeasurableSpace Ω] (P : Measure Ω) (F : Inputs Ξ)
    (ψ : Inputs Ξ → ℝ) (simLaw : Inputs Ξ → Measure ℝ)
    (X : ∀ i : Fin m, ℕ → Ω → Ξ i) (n : ℕ → Fin m → ℕ) : Prop :=
  TendstoInMeasure P (fun k ω => tau2 ψ simLaw (Fhat (dataSample X (n k) ω)))
    atTop (fun _ => tau2 ψ simLaw F)

/-- Assumption 6: resampled simulation variance is close to empirical simulation variance. -/
def A6 {m : ℕ} {Ξ : Fin m → Type u} [∀ i, MeasurableSpace (Ξ i)]
    {Ω : Type v} [MeasurableSpace Ω] (P : Measure Ω) (ψ : Inputs Ξ → ℝ)
    (simLaw : Inputs Ξ → Measure ℝ)
    (X : ∀ i : Fin m, ℕ → Ω → Ξ i) (n : ℕ → Fin m → ℕ)
    (θ : ℕ → ℝ) : Prop :=
  ∀ T : Finset (Fin m), TendstoInMeasure P (fun k ω =>
      let x := dataSample X (n k) ω
      let s := subsampleSize (θ k) (n k)
      bootAvg (n := n k) (s := s) (fun I =>
        (tau2 ψ simLaw (Fbar T I x) - tau2 ψ simLaw (Fhat x)) ^ 2))
    atTop (fun _ => 0)

/-- Assumption 7: the conditional fourth simulation moment is bounded in probability. -/
def A7 {m : ℕ} {Ξ : Fin m → Type u} [∀ i, MeasurableSpace (Ξ i)]
    {Ω : Type v} [MeasurableSpace Ω] (P : Measure Ω) (ψ : Inputs Ξ → ℝ)
    (simLaw : Inputs Ξ → Measure ℝ)
    (X : ∀ i : Fin m, ℕ → Ω → Ξ i) (n : ℕ → Fin m → ℕ)
    (θ : ℕ → ℝ) : Prop :=
  ∀ T : Finset (Fin m), ∀ ε : ℝ, 0 < ε →
    ∃ M : NNReal, ∀ᶠ k in atTop,
      P {ω | (M : ENNReal) <
        bootAvgENN (n := n k) (s := subsampleSize (θ k) (n k))
          (fun I => mu4 ψ simLaw (Fbar T I (dataSample X (n k) ω)))} ≤ ENNReal.ofReal ε

end

end SubsampVB.Consist


