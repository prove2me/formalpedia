-- Prove2me | Definitions.Def_PrivateAgnosticHalfspace_Gaussian_Supplement_LogConcave
-- name    : PrivateAgnosticHalfspace_Gaussian_Supplement_LogConcave
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T03:07:43.917346+00:00
-- url     : https://prove2.me/theorems/b1a4f305-1ab8-46b9-a2eb-b53146be63f7
-- title:
--   Known log-concave marginals, polynomial features and Appendix D.1 learner
-- statement:
--   A log-concave marginal on $\mathbb R^d$ is a Borel probability measure with a measurable nonnegative log-concave density. The published power-form log-concavity predicate permits zero density outside a convex support; its convex extended potential is $-\log f$ on $f>0$ and $+\infty$ elsewhere. Full dimensionality excludes concentration on a proper affine hyperplane. No Gaussian, isotropic, smooth or everywhere-positive density assumption is included.
--
--   For degree $p$, form the actual monomial vector $m_p$ and population Gram matrix $G_p=E[m_p m_p^\top]$. Public moment Gram–Schmidt in lexicographic monomial order gives a matrix $B_p$ and features $\psi_p=B_p m_p$. This is the equivalent orthonormal-basis choice permitted on pp.28–29. Its existence, nondegeneracy and orthonormality are asserted by the theorem, rather than assumed as input certificates. Its pointwise norm agrees with the inverse-square-root basis, so the exact threshold remains
--   $$T=\min\left\{t>0:E_\mu\left[(1-t/\|\psi_p(X)\|)_+\right]\le c\alpha\right\}.$$
--
--   The modified Algorithm 1 uses $p=\lceil e^{C/\alpha}\rceil$, clipping $T\psi_p/\max(T,\|\psi_p\|)$, coefficient radius $R_0$, independent private regression runs, midpoint thresholds and validation. An optimizer takes only public features, radius and privacy parameters and the observed sample; its type contains no privacy or accuracy promise. The public training size is the least integer at least two satisfying (27); $k,M,m$ retain (14a),(14c).
--
--   The output is an actual coefficient vector and scalar threshold. Separate execution decoding supports radius $R_0$. Concrete public basis/T programs run on a finite public description, independent of the sample and conditional labels. Their actual termination, outputs and work bound enter only the conditional runtime clause; the theorem's privacy, sample and accuracy conclusions do not assume them. All costs of these preprocessing runs and of the subsequent sample processing are counted.
-- source:
--   Giorgio Racca, Amartya Sanyal, Vikrant Singhal, Privacy for Free in Efficient Agnostic Halfspace Learning, STOC 2027 submission #1006 (October 2026), canonical held submission (not a proceedings-acceptance claim), pp.23,28–31, Theorem D.1, Eqs. (22),(27), Appendix D.1

import Definitions.Def_PrivateAgnosticHalfspace_Gaussian_Supplement_Core
import Definitions.Def_LogConcaveOn

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
set_option autoImplicit false

namespace PrivateAgnosticHalfspace.Gaussian.Supplement

noncomputable section

/-- General log-concave density object, allowing zeros and convex supports. The power-form
predicate is the published one, with no isotropy, smoothness or strict positivity bundled in.
Its extended convex potential is -log f on {f>0}, and +infinity elsewhere. -/
def IsLogConcaveMarginal (d : ℕ) (μ : Measure (Vec d)) : Prop :=
  IsProbabilityMeasure μ ∧ ∃ f : Vec d → ℝ,
    Measurable f ∧ ConvexOptimization.LogConcaveOn Set.univ f ∧
    μ = volume.withDensity (fun x => ENNReal.ofReal (f x))

def densityPotential {d : ℕ} (f : Vec d → ℝ) (x : Vec d) : EReal :=
  if 0 < f x then (-(Real.log (f x)) : ℝ) else ⊤

/-- The marginal is not supported on any proper affine hyperplane. -/
def FullDimensional (d : ℕ) (μ : Measure (Vec d)) : Prop :=
  ∀ w : Vec d, w ≠ 0 → ∀ t : ℝ, μ {x | inner ℝ w x = t} ≠ 1

def monomials (d p : ℕ) (x : Vec d) : Coeff d p :=
  WithLp.toLp 2 fun κ => ∏ i, x i ^ (κ.val i).val

def gram (d p : ℕ) (μ : Measure (Vec d)) : Matrix (Index d p) (Index d p) ℝ :=
  fun i j => ∫ x, monomials d p x i * monomials d p x j ∂μ

/-- Moment inner product on coefficient vectors. -/
def gramInner {d p : ℕ} (G : Matrix (Index d p) (Index d p) ℝ)
    (v w : Coeff d p) : ℝ := ∑ i, ∑ j, v i * G i j * w j

/-- Public moment Gram--Schmidt in lexicographic monomial order, an equivalent
orthonormal polynomial basis expressly allowed on pp.28--29. It requires only finite
arithmetic and square roots after the moments are supplied. -/
def basisRows (d p : ℕ) (μ : Measure (Vec d)) : List (Coeff d p) :=
  let G := gram d p μ
  let indices := (Finset.univ : Finset (Index d p)).toList.mergeSort
    (fun i j => indexCode i ≤ indexCode j)
  indices.foldl (fun bs i =>
    let v : Coeff d p := WithLp.toLp 2 (Pi.single i 1)
    let residual := v - (bs.map fun b => (gramInner G b v) • b).sum
    bs ++ [(Real.sqrt (gramInner G residual residual))⁻¹ • residual]) []

def basisMatrix (d p : ℕ) (μ : Measure (Vec d)) : Matrix (Index d p) (Index d p) ℝ :=
  fun i j => ((basisRows d p μ).getD (indexRank i) 0) j

def marginalFeatures (d p : ℕ) (μ : Measure (Vec d)) (x : Vec d) : Coeff d p :=
  WithLp.toLp 2 ((basisMatrix d p μ).mulVec (monomials d p x))

def clippingDeficit (d p : ℕ) (μ : Measure (Vec d)) (t : ℝ) : ℝ :=
  ∫ x, max (1 - t / ‖marginalFeatures d p μ x‖) 0 ∂μ

def thresholds22 (d p : ℕ) (μ : Measure (Vec d)) (c α : ℝ) : Set ℝ :=
  {t | 0 < t ∧ clippingDeficit d p μ t ≤ c * α}

def marginalThreshold (d p : ℕ) (μ : Measure (Vec d)) (c α : ℝ) : ℝ :=
  sInf (thresholds22 d p μ c α)

structure MarginalConstants where
  degree : ℝ
  accuracy : ℝ
  coefficientRadius : ℝ
  schedule : ℝ

/-- Sample-only optimizer for a public feature map and public coefficient radius. No
privacy, utility or cost assertion occurs in this type. The theorem chooses it uniformly. -/
abbrev MarginalOptimizer := ∀ d p n : ℕ, (Vec d → Coeff d p) →
  ℝ → ℝ → ℝ → (Fin n → Example d) → ProbabilityMeasure (Coeff d p)

def marginalDegree (c : MarginalConstants) (α : ℝ) : ℕ := ⌈Real.exp (c.degree / α)⌉₊

def marginalCondition (c : MarginalConstants) (d p : ℕ) (T α ε δ : ℝ) (n₀ : ℕ) : Prop :=
  2 ≤ n₀ ∧ c.schedule *
    (c.coefficientRadius * T * Real.sqrt ((featureDimension d p : ℝ) * Real.log (1 / δ)) /
      (ε * n₀) + c.coefficientRadius * Real.sqrt ((featureDimension d p : ℝ) / n₀)) ≤ c.accuracy * α

def marginalTrainingSize (c : MarginalConstants) (d p : ℕ) (T α ε δ : ℝ) : ℕ :=
  firstSize (marginalCondition c d p T α ε δ)

def marginalSize (c : MarginalConstants) (d p : ℕ) (T α β ε δ : ℝ) : ℕ :=
  repetitions β * marginalTrainingSize c d p T α ε δ +
    validationSize c.schedule α β ε (repetitions β) (thresholds c.schedule α)

abbrev MarginalOutput (d p : ℕ) := Coeff d p × ℝ

def marginalDecode {d p : ℕ} (φ : Vec d → Coeff d p) (o : MarginalOutput d p)
    (x : Vec d) : Bool := sign (inner ℝ o.1 (φ x) - o.2)

/-- Appendix D.1's Algorithm 1, with radius R0, a marginal-adapted feature map and threshold.
It is distinct from the immutable unit-ball Gaussian algorithmLaw. -/
def marginalLaw (O : MarginalOptimizer) (c : MarginalConstants) (d p : ℕ)
    (φ : Vec d → Coeff d p) (T α β ε δ : ℝ) (S : List (Example d)) : Measure (MarginalOutput d p) :=
  let k := repetitions β
  let M := thresholds c.schedule α
  let n₀ := marginalTrainingSize c d p T α ε δ
  let m := validationSize c.schedule α β ε k M
  let bounded := fun x => radial T (φ x)
  let train := Measure.pi fun j : Fin k =>
    (O d p n₀ bounded c.coefficientRadius ε δ
      (fun i => S[j.val * n₀ + i.val]!) : Measure (Coeff d p))
  train.bind fun vs =>
    let hs := List.ofFn fun jl : Fin (k * M) =>
      let j : Fin k := ⟨jl.val / M, by
        have hM : 0 < M := by nlinarith [jl.isLt]
        exact (Nat.div_lt_iff_lt_mul hM).mpr (by simpa [Nat.mul_comm] using jl.isLt)⟩
      (vs j, -1 + (2 * ((jl.val % M : ℕ) : ℝ) + 1) / M)
    select hs (marginalDecode bounded) ε (block S (k * n₀) m)

/-- Actual output decoding and law equality for the radius-R0 improper learner. -/
def readMarginalOutput (d p : ℕ) (s : PolySampIso.State) : MarginalOutput d p :=
  (readCoefficients d p (outputMemory s), outputMemory s (Fintype.card (Index d p)))

def marginalInput (c : MarginalConstants) (d p : ℕ)
    (B : Matrix (Index d p) (Index d p) ℝ) (T α β ε δ : ℝ)
    (S : List (Example d)) : ℕ → ℝ :=
  input ([(d : ℝ), p, S.length, α, β, ε, δ, T, c.degree, c.accuracy, c.coefficientRadius, c.schedule] ++
    List.ofFn (fun j : Fin ((Fintype.card (Index d p)) ^ 2) =>
      ∑ i : Index d p, ∑ l : Index d p,
        if j.val = indexRank i * Fintype.card (Index d p) + indexRank l then B i l else 0)) S


/-- Concrete public preprocessing routines. Their finite public description is independent
of samples and conditional labels. Actual runs must halt and return the prescribed matrix/T.
This predicate is used only in the conditional runtime conclusion, never for accuracy. -/
def PublicComputes (build threshold : Code) (info : List ℝ) (d p : ℕ)
    (B : Matrix (Index d p) (Index d p) ℝ) (T α : ℝ) (Q : ℝ) (s : ℕ) : Prop :=
  Admissible build ∧ Admissible threshold ∧
  ∀ ω : PolySampIso.Streams,
    let budget := ⌊Q * (featureDimension d p + 1 : ℝ) ^ s⌋₊
    let b := run build (fun i => ([ (d : ℝ), p, α ] ++ info).getD i 0) ω (budget + 1)
    let t := run threshold (fun i => ([ (d : ℝ), p, α ] ++ info).getD i 0) ω (budget + 1)
    b.halted = true ∧ t.halted = true ∧ b.work + t.work ≤ budget ∧
    (∀ i j, outputMemory b (indexRank i * Fintype.card (Index d p) + indexRank j) = B i j) ∧
    outputMemory t 0 = T

/-- The pipeline charges actual preprocessing and subsequent sample processing. -/
def ImplementsMarginal (code build threshold : Code) (info : List ℝ) (fuel cost : ℕ)
    (d p : ℕ) (a : ℕ → ℝ) (α : ℝ) (preBudget : ℕ)
    (ν : Measure (MarginalOutput d p)) : Prop :=
  Admissible code ∧
  (∀ ω,
    let b := run build (fun i => ([ (d : ℝ), p, α ] ++ info).getD i 0) ω (preBudget + 1)
    let t := run threshold (fun i => ([ (d : ℝ), p, α ] ++ info).getD i 0) ω (preBudget + 1)
    let result := run code a ω fuel
    b.halted = true ∧ t.halted = true ∧ result.halted = true ∧ b.work + t.work + result.work ≤ cost) ∧
  Measurable (fun ω => readMarginalOutput d p (run code a ω fuel)) ∧
  PolySampIso.tape.map (fun ω => readMarginalOutput d p (run code a ω fuel)) = ν

end
end PrivateAgnosticHalfspace.Gaussian.Supplement


