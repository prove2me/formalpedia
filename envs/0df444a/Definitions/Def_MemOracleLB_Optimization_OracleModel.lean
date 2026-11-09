-- Prove2me | Definitions.Def_MemOracleLB_Optimization_OracleModel
-- name    : MemOracleLB_Optimization_OracleModel
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:34:59.221689+00:00
-- url     : https://prove2.me/theorems/26a81f2d-52fe-4382-a81d-d761e0929fde
-- title:
--   Adaptive membership-query algorithms, convex inputs and the hard pair
-- statement:
--   A randomized procedure is an action map from a known objective, finite Boolean answer history and seed to either a real query point or a real terminal output. For each objective and history it is measurable in the seed, with unrestricted objective dependence. The oracle is exact membership, including boundary points. Recursive finite histories determine the run, its queries and any terminal output. The query count is
--
--   $$T=\inf\{t\in\mathbb N:\text{the algorithm halts after }t\text{ queries}\}\in\mathbb N\cup\{\infty\}.$$
--
--   An empty halting set has infimum $\infty$, and nontermination has no output. A separate revealed-row procedure requires joint measurability in the public row and seed.
--
--   Using the published convex-body predicate, $\mathcal C_n(C)$ consists of compact convex bodies with nonempty interior and $B^n\subseteq K\subseteq Cn^{3/2}B^n$. The linear optimum is the supremum of $\langle c,x\rangle$ on $K$, attained for admissible inputs. Valid outputs are positive and meet either the factor-two or additive-$n$ guarantee.
--
--   For rows $R_i$, define $K_b(R)=\{x:|\langle R_i,x\rangle|\le1\ (i<n),\ |\langle R_n,x\rangle|\le bL\}$, with $b=1,3$. The first separating query lies in $K_3\setminus K_1$, has one-based index $\tau$, and has index $\infty$ when absent. The interface includes the unconditioned scaled-Gaussian row law, matrix operator norm, long vector $R^{-1}e_n$, and the exact good event of Lemma 4.1.
--
--   These definitions support arbitrary adaptive query lower bounds without a fixed budget or assumed termination.
-- source:
--   Santosh Vempala, STOC 2027 submission #365 (October 2026), §§1.1–1.3 and4, Definition4.2, PDF pp.2,4–5,19–21 (printed pp.1,3–4,18–20), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/365.pdf

import Mathlib
import Definitions.Def_CoveringDensity
import Definitions.Def_MemOracleLB_Optimization_Probability

open MeasureTheory ProbabilityTheory
open scoped ENNReal RealInnerProductSpace
noncomputable section

namespace MemOracleLB.Optimization

/-- General adaptive real membership-query procedure. Its input dependence is unrestricted. -/
structure OracleAlgorithm (n : ℕ) (Ω : Type*) [MeasurableSpace Ω] where
  action : E n → List Bool → Ω → Sum (E n) ℝ
  measurable_seed : ∀ c h, Measurable (action c h)

/-- Finite histories of the run. At time k, exactly k queries have been answered;
a halted run has no later history. -/
def runHistory {n : ℕ} (action : List Bool → Sum (E n) ℝ) (O : E n → Bool) :
    ℕ → Option (List Bool)
  | 0 => some []
  | k + 1 => do
      let h ← runHistory action O k
      match action h with
      | .inl q => some (h ++ [O q])
      | .inr _ => none

/-- The k+1-st query, if the run reaches it. -/
def queryAt {n : ℕ} (action : List Bool → Sum (E n) ℝ) (O : E n → Bool)
    (k : ℕ) : Option (E n) := do
  let h ← runHistory action O k
  match action h with
  | .inl q => some q
  | .inr _ => none

/-- A terminated output; nontermination has no output. -/
def Outputs {n : ℕ} (action : List Bool → Sum (E n) ℝ) (O : E n → Bool) (z : ℝ) : Prop :=
  ∃ k h, runHistory action O k = some h ∧ action h = Sum.inr z

/-- Number of queries before halting, infinity if the run never halts.
The infimum is in the complete lattice ENat, so the empty infimum is infinity. -/
def queryCount {n : ℕ} (action : List Bool → Sum (E n) ℝ) (O : E n → Bool) : ℕ∞ :=
  sInf {k | ∃ (t : ℕ) (h : List Bool) (z : ℝ), k = (t : ℕ∞) ∧
    runHistory action O t = some h ∧ action h = Sum.inr z}

/-- Exact closed-body membership, including boundary points. -/
def membershipOracle {n : ℕ} (K : Set (E n)) (x : E n) : Bool := by
  classical
  exact decide (x ∈ K)

/-- PDF p.2: B subset K subset C n^(3/2) B. -/
def InClass {n : ℕ} (C : ℝ) (K : Set (E n)) : Prop :=
  OAI.TranslativeCovering.ConvexBody K ∧ Metric.closedBall 0 1 ⊆ K ∧
    K ⊆ Metric.closedBall 0 (C * (n : ℝ) ^ (3 / 2 : ℝ))

/-- Used only on the nonempty compact class, where this supremum is attained. -/
def optimum {n : ℕ} (K : Set (E n)) (c : E n) : ℝ :=
  sSup ((fun x => ⟪c, x⟫) '' K)

def ValidOutput {n : ℕ} (K : Set (E n)) (c : E n) (z : ℝ) : Prop :=
  0 < z ∧ ((optimum K c / 2 ≤ z ∧ z ≤ optimum K c) ∨
    (optimum K c - n ≤ z ∧ z ≤ optimum K c))

def Succeeds {n : ℕ} {Ω : Type*} [MeasurableSpace Ω] (A : OracleAlgorithm n Ω)
    (K : Set (E n)) (c : E n) (ω : Ω) : Prop :=
  ∃ z, Outputs (fun h => A.action c h ω) (membershipOracle K) z ∧ ValidOutput K c z

def queries {n : ℕ} {Ω : Type*} [MeasurableSpace Ω] (A : OracleAlgorithm n Ω)
    (K : Set (E n)) (c : E n) (ω : Ω) : ℕ∞ :=
  queryCount (fun h => A.action c h ω) (membershipOracle K)

/-- The separate revealed-row model of Definition 4.2 and Lemma 4.3. -/
structure RevealedAlgorithm (n : ℕ) (Ω : Type*) [MeasurableSpace Ω] where
  action : E n → List Bool → Ω → Sum (E n) ℝ
  measurable_joint : ∀ h, Measurable (fun p : E n × Ω => action p.1 h p.2)

/-- PDF pp.4,20: b=1 or b=3 and L=ell*n. -/
def hardBody {m : ℕ} (R : Fin (m + 1) → E (m + 1)) (L b : ℝ) : Set (E (m + 1)) :=
  {x | (∀ i : Fin m, |⟪R i.castSucc, x⟫| ≤ 1) ∧ |⟪R (Fin.last m), x⟫| ≤ b * L}

/-- PDF p.20: read the first separating query off the K1 run, 1-based. -/
def separatingIndex {m : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (A : RevealedAlgorithm (m + 1) Ω) (L : ℝ)
    (R : Fin (m + 1) → E (m + 1)) (ω : Ω) : ℕ∞ :=
  sInf {t | ∃ (k : ℕ) (q : E (m + 1)), t = ((k + 1 : ℕ) : ℕ∞) ∧
    queryAt (fun h => A.action (R (Fin.last m)) h ω)
      (membershipOracle (hardBody R L 1)) k = some q ∧
    q ∈ hardBody R L 3 ∧ q ∉ hardBody R L 1}

/-- The Gaussian product law of the independent rows. -/
def matrixLaw (n : ℕ) : Measure (Fin n → E n) := Measure.pi (fun _ => scaledGaussian n)

def rowMatrix {n : ℕ} (R : Fin n → E n) : Matrix (Fin n) (Fin n) ℝ := fun i j => R i j

def matrixAction {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (x : E n) : E n :=
  WithLp.toLp 2 (M.mulVec (fun j => x j))

/-- A supremum of a bounded set in finite dimension; for n=0 its value is zero. -/
def matrixOpNorm {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  sSup {r | ∃ x : E n, ‖x‖ = 1 ∧ r = ‖matrixAction M x‖}

def longVector {m : ℕ} (R : Fin (m + 1) → E (m + 1)) : E (m + 1) :=
  matrixAction (rowMatrix R)⁻¹ (WithLp.toLp 2 (Pi.single (Fin.last m) 1))

/-- PDF p.19: the event H, without conditioning the Gaussian law. -/
def GoodEvent {m : ℕ} (C₀ : ℝ) : Set (Fin (m + 1) → E (m + 1)) :=
  {R | (∀ i, ‖R i‖ ≤ 2) ∧ matrixOpNorm (rowMatrix R)⁻¹ ≤ C₀ * (m + 1) ∧
    Real.sqrt (m + 1) / C₀ ≤ ‖longVector R‖ ∧
    ‖longVector R‖ ≤ C₀ * Real.sqrt (m + 1)}

end MemOracleLB.Optimization


