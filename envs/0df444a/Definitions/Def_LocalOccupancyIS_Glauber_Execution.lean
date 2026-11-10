-- Prove2me | Definitions.Def_LocalOccupancyIS_Glauber_Execution
-- name    : LocalOccupancyIS_Glauber_Execution
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-09T10:58:55.462739+00:00
-- url     : https://prove2.me/theorems/e2b19fe0-0206-451a-a13b-3347d53108e2
-- title:
--   Largest-visited output and counted independent-run amplification
-- statement:
--   A heat-bath proposal changes a single spin, using an independent Bernoulli-$p$ coin if its neighbors are unoccupied. The running record is the larger of its previous value and the current configuration, with the earlier record kept on ties. The augmented transition matrix gives the joint current-state and record law. Each repetition resets to the supplied initial independent set and uses a fresh run; its output is compared with the global record.
--
--   For desired size error $\varepsilon\in(0,1)$ and failure probability $\delta\in(0,1)$, the procedure computes
--
--   $$T=\max\{1,\lceil2C_3^2H_\lambda/\varepsilon^2\rceil\},\qquad R=\max\{1,\lceil(2\Gamma/\varepsilon)\log(1/\delta)\rceil\}.$$
--
--   Its output is the largest state among these independent trajectories. Charges count graph input reading, at most $\Delta$ neighbor checks per update, spin reads and writes, two ideal random draws per update, size comparisons, record copying and resets. The cost is the sum of these computed operation counts. No independent-set oracle or efficient-success witness is an input. The shared finite conclusion predicate packages the three-sweep certificate, $\kappa\le3\Delta$, the exact expected-size inequality, and the one-run and amplified probability assertions; it does not enter the algorithm's definition.
-- source:
--   Ewan Davies, Brian Tan, STOC 2027 submission #982 (October 2026), Remark 2 and proof of Corollary 4, p. 13–20; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/982.pdf#page=13

import Definitions.Def_LocalOccupancyIS_Glauber_Parameters

open scoped BigOperators

namespace LocalOccupancyIS.Glauber
noncomputable section
variable {V : Type} [Fintype V] [DecidableEq V]

/-- The actual Boolean heat-bath update with a fresh proposal coin. -/
def updateSpin (G : SimpleGraph V) [DecidableRel G.Adj] (σ : V → Bool) (u : V) (coin : Bool) : V → Bool :=
  Function.update σ u (if ∀ v ∈ G.neighborFinset u, σ v = false then coin else false)

/-- Keep the earlier state on ties. -/
def larger (G : SimpleGraph V) (I J : State G) : State G :=
  if size I.val < size J.val then J else I

/-- A real step of ordinary Glauber dynamics, augmented by the largest state seen. -/
def recordKernel (G : SimpleGraph V) [DecidableRel G.Adj] (lam : ℝ) :
    Matrix (State G × State G) (State G × State G) ℝ := fun x y =>
  if y.2 = larger G x.2 y.1 then K G lam x.1 y.1 else 0

/-- Law of the largest state visited, including time zero and the final endpoint. -/
def runLargest (G : SimpleGraph V) [DecidableRel G.Adj] (lam : ℝ) (I : State G) (T : ℕ) : State G → ℝ :=
  fun B => ∑ J, (recordKernel G lam ^ T) (I,I) (J,B)

/-- Reset to I, execute a fresh run, and compare its output with the previous record. -/
def repetitionKernel (G : SimpleGraph V) [DecidableRel G.Adj] (lam : ℝ)
    (I : State G) (T : ℕ) : Matrix (State G) (State G) ℝ := fun B C =>
  ∑ A : State G, if C = larger G B A then runLargest G lam I T A else 0

def amplifiedLaw (G : SimpleGraph V) [DecidableRel G.Adj] (lam : ℝ)
    (I : State G) (T R : ℕ) : State G → ℝ :=
  push (point I) (repetitionKernel G lam I T ^ R)

def success (G : SimpleGraph V) [DecidableRel G.Adj] (ν : State G → ℝ) (a : ℝ) : ℝ :=
  ∑ I : State G, if a ≤ size I.val then ν I else 0

/-- Remark 2 run horizon (expected error ε/2) and independent repetitions. -/
def horizon (n Δ : ℕ) (lam c ε : ℝ) : ℕ :=
  max 1 ⌈2 * cThree Δ lam c ^ 2 * entropyBound n lam / ε ^ 2⌉₊
def repeats (Δ : ℕ) (lam c ε δ : ℝ) : ℕ :=
  max 1 ⌈(2 * Gamma Δ lam c / ε) * Real.log (1/δ)⌉₊

/-- No success or efficiency witness is an argument to this procedure. -/
def algorithm (G : SimpleGraph V) [DecidableRel G.Adj] (Δ t : ℕ) (b ε δ : ℝ) (I : State G) : State G → ℝ :=
  let lam := fugacity Δ t b
  let c := correction Δ t b
  amplifiedLaw G lam I (horizon (Fintype.card V) Δ lam c ε) (repeats Δ lam c ε δ)

/-- Separate charges for local graph operations and record maintenance. -/
structure Charges where
  adjacencyChecks : ℕ
  spinReads : ℕ
  spinWrites : ℕ
  randomDraws : ℕ
  comparisons : ℕ
  recordCopies : ℕ
  resets : ℕ
  deriving Inhabited

/-- A conservative worst-case execution charge, from its computed loop counts.
The local update scans at most Δ neighbors; record copies/reset cost n per iteration/run. -/
def executionCharges (n Δ T R : ℕ) : Charges where
  adjacencyChecks := n^2 + R*T*Δ
  spinReads := R*T*(Δ+2)
  spinWrites := R*T
  randomDraws := 2*R*T
  comparisons := R*T + R
  recordCopies := n*(R*T+R+1)
  resets := n*R

def Charges.total (c : Charges) : ℕ :=
  c.adjacencyChecks+c.spinReads+c.spinWrites+c.randomDraws+c.comparisons+c.recordCopies+c.resets

def algorithmCost (n Δ t : ℕ) (b ε δ : ℝ) : ℕ :=
  (executionCharges n Δ
    (horizon n Δ (fugacity Δ t b) (correction Δ t b) ε)
    (repeats Δ (fugacity Δ t b) (correction Δ t b) ε δ)).total

/-- Two and three repetitions of the same fixed neighborhood order. -/
def threeWords (w : V → List V) : V → List V := fun u => w u ++ w u ++ w u
def threePrefixes (w : V → List V) : V → List ℕ := fun u => [2*(w u).length,3*(w u).length]

/-- Everything finite asserted for the chosen parameters; all guarantees are conclusions. -/
def FiniteConclusion (G : SimpleGraph V) [DecidableRel G.Adj] (Δ : ℕ)
    (lam c : ℝ) (w : V → List V) : Prop :=
  let z := optimizer Δ lam c
  let β := beta lam z
  let γ := gamma c z
  0 < lam ∧ 0 < β ∧ 0 < γ ∧
  PrefixCertificate G lam β γ 0 (threeWords w) (threePrefixes w) ∧
  occurrences (threeWords w) ≤ 3*Δ ∧
  (∀ I : State G, ∀ ε : ℝ, 0 < ε → ε < 1 → ∀ T : ℕ, 1 ≤ T →
    cThree Δ lam c ^ 2 * entropyBound (Fintype.card V) lam / (2*ε^2) ≤ T →
      timeMean G lam (point I) T ≥ (1-ε)*Fintype.card V/Gamma Δ lam c) ∧
  (∀ I : State G, ∀ ε δ : ℝ, 0 < ε → ε < 1 → 0 < δ → δ < 1 →
    let T := horizon (Fintype.card V) Δ lam c ε
    let R := repeats Δ lam c ε δ
    MarkovMixing.IsDist (amplifiedLaw G lam I T R) ∧
    success G (runLargest G lam I T) ((1-ε)*Fintype.card V/Gamma Δ lam c) ≥ ε/(2*Gamma Δ lam c) ∧
    success G (amplifiedLaw G lam I T R) ((1-ε)*Fintype.card V/Gamma Δ lam c) ≥ 1-δ)

end
end LocalOccupancyIS.Glauber


