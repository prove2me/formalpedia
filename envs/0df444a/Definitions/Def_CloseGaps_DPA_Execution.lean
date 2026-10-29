-- Prove2me | Definitions.Def_CloseGaps_DPA_Execution
-- name    : CloseGaps_DPA_Execution
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-29T02:34:06.625896+00:00
-- url     : https://prove2.me/theorems/fefa4f91-aeda-4627-ab0f-fd9f21f6223e
-- title:
--   Partial DPA execution
-- statement:
--   Left-endpoint experiments, empirical choices, strict switching, asymmetric interval updates, virtual continuations and construction of the posted price rule. Undefined grid cardinalities produce no stage. Grid indices start at zero, and ties use the least tested index. Counts divided by n times the normalized duration estimate normalized base demand and are compared with x. Printed grid counts must equal positive integers exactly, without rounding. The deterministic-count reading and partial-construction obligations are declared in each theorem.
-- source:
--   Wang, Deng, and Ye (2014), Operations Research 62(2), 318–331, DOI 10.1287/opre.2013.1245, §4.2, Algorithm DPA and equations (9)–(27), pp. 322–324 (PDF 5–7)

import Definitions.Def_CloseGaps_DPA_Model
import Definitions.Def_CloseGaps_DPA_ControlledSales
import Definitions.Def_CloseGaps_DPA_Parameters

open MeasureTheory Set
noncomputable section
open scoped Classical

namespace CloseGaps.DPA

/-- Data from one complete virtual experimental stage; indices of grid points start at zero. -/
structure Stage where
  lo : ℝ
  hi : ℝ
  k : ℕ
  delta : ℝ
  startClock : ℝ
  counts : ℕ → ℕ
  endClock : ℝ
  bestU : ℕ
  bestC : ℕ
  deriving Inhabited

def Stage.grid (s : Stage) (j : ℕ) : ℝ := s.lo + j * ((s.hi - s.lo) / s.k)
def Stage.gap (s : Stage) : ℝ := (s.hi - s.lo) / s.k

def Stage.center (s : Stage) : ℝ := max (s.grid s.bestU) (s.grid s.bestC)

def Stage.switches (s : Stage) (n : ℝ) : Prop :=
  s.grid s.bestC > s.grid s.bestU + 2 * Real.sqrt (Real.log n) * s.gap

def poissonCount (E : Noise) (t : ℝ) : ℕ :=
  QueueingFundamentals.Foundations.countingProcess (fun (j : ℕ) (z : Noise) => z j) t E

/-- Finite argmax/min choose the least maximizing/minimizing grid index, without an empty default. -/
def leastMax (k : ℕ) (f : ℕ → ℝ) : Option ℕ := by
  classical
  exact if h : ∃ j, j < k ∧ ∀ l, l < k → f l ≤ f j then some (Nat.find h) else none

def leastMin (k : ℕ) (f : ℕ → ℝ) : Option ℕ := leastMax k (fun j => -f j)

/-- Counts are successive increments of the same Poisson clock, at the rates of the selected
prices. Failed cardinalities, zero durations and empty intervals have no output. -/
def makeStage (lam : ℝ → ℝ) (n x lo hi τ κ clock : ℝ) (E : Noise) : Option Stage := by
  classical
  let k := ⌊κ⌋₊
  let δ := τ / k
  let p := fun j : ℕ => lo + j * ((hi - lo) / k)
  let v := fun j : ℕ => clock + ∑ l ∈ Finset.range j, n * lam (p l) * δ
  let y := fun j : ℕ => poissonCount E (v (j + 1)) - poissonCount E (v j)
  exact if (k : ℝ) = κ ∧ 0 < k ∧ 0 < τ ∧ lo ≤ hi ∧
      (∀ j, j < k → 0 ≤ lam (p j)) then
    (leastMax k (fun j => p j * (y j : ℝ) / (n * δ))).bind fun bu =>
      (leastMin k (fun j => |(y j : ℝ) / (n * δ) - x|)).map fun bc =>
        ⟨lo, hi, k, δ, clock, y, v k, bu, bc⟩
  else none

/-- Full virtual u-learning path, continued after switching or stockout for §5's variables. -/
def uStage (a : Market) (lam : ℝ → ℝ) (n x : ℝ) (E : Noise) : ℕ → Option Stage
  | 0 => none
  | i + 1 => if i = 0 then makeStage lam n x a.lo a.hi (tauU n 1) (kappaU n 1) 0 E
    else (uStage a lam n x E i).bind fun s =>
      makeStage lam n x
        (max a.lo (s.center - Real.log n * s.gap / 3))
        (min a.hi (s.center + 2 * Real.log n * s.gap / 3))
        (tauU n (i + 1)) (kappaU n (i + 1)) s.endClock E

/-- c-learning branch after virtual u-stage l, restarting from the original interval. -/
def cStage (a : Market) (lam : ℝ → ℝ) (n x : ℝ) (E : Noise) (l : ℕ) : ℕ → Option Stage
  | 0 => none
  | i + 1 => if i = 0 then (uStage a lam n x E l).bind fun s =>
      makeStage lam n x a.lo a.hi (tauC n 1) (kappaC n 1) s.endClock E
    else (cStage a lam n x E l i).bind fun s =>
      makeStage lam n x
        (max a.lo (s.grid s.bestC - Real.log n * s.gap / 2))
        (min a.hi (s.grid s.bestC + Real.log n * s.gap / 2))
        (tauC n (i + 1)) (kappaC n (i + 1)) s.endClock E

/-- The deterministic stage-count notation used by §5. Existence is asserted, never assumed,
in the mission statements. Actual truncated widths enter the stopping tests. -/
structure StageCounts where
  Nu : ℕ
  Nc : ℕ

def leastStopU (n : ℝ) (S : ℕ → Option Stage) (N : ℕ) : Prop :=
  1 ≤ N ∧ (∃ s, S N = some s ∧ s.gap ^ 2 * Real.sqrt (Real.log n) < tauU n 1) ∧
  ∀ i, 1 ≤ i → i < N → ∃ s, S i = some s ∧
    ¬ s.gap ^ 2 * Real.sqrt (Real.log n) < tauU n 1

def leastStopC (n : ℝ) (S : ℕ → Option Stage) (N : ℕ) : Prop :=
  1 ≤ N ∧ (∃ s, S N = some s ∧ s.gap * Real.sqrt (Real.log n) < tauC n 1) ∧
  ∀ i, 1 ≤ i → i < N → ∃ s, S i = some s ∧
    ¬ s.gap * Real.sqrt (Real.log n) < tauC n 1

def switchIndex (a : Market) (lam : ℝ → ℝ) (n x : ℝ) (E : Noise) (N : StageCounts) : ℕ := by
  classical
  let A := {i : ℕ | 1 ≤ i ∧ i ≤ N.Nu ∧ ∃ s, uStage a lam n x E i = some s ∧ s.switches n}
  exact if A.Nonempty then sInf A else N.Nu + 1

/-- Genuine partial construction: every required grid and both stopping minima must exist.
Virtual c branches share the past of their u-prefix and the same future Poisson driver. -/
def completeTrace (a : Market) (lam : ℝ → ℝ) (n x : ℝ) (N : StageCounts) (E : Noise) : Prop :=
  leastStopU n (uStage a lam n x E) N.Nu ∧
  (∀ i, 1 ≤ i → i ≤ N.Nu → (uStage a lam n x E i).isSome) ∧
  (∀ l, 1 ≤ l → l ≤ N.Nu →
    leastStopC n (cStage a lam n x E l) N.Nc ∧
    ∀ i, 1 ≤ i → i ≤ N.Nc → (cStage a lam n x E l i).isSome)

/-- All experimental postings, in normalized physical time, on a particular branch. -/
def experimentalPosting (a : Market) (lam : ℝ → ℝ) (n x : ℝ) (E : Noise)
    (N : StageCounts) (t p : ℝ) : Prop :=
  let l := switchIndex a lam n x E N
  (∃ i s j, 1 ≤ i ∧ i ≤ min l N.Nu ∧ uStage a lam n x E i = some s ∧
    j < s.k ∧ timeU n (i - 1) + j * s.delta ≤ t ∧
    t < timeU n (i - 1) + (j + 1) * s.delta ∧ p = s.grid j) ∨
  (l ≤ N.Nu ∧ ∃ i s j, 1 ≤ i ∧ i ≤ N.Nc ∧ cStage a lam n x E l i = some s ∧
    j < s.k ∧ timeU n l + timeC n (i - 1) + j * s.delta ≤ t ∧
    t < timeU n l + timeC n (i - 1) + (j + 1) * s.delta ∧ p = s.grid j)

def finalPosting (a : Market) (lam : ℝ → ℝ) (n x : ℝ) (E : Noise)
    (N : StageCounts) (t p : ℝ) : Prop :=
  let l := switchIndex a lam n x E N
  (l = N.Nu + 1 ∧ timeU n N.Nu ≤ t ∧ ∃ s, uStage a lam n x E N.Nu = some s ∧
    p = s.center + 2 * Real.sqrt (Real.log n) * s.gap) ∨
  (l ≤ N.Nu ∧ timeU n l + timeC n N.Nc ≤ t ∧
    ∃ s, cStage a lam n x E l N.Nc = some s ∧ p = s.grid s.bestC)

/-- Actual prices are determined from observed histories by the one common rule π.
Postings are compared before stockout; virtual observations afterwards are only analytical.
Only postings within the selling horizon are compared; a virtual continuation does not
require that the physical policy reach the final phase. -/
def generated (a : Market) (lam : ℝ → ℝ) (n x T : ℝ)
    (π : PriceRule) (N : StageCounts) : Prop :=
  let b := normalizedMarket a
  let f := normalizedDemand a T lam
  (∀ᵐ E ∂clockLaw, completeTrace b f n x N E) ∧
  (∀ᵐ E ∂clockLaw,
    ∀ t ∈ Ico 0 T, salesBefore π lam n x E t < ⌊n * x⌋₊ →
      ∃ p, postedPrice π lam n x E t = some ((a.hi - a.lo) * p) ∧
        (experimentalPosting b f n x E N (t / T) p ∨ finalPosting b f n x E N (t / T) p))

/-- Inventory feasibility and meaningful stochastic revenue, separate from the algorithm. -/
def admissible (a : Market) (lam : ℝ → ℝ) (n x T : ℝ) (π : PriceRule) : Prop :=
  (∀ᵐ E ∂clockLaw, ∀ t ∈ Icc 0 T, a.feasible (postedPrice π lam n x E t)) ∧
  Measurable (pathRevenue π lam n x T) ∧ Integrable (pathRevenue π lam n x T) clockLaw ∧
  (∀ᵐ E ∂clockLaw, ∀ t ∈ Icc 0 T, (salesBefore π lam n x E t : ℝ) ≤ n * x)

end CloseGaps.DPA


