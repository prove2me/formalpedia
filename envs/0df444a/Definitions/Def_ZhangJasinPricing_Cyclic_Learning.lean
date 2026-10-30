-- Prove2me | Definitions.Def_ZhangJasinPricing_Cyclic_Learning
-- name    : ZhangJasinPricing_Cyclic_Learning
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-29T06:59:05.162445+00:00
-- url     : https://prove2.me/theorems/1babc203-58cd-4f7d-957d-81c7aba72278
-- title:
--   Initialization and the complete OLD and OLT period recursions
-- statement:
--   Initialization is a finite deterministic list of prescribed parameter experiments, covering every parameter and permitting repeated tests. A static test posts p_M and then p_i. A drop test posts p_M, then ℓ copies of p_i, then p_j. Each high-price observation is counted as an incidental single-price sample; each final drop observation is counted for its drop parameter. Reset-price observations are retained in total revenue but not reused as parameter samples. A final p_M period supplies the empty relevant start. The complete schedule, its length, its initial counts, and their maximum Q are explicit functions of this test list; no arbitrary idle periods or accurate-estimate assumption is allowed.
--
--   The state stores observed price/sales/revenue history, each list of actual revenue samples, the current word and position, episode snapshots, the cycle counter initially one, and the clearing count initially zero. At each boundary it computes the sample mean plus √(8 log n(c)/q), calls the appropriate DP, and selects a maximizing word by the measurable tie rule. If the new last price is lower, it posts one clearing price, updates the specified drop sample and clearing count, then starts the episode. Otherwise it starts immediately. Every played position updates exactly the source's single-price or memory-indexed drop sample. It repeats complete cycles until a used counter doubles relative to the episode-start count. The cycle counter advances once per completed cycle. A run of length T has exactly T observed periods, so its total revenue includes initialization, clearing, and any partial final cycle. Signed regret is expected total revenue divided by T minus the full-class benchmark, preserving the printed sign.
--
--   Allowing repeated targeted tests in OLT generalizes its printed once-per-parameter initialization; the once-only covering lists are included. OLD already says at least once. The prescribed test-block and final-reset conventions are the disclosed initialization reading.
-- source:
--   Zhang and Jasin (2021), DOI 10.1287/msom.2021.0979, supplied 34-page artifact, §§3–6, p. 13 (PDF p. 13)

import Definitions.Def_ZhangJasinPricing_Cyclic_DynamicPrograms
open MeasureTheory
open scoped BigOperators
open scoped Classical
noncomputable section

namespace ZhangJasinPricing.Cyclic
abbrev Observation := ℕ × ℝ × ℝ
abbrev TestPeriod := ℕ × Option Parameter
/-- Each initialization block is a prescribed test, never an idle delay.
The list may repeat tests, as allowed by 'at least once'. -/
structure Initialization (M K : ℕ) where
  tests : List Parameter
  valid : ∀ a ∈ tests, a ∈ parameters M K
  covers : ∀ a ∈ parameters M K, a ∈ tests

def testBlock (M : ℕ) (a : Parameter) : List TestPeriod :=
  [(M-1,none)] ++
  (if a.1 = a.2.1 then [(a.1,some (a.1,a.1,0))]
   else List.replicate a.2.2 (a.1,some (a.1,a.1,0)) ++ [(a.2.1,some a)])

def initialSchedule {M K : ℕ} (init : Initialization M K) : List TestPeriod :=
  init.tests.flatMap (testBlock M) ++ [(M-1,none)]

/-- Incidental observations at the high price are counted. Reset-price observations
are retained in revenue but not reused as parameter samples. -/
def initialCount {M K : ℕ} (init : Initialization M K) (a : Parameter) : ℕ :=
  ((initialSchedule init).filter (fun x => x.2 = some a)).length

def initialQ {M K : ℕ} (init : Initialization M K) : ℕ :=
  (parameters M K).sup (initialCount init)

structure Episode where
  word : Word
  start : ℕ
  counts : Parameter → ℕ
  averages : Parameter → ℝ
  cycleCounter : ℕ

structure LearningState where
  observations : List Observation := []
  samples : Parameter → List ℝ := fun _ => []
  word : Word := []
  offset : ℕ := 0
  boundary : Bool := true
  afterClearing : Bool := false
  episodes : List Episode := []
  cycles : ℕ := 1
  clearing : ℕ := 0

def sampleCount (s : LearningState) (a : Parameter) : ℕ := (s.samples a).length

def sampleAverage (s : LearningState) (a : Parameter) : ℝ :=
  (s.samples a).sum / sampleCount s a

def optimistic (s : LearningState) (a : Parameter) : ℝ :=
  sampleAverage s a + Real.sqrt (8 * Real.log s.cycles / sampleCount s a)

/-- Three coordinates per past observation; future coordinates are zero. -/
def observedHistory (s : LearningState) (n : ℕ) : ℝ :=
  if n = 0 then s.observations.length else
    let j := n-1
    let o := s.observations[j/3]?.getD (0,0,0)
    if j/3 < s.observations.length then
      if j%3 = 0 then o.1 else if j%3 = 1 then o.2.1 else o.2.2
    else 0

def observationParameter (mode : Mode) (K : ℕ) (p : ℕ → ℝ) (w : Word) (pos : ℕ) : Parameter :=
  let i := w[pos]?.getD 0
  let j := w[pos-1]?.getD 0
  if pos = 0 ∨ p j ≤ p i then (i,i,0)
  else (j,i,min (match mode with | .decreasing => pos | .threshold => pos - threshold p w (pos+1)) K)

def usedParameters (mode : Mode) (K : ℕ) (p : ℕ → ℝ) (w : Word) : List Parameter :=
  (List.range w.length).map (observationParameter mode K p w)

def observe {Ω : Type} [MeasurableSpace Ω] (D : Model Ω) (ω : Ω)
    (s : LearningState) (i : ℕ) (a : Option Parameter) : LearningState :=
  let t := s.observations.length
  let prices := fun u => if u < t then (s.observations[u]?.getD (0,0,0)).1 else i
  let sales := demand D (fun u j k => D.cohort u j k ω) prices t
  let r := D.price i * sales
  {s with observations := s.observations ++ [(i,sales,r)]
          samples := fun b => if a = some b then s.samples b ++ [r] else s.samples b}

def beginEpisode (s : LearningState) (w : Word) : LearningState :=
  let ep : Episode := {
    word := w
    start := s.observations.length
    counts := sampleCount s
    averages := sampleAverage s
    cycleCounter := s.cycles }
  {s with
    word := w
    offset := 0
    boundary := false
    afterClearing := false
    episodes := s.episodes ++ [ep]}

def playPosition {Ω : Type} [MeasurableSpace Ω] (D : Model Ω) (mode : Mode)
    (ω : Ω) (s : LearningState) : LearningState :=
  let a := observationParameter mode D.K D.price s.word s.offset
  let s' := observe D ω s (s.word[s.offset]?.getD 0) (some a)
  if s.offset+1 < s.word.length then {s' with offset := s.offset+1}
  else
    let e := s.episodes.getLastD {
      word := []
      start := 0
      counts := fun _ => 0
      averages := fun _ => 0
      cycleCounter := 1 }
    let doubled := (usedParameters mode D.K D.price s.word).any
      (fun b => decide (2 * e.counts b ≤ sampleCount s' b))
    {s' with offset := 0, cycles := s.cycles+1, boundary := doubled}

def learningStep {Ω : Type} [MeasurableSpace Ω] (D : Model Ω) (mode : Mode)
    (init : Initialization D.M D.K) (tie : TieRule) (ω : Ω) (s : LearningState) : LearningState :=
  let t := s.observations.length
  if t < (initialSchedule init).length then
    let x := (initialSchedule init)[t]?.getD (0,none)
    observe D ω s x.1 x.2
  else if s.afterClearing then playPosition D mode ω (beginEpisode s s.word)
  else if s.boundary then
    let w := (selectPlan tie (observedHistory s)
      (dpOptions mode D.M D.K (searchBound mode D.M D.K) (optimistic s))).1
    if s.word ≠ [] ∧ D.price (w.getLastD 0) < D.price (s.word.getLastD 0) then
      let a := (s.word.getLastD 0,w.getLastD 0,min s.word.length D.K)
      let s' := observe D ω s (w.getLastD 0) (some a)
      {s' with
        word := w
        offset := 0
        boundary := false
        afterClearing := true
        clearing := s.clearing+1}
    else playPosition D mode ω (beginEpisode s w)
  else playPosition D mode ω s

/-- Exactly T actual periods, including initialization, clearing, and partial cycles. -/
def run {Ω : Type} [MeasurableSpace Ω] (D : Model Ω) (mode : Mode)
    (init : Initialization D.M D.K) (tie : TieRule) (ω : Ω) : ℕ → LearningState
  | 0 => {}
  | t+1 => learningStep D mode init tie ω (run D mode init tie ω t)

def totalRevenue {Ω : Type} [MeasurableSpace Ω] (D : Model Ω) (mode : Mode)
    (init : Initialization D.M D.K) (tie : TieRule) (T : ℕ) (ω : Ω) : ℝ :=
  ((run D mode init tie ω T).observations.map (fun x => x.2.2)).sum

def signedRegret {Ω : Type} [MeasurableSpace Ω] (D : Model Ω) (mode : Mode)
    (init : Initialization D.M D.K) (tie : TieRule) (T : ℕ) : ℝ :=
  (∫ ω, totalRevenue D mode init tie T ω ∂D.law) / T - benchmark D mode
end ZhangJasinPricing.Cyclic


