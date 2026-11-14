-- Prove2me | Definitions.Def_CountingLLL_ReciprocalTest
-- name    : CountingLLL_ReciprocalTest
-- status  : Definition
-- author  : @wcysai
-- created : 2026-11-13T06:37:53.491513+00:00
-- url     : https://prove2.me/theorems/662a0649-c3f9-4ef6-b5e6-2c59613ef705
-- title:
--   Small-step semantics of ReciprocalTest
-- statement:
--   A small-step operational semantics for Algorithm 6 of the pinned STOC submission. Three independent coordinate arrays supply the Bernoulli oracle, fair bits and uniform finite draws. The state records the program phase, counters, and entropy consumed. Nontermination has infinite oracle cost. Uniform finite draws are primitives here: this definition does not model or claim their bit-operation cost.
-- source:
--   Liu, Wang, Yin, Zhang and Zhou, A Counting and Sampling Lovász Local Lemma, STOC 2027 #442, Algorithm 6 and Lemma 6.5, PDF pp. 26–28, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/442.pdf

import Mathlib

set_option autoImplicit false

/-! An operational model of Algorithm 6 in the pinned STOC #442 paper.
The three entropy arrays are independent: oracle answers, fair bits, and uniform
integers. A draw from `uniform n` is uniform on `Fin (n+1)` and represents
1,...,n+1. Each individual array coordinate is consumed at most once. The
uniform primitive abstracts its fair-bit implementation and its bit cost, so
this model specifies oracle calls and the output law, not the paper's claimed
additional bit-running-time bound. -/
namespace CountingLLL.ReciprocalTest

open MeasureTheory
open scoped ENNReal

inductive Context where
  | initial | first | second
  deriving DecidableEq

inductive Phase where
  | start | initialCheck | loop | coinOracle (k : Context) | coinFair (k : Context)
  | uniformCheck | done (value : Bool)
  deriving DecidableEq

abbrev Entropy := (ℕ → Bool) × (ℕ → Bool) × ((a : ℕ × ℕ) → Fin (a.1 + 1))

structure State where
  phase : Phase := .start
  i : ℕ := 0
  j : ℕ := 0
  oracleUsed : ℕ := 0
  fairUsed : ℕ := 0
  uniformUsed : ℕ := 0
  deriving Inhabited

def initial : State := {}

/-- Resume one of the three syntactic calls of the local procedure Coin. -/
def coinReturn (k : Context) (v : Bool) (s : State) : State :=
  match k with
  | .initial =>
    let j := if v then 2 else 1
    { s with j := j, i := 2 * j - 1, phase := if v then .initialCheck else .loop }
  | .first => if v then { s with phase := .coinOracle .second }
      else { s with i := s.i - 1, phase := .loop }
  | .second => if v then { s with i := s.i + 2, j := s.j + 1, phase := .uniformCheck }
      else { s with phase := .loop }

/-- One atomic step. Nonhalting states never acquire an output. -/
def step (ω : Entropy) (s : State) : State :=
  match s.phase with
  | .start =>
    let b := ω.2.1 s.fairUsed
    let s' := { s with fairUsed := s.fairUsed + 1 }
    if b then { s' with phase := .done true } else { s' with phase := .coinOracle .initial }
  | .initialCheck =>
    let b := ω.2.1 s.fairUsed
    let s' := { s with fairUsed := s.fairUsed + 1 }
    if b then { s' with phase := .done true } else { s' with phase := .loop }
  | .loop =>
    if s.i = 0 then { s with phase := .done false }
    else { s with phase := .coinOracle .first }
  | .coinOracle k =>
    let b := ω.1 s.oracleUsed
    let s' := { s with oracleUsed := s.oracleUsed + 1 }
    if b then coinReturn k true s' else { s' with phase := .coinFair k }
  | .coinFair k =>
    let b := ω.2.1 s.fairUsed
    let s' := { s with fairUsed := s.fairUsed + 1 }
    if b then coinReturn k false s' else { s' with phase := .coinOracle k }
  | .uniformCheck =>
    let u := ω.2.2 (s.j - 1, s.uniformUsed)
    let s' := { s with uniformUsed := s.uniformUsed + 1 }
    if u.val = 0 then { s' with phase := .done true } else { s' with phase := .loop }
  | .done _ => s

def run (ω : Entropy) (n : ℕ) : State := (step ω)^[n] initial

def Halts (ω : Entropy) : Prop := ∃ n b, (run ω n).phase = .done b

def Returns (ω : Entropy) (b : Bool) : Prop := ∃ n, (run ω n).phase = .done b

noncomputable def oracleCost (ω : Entropy) : ℝ≥0∞ := by
  classical
  exact if h : Halts ω then ((run ω (Nat.find h)).oracleUsed : ℝ≥0∞) else ⊤

/-- Bernoulli oracle: false has mass B, true has mass 1-B, for B in [0,1]. -/
noncomputable def oracleLaw (B : ℝ≥0∞) : Measure Bool :=
  B • Measure.dirac false + (1-B) • Measure.dirac true

noncomputable def fairLaw : Measure Bool :=
  (1/2 : ℝ≥0∞) • Measure.dirac false + (1/2 : ℝ≥0∞) • Measure.dirac true

noncomputable def uniformLaw (n : ℕ) : Measure (Fin (n+1)) :=
  (1 / ((n+1 : ℕ) : ℝ≥0∞)) • Measure.count

/-- A countable product makes all oracle answers, fair bits and uniform draws independent. -/
noncomputable def entropyLaw (B : ℝ≥0∞) : Measure Entropy :=
  let μo := Measure.infinitePi (fun _ : ℕ => oracleLaw B)
  let μf := Measure.infinitePi (fun _ : ℕ => fairLaw)
  let μu := Measure.infinitePi (fun a : ℕ × ℕ => uniformLaw a.1)
  μo.prod (μf.prod μu)

end CountingLLL.ReciprocalTest


