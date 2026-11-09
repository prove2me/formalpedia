-- Prove2me | Definitions.Def_EnumeratingComplexity224_Dichotomy_Process
-- name    : EnumeratingComplexity224_Dichotomy_Process
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T09:28:12.368944+00:00
-- url     : https://prove2.me/theorems/fc8a67d8-f076-4563-a7ad-574f10088f5c
-- title:
--   The finite-table scattering and collecting process
-- statement:
--   Fix machine codes $M,P$ and natural parameters $k,l$. The stage-$t$ table has one row for each binary word of length $t$, representing a cylinder of fair-tape mass $2^{-t}$. Each row stores a finite slow position, a frozen flag, and separate release and collecting event flags. Initially the position is empty and the row is free.
--
--   Each stage lifts the previous table to the longer prefixes. It first releases every frozen row whose old position equals a current output of a program of length at most $l$ on $M$, moving that row to its current fast output under $P$. Next it repeatedly selects an eligible finite set $F$, moves the entire eligible batch to $F$, and freezes the batch. Eligibility means being free and satisfying $B(w)\subseteq F\subseteq P^t(w)$. The comparison is exactly
--   $$2^{k+2}\,\#\{\text{eligible rank-}t\text{ rows}\}\ \ge\ 2^t.$$
--   Candidate sets are all subsets of the finite union of fast outputs, ordered by $\sum_{n\in F}2^n$. The loop makes $2^{k+2}$ attempts; after no candidate remains each further attempt is the identity. This realizes exhaustive collecting using the source's bound on successful iterations.
--
--   Write $N^t(w)$ for the final row position and $N(w)=\bigcup_tN^t(w)$. Its exact-output probability is $R_N(S\mid k,l)=\mu\{w:N(w)=S\}$. Case A means arbitrarily late release events; the alternating transitions also give arbitrarily late collecting events. Case B means eventually frozen with no later release. Case C means eventually free with no later release or collecting. A release followed by refreezing in the same stage is explicitly recorded. This reads the source's cases as properties of the whole transition history.
--
--   The table is constructed from $M,P,k,l$ alone, without access to $S$ or to the actual tape whose output is requested. It provides the specific process used by Lemmas 14 and 16–18, rather than arbitrary tables assumed to have their conclusions.
-- source:
--   Alexander Shekhovtsov, Nikolay Vereshchagin, Georgii Zakharov, Enumerating Complexity Revisited, STOC 2027 submission #224 (October 2026), p. 7–9, §3.1, equation (3), Remark 15 and cases A–C

import Definitions.Def_EnumeratingComplexity224_Dichotomy_Machines

namespace EnumeratingComplexity224.Dichotomy

/-- All rank-t cylinders, represented by their t bits. -/
def words : ℕ → List Word
  | 0 => [[]]
  | t + 1 => (words t).flatMap (fun u => [u ++ [false], u ++ [true]])

def tapePrefix (w : Tape) (t : ℕ) : Word := (List.range t).map w
def extend (u : Word) : Tape := fun i => u[i]?.getD false

/-- Position, frozen flag, release event, collecting event. Event flags are
reset at each stage, and retained even after another transition in that stage. -/
abbrev SlowState := Finset ℕ × Bool × Bool × Bool
abbrev Table := List (Word × SlowState)

def position (s : SlowState) : Finset ℕ := s.1
def frozen (s : SlowState) : Bool := s.2.1
def released (s : SlowState) : Bool := s.2.2.1
def collected (s : SlowState) : Bool := s.2.2.2

def lookup (u : Word) : Table → SlowState
  | [] => (∅, false, false, false)
  | (v, s) :: rest => if u = v then s else lookup u rest

def catPositions (m : Machine) (l t : ℕ) : List (Finset ℕ) :=
  ((List.range (l + 1)).flatMap words).map
    (fun p => stageOutput m p [] (fun _ => false) t)

def fastPosition (p : Machine) (t : ℕ) (u : Word) : Finset ℕ :=
  stageOutput p [] [] (extend u) t

/-- Lift the previous cylinder table, testing the OLD slow position against
current cats. Scattering precedes every collecting operation. -/
def scatterTable (m p : Machine) (l t : ℕ) (old : Table) : Table :=
  (words t).map fun u =>
    let s := lookup (u.take (t - 1)) old
    let hit := frozen s && (catPositions m l t).contains (position s)
    (u, if hit then (fastPosition p t u, false, true, false)
         else (position s, frozen s, false, false))

def eligible (p : Machine) (t : ℕ) (F : Finset ℕ) (row : Word × SlowState) : Bool :=
  !frozen row.2 && decide (position row.2 ⊆ F ∧ F ⊆ fastPosition p t row.1)

def batchCount (p : Machine) (t : ℕ) (F : Finset ℕ) (b : Table) : ℕ :=
  (b.filter (eligible p t F)).length

/-- Integer comparison equivalent to count/2^t ≥ 2^(-k-2). -/
def collectable (p : Machine) (k t : ℕ) (F : Finset ℕ) (b : Table) : Bool :=
  decide (2 ^ t ≤ 2 ^ (k + 2) * batchCount p t F b)

def finiteSetCode (F : Finset ℕ) : ℕ := F.sum (fun n => 2 ^ n)

/-- All subsets of the finite fast-output union, in increasing finite-set code. -/
def candidates (p : Machine) (t : ℕ) : List (Finset ℕ) :=
  let U := ((words t).map (fastPosition p t)).foldl (· ∪ ·) ∅
  (U.powerset.image finiteSetCode).sort (· ≤ ·) |>.map (fun c => (Finset.range (c + 1)).filter (fun i => c.testBit i = true))

def collectOnce (p : Machine) (k t : ℕ) (b : Table) : Table :=
  match (candidates p t).find? (fun F => collectable p k t F b) with
  | none => b
  | some F => b.map fun row =>
      (row.1, if eligible p t F row then (F, true, released row.2, true) else row.2)

/-- The mass bound allows at most 2^(k+2) successful iterations.
Identity iterations after exhaustion do not change the table. -/
def collectLoop (p : Machine) (k t : ℕ) : ℕ → Table → Table
  | 0, b => b
  | n + 1, b => collectLoop p k t n (collectOnce p k t b)

def history (m p : Machine) (k l : ℕ) : ℕ → Table
  | 0 => [([], (∅, false, false, false))]
  | t + 1 => collectLoop p k (t + 1) (2 ^ (k + 2))
      (scatterTable m p l (t + 1) (history m p k l t))

def slowState (m p : Machine) (k l t : ℕ) (w : Tape) : SlowState :=
  lookup (tapePrefix w t) (history m p k l t)

def slowOutput (m p : Machine) (k l : ℕ) (w : Tape) : Set ℕ :=
  {n | ∃ t, n ∈ position (slowState m p k l t w)}

noncomputable def slowProbability (m p : Machine) (k l : ℕ) (S : Set ℕ) : ENNReal :=
  tapeMeasure {w | slowOutput m p k l w = S}

def caseA (m p : Machine) (k l : ℕ) (w : Tape) : Prop :=
  ∀ T : ℕ, ∃ t ≥ T, released (slowState m p k l t w) = true

/-- Eventually frozen with no further release, including within-stage releases. -/
def caseB (m p : Machine) (k l : ℕ) (w : Tape) : Prop :=
  ∃ T : ℕ, ∀ t ≥ T, frozen (slowState m p k l t w) = true ∧
    released (slowState m p k l t w) = false

/-- Eventually free with no collecting or release transition. -/
def caseC (m p : Machine) (k l : ℕ) (w : Tape) : Prop :=
  ∃ T : ℕ, ∀ t ≥ T, frozen (slowState m p k l t w) = false ∧
    released (slowState m p k l t w) = false ∧
    collected (slowState m p k l t w) = false

end EnumeratingComplexity224.Dichotomy


