-- Prove2me | Definitions.Def_OnlineRealSampling_Exact_Supplement_Sampler
-- name    : OnlineRealSampling_Exact_Supplement_Sampler
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T03:37:37.275595+00:00
-- url     : https://prove2.me/theorems/a95e1e5b-6e49-4894-beda-d5c631d69058
-- title:
--   General represented-state online oracle samplers and finite-prefix traces
-- statement:
--   A sampler has an arbitrary state type with an injective finite binary representation, a fixed initial state and a fixed deterministic transition rule. There is no finite-state, storage-length, time, horizon or precision bound. Its local actions use the published charged-machine conventions. It can consume fresh fair bits sequentially, query the current or any earlier revealed CDF oracle, and emit a natural number with a new persistent state. The only oracle information supplied to a continuation is the returned dyadic numerator. CDFs, evaluation costs, external seeds, histories and unread bits are not program inputs.
--
--   Finite-prefix execution freezes immediately after its prescribed number of emissions; the program never receives this stopping horizon. Invalid future-oracle queries and local halt actions stall. Failure to finish in finitely many transitions is represented by none. The public output history, shared bit cursor, largest query precision and peak storage are analysis data. Storage charges include actual state representations and intermediate operands, each precision-k answer's mandatory k-bit buffer, and each emitted integer's binary length. Trace history is not charged as retained program memory.
--
--   This general model supports the universal lower bound rather than describing only Algorithm 2. Every physical finite binary state representation can be relabeled in this model. Arbitrary deterministic local transitions include every effective word-RAM program; the lower bound does not depend on local computational power. There is no restriction to finite support or rational target probabilities.
-- source:
--   Draper, Harris and Saad, Online Random Sampling with Real Probabilities, STOC 2027 submission #103, manuscript dated 2026-11-02. Citation basis: preprint; pinned source.pdf SHA-256 66aeb5c181baf97cefba69aa26d29299e888a7a86c837a71af5b77d35f11c3e1; no arXiv identifier/version exists in the artifact, so cite the dated hash-pinned submission with the paper's own result number. PDF 1 is unnumbered; For PDF pages 2–24, printed page = PDF page − 1; PDF 1 is unnumbered. Source artifact: https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/103.pdf. §1 PDF 2 / printed 1; §3 PDF 7–8 / printed 6–7; §7.2 PDF 17–19 / printed 16–18.

import Mathlib
import Definitions.Def_OnlineRealSampling_Exact_Machine

namespace OnlineRealSampling.Exact.Supplement

noncomputable section

/-- A local machine action, a query to an already revealed oracle (zero-based index),
or emission of an output followed by the next persistent state. Local queries use the
current oracle. The program has no access to CDFs, costs, the external seed or unread bits. -/
inductive Command (σ : Type) where
  | local (action : Action σ) : Command σ
  | query (j x k : ℕ) (next : ℤ → Charged σ) : Command σ
  | emit (x : ℕ) (next : Charged σ) : Command σ

/-- An arbitrary represented-state online oracle program, fixed before its inputs or horizon.
The state has an actual finite binary representation, with no bound on its length. The
injection prevents hiding distinct stored states in one representation. Neither the state
space nor the number of transitions, queries or coin reads is required to be finite. -/
structure Sampler (σ : Type) where
  initial : σ
  step : σ → Command σ
  storage : σ → List Bool
  faithful : Function.Injective storage

/-- Analysis configuration. Only `st` is program memory. The bit cursor, public output
transcript, precision maximum and peak storage are trace data, unavailable to the program.
The transcript is used by the causal input environment and is not charged as stored history. -/
structure Trace (σ : Type) where
  st : σ
  pos : ℕ
  history : List ℕ
  precision : ℕ
  peak : ℕ

def start {σ : Type} (A : Sampler σ) : Trace σ :=
  ⟨A.initial, 0, [], 0, (A.storage A.initial).length⟩

/-- Charge actual old/new represented memory, local operands and the current input/output
buffer. Counts are peaks, not sums over rounds. Oracle internal workspace is excluded. -/
def move {σ : Type} (A : Sampler σ) (c : Trace σ) (r : Charged σ)
    (readBits buffer : ℕ) : Trace σ :=
  { c with
    st := r.val
    pos := c.pos + readBits
    peak := max c.peak
      (max (A.storage c.st).length (A.storage r.val).length + max r.led.maxBits buffer) }

/-- Query only a revealed handle. `j = history.length` denotes the current target;
smaller j accesses the target selected at the earlier public history `history.take j`.
Invalid future handles stall. The returned dyadic numerator is the only oracle data
passed to the continuation. The answer buffer of a precision-k query is charged exactly k bits (Section 3, PDF 7 / printed 6), whatever its value. -/
def queryStep {σ : Type} (A : Sampler σ) (orc : List ℕ → CDFOracle)
    (c : Trace σ) (j x k : ℕ) (next : ℤ → Charged σ) : Trace σ :=
  if j ≤ c.history.length then
    let answer := (orc (c.history.take j)).φ x k
    { move A c (next answer) 0 k with
      precision := max c.precision k }
  else c

/-- One deterministic transition, reading fresh coins sequentially from one shared tape.
An emitted output is charged its binary length even when not retained in the next state.
The local halt action stalls: it does not fabricate a completed sampling round. -/
def advance {σ : Type} (A : Sampler σ) (orc : List ℕ → CDFOracle)
    (ω : ℕ → Bool) (c : Trace σ) : Trace σ :=
  match A.step c.st with
  | .local .halt => c
  | .local (.compute r) => move A c r 0 0
  | .local (.coin next) => move A c (next (ω c.pos)) 1 1
  | .local (.coins m next) => move A c (next (bitsValue ω c.pos m)) m m
  | .local (.query x k next) => queryStep A orc c c.history.length x k next
  | .query j x k next => queryStep A orc c j x k next
  | .emit x next =>
    { move A c next 0 (bitLen (x : ℤ)) with history := c.history ++ [x] }

/-- Freeze analysis immediately after the nth emission, without informing the program of n.
The same fixed initial state and transition function serve all horizons. -/
def prefixStep {σ : Type} (A : Sampler σ) (orc : List ℕ → CDFOracle)
    (ω : ℕ → Bool) (n : ℕ) (c : Trace σ) : Trace σ :=
  if c.history.length < n then advance A orc ω c else c

def runPrefix {σ : Type} (A : Sampler σ) (orc : List ℕ → CDFOracle)
    (ω : ℕ → Bool) (n t : ℕ) : Trace σ :=
  (prefixStep A orc ω n)^[t] (start A)

/-- Completion means n actual emissions in finitely many transitions. -/
def Terminates {σ : Type} (A : Sampler σ) (orc : List ℕ → CDFOracle)
    (ω : ℕ → Bool) (n : ℕ) : Prop :=
  ∃ t, (runPrefix A orc ω n t).history.length = n

open Classical in
/-- First completed prefix, or none on nontermination. No finite time bound is imposed. -/
def finish {σ : Type} (A : Sampler σ) (orc : List ℕ → CDFOracle)
    (ω : ℕ → Bool) (n : ℕ) : Option (Trace σ) :=
  if h : Terminates A orc ω n then some (runPrefix A orc ω n (Nat.find h)) else none

/-- Output-history cylinder; nontermination is not an output. -/
def outputEvent {σ : Type} (A : Sampler σ) (orc : List ℕ → CDFOracle)
    (xs : List ℕ) : Set (ℕ → Bool) :=
  {ω | (finish A orc ω xs.length).map Trace.history = some xs}

/-- E_{n,k}: no query above k anywhere in the first n rounds, including earlier-oracle
queries. Infinite nonterminating paths are included if all their queries are low precision;
for exact samplers these paths have probability zero. -/
def lowPrecision {σ : Type} (A : Sampler σ) (orc : List ℕ → CDFOracle)
    (n k : ℕ) : Set (ℕ → Bool) :=
  {ω | ∀ t, (runPrefix A orc ω n t).precision ≤ k}

/-- A fixed sequence is a causal oracle rule ignoring the values of earlier outputs. -/
def fixedTargets (O : ℕ → CDFOracle) : List ℕ → CDFOracle := fun h => O h.length

end
end OnlineRealSampling.Exact.Supplement


