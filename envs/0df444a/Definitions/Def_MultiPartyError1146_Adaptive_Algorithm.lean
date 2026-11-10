-- Prove2me | Definitions.Def_MultiPartyError1146_Adaptive_Algorithm
-- name    : MultiPartyError1146_Adaptive_Algorithm
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-09T18:33:39.207619+00:00
-- url     : https://prove2.me/theorems/f82ff3bc-36bc-4533-a73e-826b7b5d27c7
-- title:
--   Algorithm 1: actual local transitions and binary-round execution
-- statement:
--   The three phases of Algorithm 1 are represented by finite lists of binary-symbol blocks. Phase 1 repeats each party's input and uses the number of received ones divided by the full block length. Phase 2 resets signed counters, forwards the least-cushion coordinates in index order, checks decoded packets for distinct valid indices, and updates the time-above-threshold counters. Phase 3 uses the balanced encoding of each ordered restricted ternary view as a speaking schedule, decodes identity/bit pairs only while listening, and applies the signed-vote threshold or the stored majority fallback.
--
--   The ordinary estimate before supermajority is retained separately for Lemma 4.4. Supermajority gives 0 at $1/3$, 1 at $2/3$, and unsure strictly between them. A party always retains its true private input. The generated protocol reads only completed blocks of its received prefix.
--
--   For internal iteration count $R\ge1$, put $h=1/(2R)$. Widths and prefixes are the ceilings of $n^{1/2+(r+1)h}$ and $n^{1-rh}$, capped at $n$, with zero-based iteration index $r$. The lead scale is $\lceil n^{1/2+h}\rceil$. Code quality and fixed rate bounds form the separate predicate Good; they are not fields asserting correctness. No invariant, good execution, or existence theorem is hidden in the algorithm.
-- source:
--   Klim Efremenko, Gillat Kol, Raghuvansh Saxena, Zhijun Zhang, STOC 2027 submission #1146 (October 2026), Algorithm 1; setup printed p.20, printed p.21, PDF p.23

import Mathlib
import Definitions.Def_MultiPartyError1146_Adaptive_Protocol
import Definitions.Def_MultiPartyError1146_Adaptive_Codes

set_option autoImplicit false

namespace MultiPartyError1146.Adaptive

noncomputable def internalIterations (η : ℝ) : ℕ := max 1 ⌈1 / (2 * η)⌉₊

noncomputable def exponent (R : ℕ) : ℝ := 1 / (2 * (R : ℝ))
noncomputable def width (n R r : ℕ) : ℕ :=
  min n ⌈(n : ℝ) ^ ((1 : ℝ) / 2 + (r + 1) * exponent R)⌉₊
noncomputable def prefixSize (n R r : ℕ) : ℕ :=
  min n ⌈(n : ℝ) ^ (1 - r * exponent R)⌉₊
noncomputable def leadScale (n R : ℕ) : ℕ := ⌈(n : ℝ) ^ ((1 : ℝ) / 2 + exponent R)⌉₊
noncomputable def rollLength (n R : ℕ) : ℕ :=
  max 1 ⌈(leadScale n R : ℝ) * Real.log (2 * n)⌉₊
noncomputable def selectorCount (n R : ℕ) : ℕ := max 1 ⌈(n : ℝ) ^ (1 + exponent R)⌉₊
noncomputable def viewWidth (n : ℕ) : ℕ := max 1 ⌈Real.sqrt n⌉₊

/-- Fixed-length lists of possibly missing index/value pairs. Validity is checked after decoding. -/
abbrev Packet (n l : ℕ) := Fin l → Option (Fin n × Bool)

/-- Actual encoders and selector sets, with no quality assertions stored as fields. -/
structure AlgorithmData (n R : ℕ) where
  shortCode : BinaryCode (Fin n × Bool)
  forwardCode : (r : Fin R) → BinaryCode (Packet n (width n R r.val))
  balancedCode : BinaryCode (Fin (viewWidth n) → Symbol)
  selectors : Selector n (selectorCount n R)

/-- The ordinary code/selector assumptions made in the source's algorithm setup.
Length bounds expose the otherwise implicit fixed code-rate constants. -/
noncomputable def AlgorithmData.Good {n R : ℕ} (D : AlgorithmData n R) (a : ℝ) : Prop :=
  D.shortCode.HasDistance ((49 : ℝ) / 100) ∧
  Real.log (2 * n) ≤ D.shortCode.length ∧
  (D.shortCode.length : ℝ) ≤ a * Real.log (2 * n) ∧
  (∀ r, (D.forwardCode r).HasDistance ((49 : ℝ) / 100) ∧
    (width n R r.val : ℝ) * Real.log (2 * n) ≤ (D.forwardCode r).length ∧
    ((D.forwardCode r).length : ℝ) ≤ a * width n R r.val * Real.log (2 * n)) ∧
  D.balancedCode.Balanced 3 ((99 : ℝ) / 100) ∧
  (viewWidth n : ℝ) ≤ D.balancedCode.length ∧
  (D.balancedCode.length : ℝ) ≤ a * viewWidth n ∧ IsSelector D.selectors

/-- All local quantities are updated from the receiver's own messages. -/
structure LocalState (n : ℕ) where
  view : Fin n → Symbol
  estimate : Fin n → Bool
  gamma : Fin n → ℤ
  xi : Fin n → ℤ
  beta : Fin n → ℝ
  sigma : Fin n → ℤ

noncomputable def initial {n : ℕ} (i : Fin n) (b : Bool) : LocalState n :=
  ⟨fun k => some (if k = i then b else false), fun k => if k = i then b else false, fun _ => 0, fun _ => 0,
    fun _ => 0, fun _ => 0⟩

def sign (b : Bool) : ℤ := if b then 1 else -1
noncomputable def majority (w : ℝ) : Bool := decide ((1 : ℝ) / 2 ≤ w)
noncomputable def supermajority (w : ℝ) : Symbol :=
  if w ≤ (1 : ℝ) / 3 then some false else if (2 : ℝ) / 3 ≤ w then some true else none

/-- Ties in the least-cushion rule are settled by party index. -/
noncomputable def selected {n R : ℕ} (r : Fin R) (s : LocalState n) : List (Fin n) :=
  ((List.finRange n).mergeSort fun j k =>
    let cj := sign (s.estimate j) * s.gamma j
    let ck := sign (s.estimate k) * s.gamma k
    decide (cj < ck ∨ (cj = ck ∧ j.val ≤ k.val))).take (width n R r.val)

noncomputable def packet {n R : ℕ} (r : Fin R) (s : LocalState n) :
    Packet n (width n R r.val) :=
  fun j => ((selected r s)[j.val]?).map fun k => (k, s.estimate k)

noncomputable def entries {n l : ℕ} (p : Packet n l) : List (Fin n × Bool) :=
  (List.finRange l).filterMap p

noncomputable def validPacket {n l : ℕ} (p : Packet n l) : Prop :=
  (entries p).length = l ∧ ((entries p).map Prod.fst).Nodup

noncomputable def addPacket {n l : ℕ} (g : Fin n → ℤ) (p : Packet n l) : Fin n → ℤ :=
  fun k => g k + ((entries p).map fun e => if e.1 = k then sign e.2 else 0).sum

/-- Ordered restriction followed by fixed ternary padding. -/
noncomputable def restrictedView {n R : ℕ} (D : AlgorithmData n R)
    (q : Fin (selectorCount n R)) (s : LocalState n) : Fin (viewWidth n) → Symbol :=
  fun j => match ((D.selectors q).sort (· ≤ ·))[j.val]? with
    | some k => s.view k
    | none => none

/-- Binary-symbol blocks, not macro-rounds. -/
inductive Block (n R : ℕ) where
  | roll (speaker : Fin n)
  | forward (iteration : Fin R) (speaker : Fin n)
  | repair (group : Fin (selectorCount n R)) (position : ℕ)

noncomputable def blocks {n R : ℕ} (D : AlgorithmData n R) : List (Block n R) :=
  (List.finRange n).map Block.roll ++
  (List.finRange R).flatMap (fun r =>
    ((List.finRange n).filter fun i => i.val < prefixSize n R r.val).map (Block.forward r)) ++
  (List.finRange (selectorCount n R)).flatMap (fun q =>
    (List.range D.balancedCode.length).map (Block.repair q))

noncomputable def blockLength {n R : ℕ} (D : AlgorithmData n R) : Block n R → ℕ
  | .roll _ => rollLength n R
  | .forward r _ => (D.forwardCode r).length
  | .repair _ _ => D.shortCode.length

noncomputable def duration {n R : ℕ} (D : AlgorithmData n R) : ℕ :=
  ((blocks D).map (blockLength D)).sum

noncomputable def prepare {n R : ℕ} (b : Block n R) (s : LocalState n) : LocalState n :=
  match b with
  | .forward _ j => if j.val = 0 then {s with gamma := fun _ => 0, xi := fun _ => 0} else s
  | _ => s

noncomputable def scheduledToSpeak {n R : ℕ} (D : AlgorithmData n R)
    (i : Fin n) (s : LocalState n) (b : Block n R) : Bool := by
  classical
  exact match b with
  | .roll j => decide (i = j)
  | .forward _ j => decide (i = j)
  | .repair q l => decide (i ∈ D.selectors q) &&
      if h : l < D.balancedCode.length then
        D.balancedCode.encode (restrictedView D q s) ⟨l,h⟩ else false

noncomputable def blockSend {n R : ℕ} (D : AlgorithmData n R) (i : Fin n)
    (own : Bool) (s : LocalState n) (b : Block n R) (l : ℕ) : Symbol :=
  if scheduledToSpeak D i s b then
    match b with
    | .roll _ => some own
    | .forward r _ => if h : l < (D.forwardCode r).length then
        some ((D.forwardCode r).encode (packet r s) ⟨l,h⟩) else none
    | .repair _ _ => if h : l < D.shortCode.length then
        some (D.shortCode.encode (i,own) ⟨l,h⟩) else none
  else none

noncomputable def endForward {n R : ℕ} (i : Fin n) (r : Fin R) (j : Fin n)
    (s : LocalState n) : LocalState n :=
  let L : ℝ := leadScale n R
  let xi' := fun k => if k = i then s.xi k else
    s.xi k + (if L / 100 ≤ (s.gamma k : ℝ) then 1 else
      if (s.gamma k : ℝ) ≤ -L / 100 then -1 else 0)
  let s' := {s with xi := xi'}
  if j.val + 1 = prefixSize n R r.val then
    let v' := fun k => if k = i then s'.estimate k else
      if (prefixSize n R r.val : ℝ) / 2 < (xi' k : ℝ) then true else
      if (xi' k : ℝ) < -(prefixSize n R r.val : ℝ) / 2 then false else s'.estimate k
    if r.val + 1 = R then
      let beta' := fun k => (1 + (s'.gamma k : ℝ) / L) / 2
      {s' with beta := beta', estimate := v', view := fun k => if k = i then some (v' k) else supermajority (beta' k)}
    else {s' with estimate := v', view := fun k => some (v' k)}
  else s'

/-- Completion of a block; the speaker ignores its own incoming coordinates. -/
noncomputable def blockReceive {n R : ℕ} (D : AlgorithmData n R) (i : Fin n)
    (s : LocalState n) (b : Block n R) (y : ℕ → Symbol) : LocalState n := by
  classical
  exact match b with
  | .roll j =>
      if i = j then s else
        let ones := ((List.range (rollLength n R)).filter fun l => y l = some true).length
        let value := majority ((ones : ℝ) / rollLength n R)
        {s with
          view := Function.update s.view j (some value)
          estimate := Function.update s.estimate j value}
  | .forward r j =>
      let decoded := if i = j then some (packet r s) else (D.forwardCode r).decode (fun l => y l.val)
      let g := match decoded with
        | some p => if validPacket p then addPacket s.gamma p else s.gamma
        | none => s.gamma
      endForward i r j {s with gamma := g}
  | .repair _ _ =>
      if scheduledToSpeak D i s b then s else
        match D.shortCode.decode (fun l => y l.val) with
        | none => s
        | some (k,v) => {s with sigma := fun j => s.sigma j + if j = k then sign v else 0}

/-- Replay only completed blocks; the partial block's action is computed from its starting
state. Values of y at times ≥ cut are never read. -/
noncomputable def replay {n R : ℕ} (D : AlgorithmData n R) (i : Fin n) (own : Bool)
    (cut : ℕ) (y : ℕ → Symbol) : LocalState n × Symbol :=
  let result := (blocks D).foldl (fun (z : ℕ × LocalState n × Symbol) b =>
    let start := z.1
    let stop := start + blockLength D b
    if stop ≤ cut then
      (stop, blockReceive D i (prepare b z.2.1) b (fun l => y (start + l)), z.2.2)
    else if start ≤ cut then
      (stop, z.2.1, blockSend D i own (prepare b z.2.1) b (cut - start))
    else (stop, z.2.1, z.2.2)) (0, initial i own, none)
  result.2

noncomputable def algorithm1 {n R : ℕ} (D : AlgorithmData n R) : Protocol n 1 (duration D) where
  send t i own h := (replay D i (own 0) t.val
    (fun j => if hj : j < t.val then h ⟨j,hj⟩ else none)).2
  output i own h :=
    let s := (replay D i (own 0) (duration D)
      (fun j => if hj : j < duration D then h ⟨j,hj⟩ else none)).1
    fun k _ => if k = i then own 0 else
      if (leadScale n R : ℝ) * D.balancedCode.length / 100 < (s.sigma k : ℝ) then true else
      if (s.sigma k : ℝ) < -(leadScale n R : ℝ) * D.balancedCode.length / 100 then false
      else majority (s.beta k)

/-- End time of a block prefix, used for execution-derived internal notation. -/
noncomputable def prefixTime {n R : ℕ} (D : AlgorithmData n R) (s : ℕ) : ℕ :=
  (((blocks D).take s).map (blockLength D)).sum

noncomputable def phase1Time {n R : ℕ} (D : AlgorithmData n R) : ℕ := prefixTime D n
noncomputable def iterationStart {n R : ℕ} (D : AlgorithmData n R) (r : ℕ) : ℕ :=
  prefixTime D (n + ((List.range r).map (prefixSize n R)).sum)
noncomputable def iterationEnd {n R : ℕ} (D : AlgorithmData n R) (r : ℕ) : ℕ :=
  iterationStart D (r + 1)

/-- A local snapshot computed from the actual received matrix, never a free invariant. -/
noncomputable def snapshot {n R : ℕ} (D : AlgorithmData n R) (x : Input n 1)
    (A : Adversary n (duration D)) (time : ℕ) (i : Fin n) : LocalState n :=
  (replay D i (x i 0) time (fun t => if h : t < duration D then A ⟨t,h⟩ i else none)).1

noncomputable def exceptionalInputs {n R : ℕ} (D : AlgorithmData n R) (x : Input n 1)
    (A : Adversary n (duration D)) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter fun k => (n : ℝ) / 100 ≤
    ((Finset.univ.filter fun i => (snapshot D x A (phase1Time D) i).view k ≠ some (x k 0)).card : ℝ)

noncomputable def phase2Time {n R : ℕ} (D : AlgorithmData n R) : ℕ := iterationStart D R
noncomputable def exceptionalReceivers {n R : ℕ} (D : AlgorithmData n R) (x : Input n 1)
    (A : Adversary n (duration D)) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter fun i => ∃ k, k ∉ exceptionalInputs D x A ∧
    (snapshot D x A (phase2Time D) i).view k ≠ some (x k 0)

end MultiPartyError1146.Adaptive


