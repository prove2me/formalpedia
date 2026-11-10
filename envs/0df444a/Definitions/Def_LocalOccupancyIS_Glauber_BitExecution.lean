-- Prove2me | Definitions.Def_LocalOccupancyIS_Glauber_BitExecution
-- name    : LocalOccupancyIS_Glauber_BitExecution
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-09T11:00:08.537041+00:00
-- url     : https://prove2.me/theorems/fc786149-86e9-4015-b77d-abe7c19b3371
-- title:
--   Rational preprocessing and a charged fair-bit Glauber machine
-- statement:
--   For rational $b\ge0$, a fixed program computes enclosures for $s=(b+1)^{1/(2t-1)}$ by rational bisection and for $D=\log\Delta-\log s$ by binary normalization and finite atanh series. It refines until its enclosure $[l,u]$ for $x=sD^{2t-1}$ has width at most $1/2$, then rounds $u$ upward to a positive integer $q$. The midpoint is intended to approximate $x$ within $1/4$; accuracy and termination remain theorem obligations. Rational arithmetic and comparisons accumulate cubic charges in operand bit lengths.
--
--   The fixed fair-bit machine rejection-samples a uniform site in $\{0,\ldots,n-1\}$ and a uniform integer in $\{0,\ldots,q\}$, using proposal one exactly when the latter is zero. It updates the actual spin array, retains a largest record, and resets between
--
--   $$T_{\rm bit}=\max\{1,n^8\},\qquad R_{\rm bit}=\max\{1,n^3(m+1)\}$$
--
--   runs and repetitions, for accuracy input $m\ge1$ and intended failure bound $e^{-m}$. Every machine transition consumes one fair bit; bits on deterministic transitions are discarded. Output mass is summed over first-halting finite tapes, and expected cost is a nonnegative extended-real sum over all live prefixes, including rational preprocessing, input reading, graph scans, array updates, record maintenance and integer bookkeeping. No rejection cutoff, termination guarantee, success assertion or polynomial bound is assumed by the definitions. This realizes the source's rounded-fugacity implementation without treating $\widehat\lambda$ as $\lambda$.
-- source:
--   Ewan Davies, Brian Tan, STOC 2027 submission #982 (October 2026), proof of Corollary 4, random-bit implementation, p. 20; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/982.pdf#page=20

import Definitions.Def_LocalOccupancyIS_Glauber_Execution

open scoped BigOperators

namespace LocalOccupancyIS.Glauber

/-! A single rational preprocessing procedure and fair-bit state machine.
Rational arithmetic is charged by a conservative school-arithmetic bit cost.
Neither termination, approximation accuracy nor polynomial cost is built into the model. -/

def bits (a : ℕ) : ℕ := a.log2 + 1
def ratBits (a : ℚ) : ℕ := bits a.num.natAbs + bits a.den + 1
abbrev Counted (α : Type) := StateM ℕ α

def charge (c : ℕ) : Counted Unit := modify (fun z => z+c)
def rationalOp (op : ℚ → ℚ → ℚ) (a b : ℚ) : Counted ℚ := do
  charge ((ratBits a + ratBits b + 1)^3)
  pure (op a b)
def addQ := rationalOp (· + ·)
def subQ := rationalOp (· - ·)
def mulQ := rationalOp (· * ·)
def divQ := rationalOp (· / ·)
def lessQ (a b : ℚ) : Counted Bool := do
  charge ((ratBits a + ratBits b + 1)^3)
  pure (decide (a < b))

def powQ (a : ℚ) (r : ℕ) : Counted ℚ := do
  let mut y : ℚ := 1
  for _ in List.range r do y ← mulQ y a
  pure y

/-- r-th root of B, by rational bisection from [1,max(1,B)]. -/
def rootBracket (B : ℚ) (r h : ℕ) : Counted (ℚ × ℚ) := do
  let mut lo : ℚ := 1
  let mut hi : ℚ := max 1 B
  for _ in List.range (h + ratBits B + 2) do
    let mid ← divQ (← addQ lo hi) 2
    let y ← powQ mid r
    if ← lessQ y B then lo := mid else hi := mid
  pure (lo,hi)

/-- Truncated atanh series 2 Σ_{i<L} z^(2i+1)/(2i+1). -/
def logSeries (z : ℚ) (L : ℕ) : Counted ℚ := do
  let mut a : ℚ := 0
  let mut power := z
  let z₂ ← mulQ z z
  for i in List.range L do
    a ← addQ a (← divQ power (2*i+1))
    power ← mulQ power z₂
  mulQ 2 a

/-- Log on y≥1: binary normalization, then the convergent atanh series.
The second component is the computable upper error enclosure. -/
def logBracket (y : ℚ) (h : ℕ) : Counted (ℚ × ℚ) := do
  charge ((ratBits y+1)^3)
  let k := (y.num.natAbs / y.den).log2
  let z ← divQ y (← powQ 2 k)
  let L := h + ratBits y + 10
  let ln₂ ← logSeries (1/3) L
  let a ← logSeries (← divQ (← subQ z 1) (← addQ z 1)) L
  let lo ← addQ (← mulQ k ln₂) a
  let err ← divQ (3*(k+1)) (← powQ 9 L)
  pure (lo, ← addQ lo err)

/-- A stage refines s and D, then encloses x=s D^(2t-1).
Stopping at width 1/2 supplies a midpoint approximation within 1/4. -/
def parameterStage (Δ t : ℕ) (b : ℚ) (h : ℕ) : Counted (Option (ℕ × ℚ × ℚ)) := do
  let B ← addQ b 1
  let r := 2*t-1
  let (sl,sh) ← rootBracket B r h
  let (dl,dh) ← logBracket Δ h
  let (ll,_) ← logBracket sl h
  let (_,hh) ← logBracket sh h
  let lowD ← subQ dl hh
  let highD ← subQ dh ll
  let xl ← mulQ sl (← powQ (max 0 lowD) r)
  let xh ← mulQ sh (← powQ (max 0 highD) r)
  let width ← subQ xh xl
  if ← lessQ (1/2) width then pure none
  else
    charge ((ratBits xh+1)^3)
    pure (some (max 1 (Int.toNat ⌈xh⌉),xl,xh))

/-- Fixed conservative polynomial horizons. No real constants are evaluated at run time. -/
def bitHorizon (n : ℕ) : ℕ := max 1 (n^8)
def bitRepeats (n m : ℕ) : ℕ := max 1 (n^3*(m+1))
def drawWidth (m : ℕ) : ℕ := bits (m-1)

inductive BitState (n : ℕ) where
  | prepare (h : ℕ)
  | draw (q runs remaining : ℕ) (current best : Fin n → Bool)
      (proposal : Bool) (site j accumulator : ℕ)
  | done (best : Fin n → Bool)

/-- Executable array operations for the bit machine. -/
def bitSize {n : ℕ} (σ : Fin n → Bool) : ℕ := (List.finRange n).countP σ
def bitSpin {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (σ : Fin n → Bool) (u : Fin n) (coin : Bool) : Fin n → Bool :=
  Function.update σ u (if (List.finRange n).all (fun v => !(decide (G.Adj u v) && σ v)) then coin else false)

/-- One fair bit per machine transition; deterministic transitions discard that bit.
Rejection loops are unbounded. A site draw is followed by an independent proposal draw. -/
def bitStep {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (Δ t : ℕ) (b : ℚ) (initial : Fin n → Bool) (m : ℕ) (state : BitState n) (coin : Bool) : BitState n :=
  match state with
  | .done B => .done B
  | .prepare h =>
    match ((parameterStage Δ t b h).run 0).1 with
    | none => .prepare (h+1)
    | some (q,_,_) => .draw q (bitRepeats n m) (bitHorizon n) initial initial false 0 0 0
  | .draw q runs remaining current best proposal site j acc =>
    let target := if proposal then q+1 else n
    if j < drawWidth target then
      .draw q runs remaining current best proposal site (j+1) (2*acc + if coin then 1 else 0)
    else if target ≤ acc then
      .draw q runs remaining current best proposal site 0 0
    else if !proposal then
      .draw q runs remaining current best true acc 0 0
    else
      let next := if hs : site < n then bitSpin G current ⟨site,hs⟩ (decide (acc=0)) else current
      let record := if bitSize best < bitSize next then next else best
      if 1 < remaining then .draw q runs (remaining-1) next record false 0 0 0
      else if 1 < runs then .draw q (runs-1) (bitHorizon n) initial record false 0 0 0
      else .done record

/-- Charged integer bookkeeping at each bit; local neighbor scans, record copies and resets
are charged at completed updates. Rational preprocessing charges each arithmetic operation. -/
def bitStepCost {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (Δ t : ℕ) (b : ℚ) (m : ℕ) : BitState n → ℕ
  | .done _ => 0
  | .prepare h => 1 + (bits h+1)^3 + ((parameterStage Δ t b h).run 0).2
  | .draw q runs remaining _ _ proposal _ j acc =>
    1 + (bits n+bits q+bits runs+bits remaining+bits j+bits acc+bits m+1)^3 +
      if proposal && decide (drawWidth (q+1) ≤ j) && decide (acc < q+1) then
        (8*n+8)*(bits n+1)^3 else 0

def bitEval {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (Δ t : ℕ) (b : ℚ) (initial : Fin n → Bool) (m : ℕ) (tape : List Bool) : BitState n :=
  tape.foldl (bitStep G Δ t b initial m) (.prepare 1)

def isDone {n : ℕ} : BitState n → Bool
  | .done _ => true
  | _ => false

/-- First-halting output mass, summed over finite fair-bit tapes. -/
noncomputable def bitLaw {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (Δ t : ℕ) (b : ℚ) (initial : Fin n → Bool) (m : ℕ) (out : Fin n → Bool) : ENNReal :=
  ∑' j : ℕ, ∑ tape : Fin (j+1) → Bool,
    if isDone (bitEval G Δ t b initial m ((List.ofFn tape).take j)) then 0 else
    match bitEval G Δ t b initial m (List.ofFn tape) with
    | .done B => if B = out then (2 : ENNReal)⁻¹ ^ (j+1) else 0
    | _ => 0

/-- Restriction to feasible configurations. Total mass one is a theorem conclusion. -/
noncomputable def bitOutput {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (Δ t : ℕ) (b : ℚ) (I : State G) (m : ℕ) : State G → ℝ :=
  fun out => (bitLaw G Δ t b I.val m out.val).toReal

/-- Input reading plus the expectation of the charged steps before halting.
An infinite/nonterminating execution has its full extended nonnegative cost. -/
noncomputable def expectedBitCost {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (Δ t : ℕ) (b : ℚ) (I : State G) (m : ℕ) : ENNReal :=
  (n^2+ratBits b+bits t+m+1 : ℕ) +
  ∑' j : ℕ, ∑ tape : Fin j → Bool,
    (bitStepCost G Δ t b m (bitEval G Δ t b I.val m (List.ofFn tape)) : ENNReal) * (2 : ENNReal)⁻¹ ^ j

end LocalOccupancyIS.Glauber


