-- Prove2me | Definitions.Def_DirectedHamiltonicity_CycleSearchHost
-- name    : DirectedHamiltonicity_CycleSearchHost
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-27T04:00:11.528018+00:00
-- url     : https://prove2.me/theorems/2817846a-100a-56b8-828c-660ea46f1f37
-- title:
--   A host RAM for the finite edge-deletion cycle search
-- statement:
--   An explicit host program for the finite edge-deletion cycle search of Koana and Kumabe.
--
--   For a fixed parity program $Q$ and constants $A,k$, `main Q A k` is a structured log-cost RAM routine. On the input encoding of an $n$-vertex directed graph it
--
--   1. reads $n$ and the adjacency matrix, packing the arcs into one integer $G$ whose bit $u n+v$ records the arc $u\to v$;
--   2. answers directly when $n\le 1$;
--   3. otherwise computes all search parameters (number of trials, seed width, majority size, parity-string length $L$), then for every arc in row-major order tentatively deletes it and runs the amplified decision: for each trial it reads a seed block from the coins, decodes the draw, and for an admissible draw writes the weighted parity instance into memory and runs $Q$ through the structured interpreter on $2r$ disjoint coin windows of length $L$, accepting by majority;
--   4. finally checks that the remaining arcs form a Hamiltonian cycle (following the first outgoing arc from vertex $0$) and outputs the result.
--
--   The file also fixes the vocabulary used to specify the sub-routines: the constant registers (`Consts`), the parity-instance string `candX` of a candidate draw, the frame predicate `Kept` and the lists of registers each sub-routine may modify.
--
--   **Formalization Note** Logical register $i$ is the cell $14+i$; cells $0,\dots,13$ are arithmetic scratch. The simulated input starts at address $300$.
-- source:
--   Engineering definition for DirectedHamiltonicity.Main.execute_cycle_search: an explicit host RAM for the finite edge-deletion cycle search (Def_DirectedHamiltonicity_CycleSearch), following T. Koana and S. Kumabe, Breaking the 2^n barrier for directed hamiltonicity (STOC 2027 submission #811), Section 2 / proof of Theorem 1 (PDF pp. 4-5).

import Definitions.Def_LogCostRAM_Interpreter
import Definitions.Def_DirectedHamiltonicity_CycleSearch

set_option autoImplicit false

namespace DirectedHamiltonicity.Main.CycleHost

/-!
# A host RAM for the finite edge-deletion cycle search

The host program implements, for a fixed parity program `Q` and constants `A k`, the procedure
`CycleReduction.answer Q A k` of `Def_DirectedHamiltonicity_CycleSearch`. Logical registers are
the cells `Word.cell i = 14 + i`; cells `0, …, 13` are arithmetic scratch. Each parity query is run
by the structured interpreter `Interp.call`.
-/

open TargetedSamplers TargetedSamplers.Structured TargetedSamplers.Structured.Word
open TargetedSamplers.Structured.Interp

/-- Register numbers (logical; the address of register `i` is `cell i`). -/
def rN := 0      -- n
def rCur := 1    -- input cursor after the header
def rN2 := 2     -- n*n
def rG := 3      -- current graph, packed: bit (u*n+v)
def rE := 4      -- edge index
def rBit := 5
def rGp := 6     -- candidate graph
def rFlag := 7
def rTrials := 8
def rSw := 9     -- seed width
def rL := 10     -- parity coin string length
def rR := 11     -- majority half r
def rR2 := 12    -- 2r
def rDc := 13    -- draw count
def rOne := 14
def rZero := 15
def rTwo := 16
def rI := 17     -- trial index
def rJ := 18     -- inner index
def rDv := 19    -- draw rank
def rPow := 20
def rTmp := 21
def rTmp2 := 22
def rS := 23
def rT := 24
def rB := 25
def rSym := 26   -- symbol table rank
def rWt := 27    -- weight table rank
def rPW := 29    -- Wmax^(3n)
def rIn := 30    -- inner cardinality (50^(n*n) * Wmax^(3n) * (Bmax+1))
def rW := 31     -- Wmax
def rBm1 := 32   -- Bmax+1
def rSeedPos := 33
def rTapeBase := 34
def rVotes := 35
def rCand := 36
def rXc := 37    -- x cursor
def rK := 38     -- value being emitted
def rSlot := 39
def rU := 40
def rV := 41
def rLl := 42
def rTv := 43
def rHv := 44
def rWv := 45
def rM := 46     -- 3*n*n
def rOk := 47
def rFound := 48
def rNext := 49
def rAddr := 57
def rFifty := 58
def rThree := 59
def rSeven := 60
def rCoin := 61
def rC2 := 62
def rVB := 63    -- visited array base
def rXmax := 64
def rHi := 65
def rInner := 66
def rTab := 67
def rQ := 68
def rMm := 69
def rIdx := 70
def rA := 71     -- constant A
def rKk := 72    -- constant k
def rP15 := 73
def rP8 := 74
def rP50 := 75
def rP49 := 76
def rCeil15 := 77
def rCeil50 := 78
def rBase := 79
def rTb := 80    -- trialBlock
def rOb := 81    -- outerBlocks

/-- Registers of the input-field reader (BinaryRead.readField). -/
def readRegs : Fin 7 ↪ ℕ := ⟨fun i => cell (50 + i.val), fun a b h => by
  simp only [cell] at h; exact Fin.ext (by omega)⟩

/-- Interpreter registers. -/
def iregs : IRegs :=
  { pc := cell 100, run := cell 101, big := cell 102, logb := cell 103, cnt := cell 104,
    xb := cell 105, xlen := cell 106, co := cell 107, cl := cell 108, cap := cell 109,
    one := cell 110, zero := cell 111, ds := cell 112, t1 := cell 113, t2 := cell 114,
    t3 := cell 115, t4 := cell 116, t5 := cell 117, t6 := cell 118 }

/-- First address of the simulated input string. -/
def xBase : ℕ := 300

/-- `r := l op r'` as one arithmetic-circuit assignment. -/
def asg (d : ℕ) (e : Expression) : Assignment := ⟨d, e⟩

def circ (as : List Assignment) : Cmd := Circuit.cmd as

/-- Ascending loop over register `i` from its current value up to the value of `stop`. -/
def loop (i stop : ℕ) (body : Cmd) : Cmd := forRange (cell i) (cell stop) (cell rOne) body

/-- `if l ≤ r then yes else no` on logical registers. -/
def ifLe (l r : ℕ) (yes no : Cmd) : Cmd := .branch (cell l) (cell r) yes no

/-- Store the value of register `val` at absolute address `XB + cursor`, advance the cursor. -/
def putBit (val : ℕ) : Cmd :=
  circ [asg rAddr (.literal xBase), asg rAddr (.add rAddr rXc)] |>.seq
    (.seq (.op (.store (cell rAddr) (cell val))) (circ [asg rXc (.add rXc rOne)]))

/-- Emit the self-delimiting code `encNat` of the value of register `rK` (destroys `rK`). -/
def emitK : Cmd :=
  .seq (.whileGt (cell rK) (cell rZero)
    (.seq (putBit rOne) (.seq (circ [asg rTmp (.arithmetic .mod rK rTwo)])
      (.seq (putBit rTmp) (circ [asg rK (.arithmetic .div rK rTwo)])))))
    (putBit rZero)

/-- Emit `encNat` of register `src`. -/
def emit (src : ℕ) : Cmd := .seq (circ [asg rK (.add src rZero)]) emitK

/-- `rTmp := bit `(value of idx)` of register `src`` (i.e. `(src / 2^idx) % 2`). -/
def bitOf (src idx : ℕ) : List Assignment :=
  [asg rTmp (.arithmetic .pow rTwo idx), asg rTmp (.arithmetic .div src rTmp),
   asg rTmp (.arithmetic .mod rTmp rTwo)]

/-- Compute the arc stored in slot `rSlot` of the padded parity instance into `rTv rHv rWv`. -/
def slotArc : Cmd :=
  .seq (circ ([asg rQ (.arithmetic .div rSlot rThree), asg rLl (.arithmetic .mod rSlot rThree),
      asg rU (.arithmetic .div rQ rN), asg rV (.arithmetic .mod rQ rN),
      asg rIdx (.arithmetic .mul rU rN), asg rIdx (.add rIdx rV)] ++ bitOf rGp rIdx ++
      [asg rCand (.add rTmp rZero),
       -- symbol of the pair
       asg rTmp2 (.arithmetic .pow rFifty rIdx), asg rTmp2 (.arithmetic .div rSym rTmp2),
       asg rTmp2 (.arithmetic .mod rTmp2 rFifty),
       -- weight of (v, l)
       asg rIdx (.arithmetic .mul rV rThree), asg rIdx (.add rIdx rLl),
       asg rWv (.arithmetic .pow rW rIdx), asg rWv (.arithmetic .div rWt rWv),
       asg rWv (.arithmetic .mod rWv rW), asg rWv (.add rWv rOne),
       -- default (padding) arc
       asg rTv (.add rS rZero), asg rHv (.add rS rZero)]))
  -- mask of the symbol: mm = 0 if symbol = 0, else 1 + (symbol-1)/7; test bit l
  (.seq (ifLe rTmp2 rZero (circ [asg rMm (.literal 0)])
      (circ [asg rMm (.sub rTmp2 rOne), asg rMm (.arithmetic .div rMm rSeven),
        asg rMm (.add rMm rOne)]))
    (.seq (circ (bitOf rMm rLl))
      -- arc present iff adjacency bit, mask bit, u ≠ v, v ≠ s, u ≠ t
      (ifLe rCand rZero (circ [asg rWv (.literal 0)])
        (ifLe rTmp rZero (circ [asg rWv (.literal 0)])
          (ifEqual (cell rU) (cell rV) (circ [asg rWv (.literal 0)])
            (ifEqual (cell rV) (cell rS) (circ [asg rWv (.literal 0)])
              (ifEqual (cell rU) (cell rT) (circ [asg rWv (.literal 0)])
                (circ [asg rTv (.add rU rZero), asg rHv (.add rV rZero)]))))))))

/-- Write `encodeParityInstance` of the decoded candidate at `xBase` and set `iregs.xlen`. -/
def buildX : Cmd :=
  .seq (circ [asg rXc (.literal 0)])
  (.seq (emit rN) (.seq (emit rM)
  (.seq (.seq (circ [asg rSlot (.literal 0)])
      (loop rSlot rM (.seq slotArc (.seq (emit rTv) (.seq (emit rHv) (emit rWv))))))
  (.seq (emit rS) (.seq (emit rT) (.seq (putBit rZero) (.seq (emit rB)
    (circ [asg 106 (.add rXc rZero)]))))))))
    -- cell 106 = iregs.xlen

/-- Run the parity program `Q` on the simulated input with tape `rJ`, add the result to the
vote count. -/
def runTape (Q : Program) : Cmd :=
  .seq (circ [asg 107 (.arithmetic .mul rJ rL), asg 107 (.add 107 rTapeBase),
      asg 108 (.add rL rZero), asg 100 (.literal 0), asg 101 (.literal 1),
      asg 104 (.literal 0), asg 109 (.literal 2)])
    (.seq (.op (.const 0 0)) (.seq (call iregs Q) (circ [asg rVotes (.add rVotes 109)])))

/-- Read the seed block of trial `rI` into `rDv` (bits read as 1 exactly when the coin is 1). -/
def readSeed : Cmd :=
  .seq (circ [asg rDv (.literal 0), asg rPow (.literal 1), asg rSeedPos (.arithmetic .mul rI rSw),
      asg rJ (.literal 0)])
    (loop rJ rSw (.seq (circ [asg rAddr (.add rSeedPos rJ)])
      (.seq (.op (.coin (cell rCoin) (cell rAddr)))
        (.seq (ifLe rCoin rZero .skip (ifLe rCoin rOne (circ [asg rDv (.add rDv rPow)]) .skip))
          (circ [asg rPow (.add rPow rPow)])))))

/-- Decode the draw rank `rDv < rDc` into the endpoints, tables and target. -/
def decodeDraw : Cmd :=
  circ [asg rHi (.arithmetic .div rDv rIn), asg rInner (.arithmetic .mod rDv rIn),
    asg rS (.arithmetic .div rHi rN), asg rT (.arithmetic .mod rHi rN),
    asg rB (.arithmetic .mod rInner rBm1), asg rTab (.arithmetic .div rInner rBm1),
    asg rSym (.arithmetic .div rTab rPW), asg rWt (.arithmetic .mod rTab rPW)]

/-- One trial of the amplified decision on the candidate graph `rGp`. -/
def trial (Q : Program) : Cmd :=
  .seq readSeed
  (ifLe rDc rDv .skip
    (.seq decodeDraw
    (ifEqual (cell rS) (cell rT) .skip
      (.seq (circ ([asg rIdx (.arithmetic .mul rT rN), asg rIdx (.add rIdx rS)] ++ bitOf rGp rIdx))
      (ifLe rTmp rZero .skip
        (.seq buildX
        (.seq (circ [asg rVotes (.literal 0), asg rJ (.literal 0)])
        (.seq (loop rJ rR2 (runTape Q))
          (ifLe rVotes rR .skip (circ [asg rFlag (.literal 1)]))))))))))

/-- The amplified two-sided decision `twoSided` on `rGp`, result in `rFlag`. -/
def decideCmd (Q : Program) : Cmd :=
  .seq (circ [asg rFlag (.literal 0), asg rI (.literal 0)]) (loop rI rTrials (trial Q))

/-- Greedy edge deletion over all `n*n` arcs in row-major order. -/
def prune (Q : Program) : Cmd :=
  .seq (circ [asg rE (.literal 0)])
    (loop rE rN2 (.seq (circ (bitOf rG rE))
      (ifLe rTmp rZero .skip
        (.seq (circ [asg rTmp2 (.arithmetic .pow rTwo rE), asg rGp (.sub rG rTmp2)])
          (.seq (decideCmd Q) (ifLe rFlag rZero .skip (circ [asg rG (.add rGp rZero)])))))))

/-- Read the adjacency matrix bits into the packed graph `rG`. -/
def readGraph : Cmd :=
  .seq (circ [asg rG (.literal 0), asg rPow (.literal 1), asg rE (.literal 0)])
    (loop rE rN2 (.seq (circ [asg rAddr (.add rCur rE)])
      (.seq (.op (.input (cell rCoin) (cell rAddr)))
        (.seq (ifLe rCoin rZero .skip (circ [asg rG (.add rG rPow)]))
          (circ [asg rPow (.add rPow rPow)])))))

/-- Visited test and successor search of the certificate check. -/
def certifyStep : Cmd :=
  .seq (circ [asg rAddr (.add rVB rU)])
  (.seq (.op (.load (cell rTmp) (cell rAddr)))
  (.seq (ifLe rTmp rZero .skip (circ [asg rOk (.literal 0)]))
  (.seq (.op (.store (cell rAddr) (cell rOne)))
  (.seq (circ [asg rNext (.add rU rZero), asg rFound (.literal 0), asg rV (.literal 0)])
  (.seq (loop rV rN (.seq (circ ([asg rIdx (.arithmetic .mul rU rN), asg rIdx (.add rIdx rV)] ++
          bitOf rG rIdx))
        (ifLe rTmp rZero .skip (ifLe rFound rZero (circ [asg rNext (.add rV rZero),
          asg rFound (.literal 1)]) .skip))))
  (.seq (ifLe rFound rZero (circ [asg rOk (.literal 0)]) .skip)
    (circ [asg rU (.add rNext rZero)])))))))

/-- The certificate check `certify n R` on the packed graph `rG`, result output. -/
def certify : Cmd :=
  .seq (circ [asg rU (.literal 0), asg rOk (.literal 1), asg rJ (.literal 0)])
  (.seq (loop rJ rN certifyStep)
  (.seq (ifLe rU rZero .skip (circ [asg rOk (.literal 0)]))
    (.op (.output (cell rOk)))))

def rSix := 82
def rC49 := 83

/-- Registers of the ceiling-logarithm routine. -/
def logRegs : Fin 4 ↪ ℕ := ⟨fun i => cell (90 + i.val), fun a b h => by
  simp only [cell] at h; exact Fin.ext (by omega)⟩

/-- `ceilLog` of register `src` into register `dst` (via the ceiling-log routine). -/
def clogInto (dst src : ℕ) : Cmd :=
  .seq (circ [asg 90 (.add src rZero)]) (.seq (ceilLog logRegs) (circ [asg dst (.add 92 rZero)]))

/-- All parameters of the search as functions of `n` and the constants `A`, `k`. -/
def params : Cmd :=
  .seq (circ [
    asg rN2 (.arithmetic .mul rN rN), asg rM (.arithmetic .mul rThree rN2),
    asg rTmp (.sub rN rOne), asg rW (.arithmetic .mul rSix rTmp),
    asg rBm1 (.arithmetic .mul rTmp rW), asg rBm1 (.add rBm1 rOne),
    asg rTmp2 (.arithmetic .mul rN rThree), asg rPW (.arithmetic .pow rW rTmp2),
    asg rP50 (.arithmetic .pow rFifty rN2), asg rIn (.arithmetic .mul rP50 rPW),
    asg rIn (.arithmetic .mul rIn rBm1), asg rDc (.arithmetic .mul rN2 rIn),
    -- outerCeil n = (50^n + 49^n - 1) / 49^n
    asg rP50 (.arithmetic .pow rFifty rN), asg rP49 (.arithmetic .pow rC49 rN),
    asg rCeil50 (.add rP50 rP49), asg rCeil50 (.sub rCeil50 rOne),
    asg rCeil50 (.arithmetic .div rCeil50 rP49),
    -- trials = 4*(n*n*(Bmax+1))*outerCeil * (6*n*n+6)
    asg rTb (.arithmetic .mul rN2 rBm1), asg rTmp (.literal 4), asg rTb (.arithmetic .mul rTmp rTb),
    asg rTb (.arithmetic .mul rTb rCeil50),
    asg rOb (.arithmetic .mul rSix rN2), asg rOb (.add rOb rSix),
    asg rTrials (.arithmetic .mul rTb rOb),
    -- coinSpan = A * ceil((15/8)^n) * (n + n*n*3 + 6*(n-1) + 1)^k
    asg rTmp (.literal 15), asg rP15 (.arithmetic .pow rTmp rN),
    asg rTmp (.literal 8), asg rP8 (.arithmetic .pow rTmp rN),
    asg rCeil15 (.add rP15 rP8), asg rCeil15 (.sub rCeil15 rOne),
    asg rCeil15 (.arithmetic .div rCeil15 rP8),
    asg rBase (.add rN rM), asg rBase (.add rBase rW), asg rBase (.add rBase rOne),
    asg rBase (.arithmetic .pow rBase rKk),
    asg rL (.arithmetic .mul rA rCeil15), asg rL (.arithmetic .mul rL rBase),
    asg rTmp (.add rTrials rOne)])
  (.seq (clogInto rTmp2 rTmp)
  (.seq (clogInto rSw rDc)
    (circ [
    -- majorityHalf = 2*((trials).size + outerBlocks); size x = clog 2 (x+1)
    asg rR (.add rTmp2 rOb), asg rR (.add rR rR), asg rR2 (.add rR rR),
    asg rTapeBase (.arithmetic .mul rTrials rSw),
    -- layout: x at xBase, visited array, log, simulated memory
    asg rXmax (.add rN rOne), asg rTmp (.arithmetic .mul rXmax rXmax),
    asg rXmax (.arithmetic .mul rTmp rXmax), asg rTmp (.literal 128),
    asg rXmax (.arithmetic .mul rTmp rXmax),
    asg rVB (.literal xBase), asg rVB (.add rVB rXmax),
    asg 103 (.add rVB rN), asg 102 (.add 103 rL), asg 102 (.add 102 rOne),
    asg 105 (.literal xBase), asg 110 (.literal 1), asg 111 (.literal 0)])))

/-- The full host program for parity program `Q` and constants `A k`. -/
def main (Q : Program) (A k : ℕ) : Cmd :=
  .seq (circ [asg rOne (.literal 1), asg rZero (.literal 0), asg rTwo (.literal 2),
      asg rThree (.literal 3), asg rSix (.literal 6), asg rSeven (.literal 7),
      asg rFifty (.literal 50), asg rC49 (.literal 49), asg rA (.literal A), asg rKk (.literal k),
      asg 50 (.literal 0)])
  (.seq (BinaryRead.readField readRegs)
  (.seq (circ [asg rN (.add 51 rZero), asg rCur (.add 50 rZero)])
  (ifLe rN rOne
    (ifLe rN rZero (.op (.output (cell rZero)))
      (.seq (.op (.input (cell rCoin) (cell rCur))) (.op (.output (cell rCoin)))))
    (.seq params (.seq readGraph (.seq (prune Q) certify))))))

end DirectedHamiltonicity.Main.CycleHost

namespace DirectedHamiltonicity.Main.CycleHost

open TargetedSamplers TargetedSamplers.Structured TargetedSamplers.Structured.Word
open DirectedHamiltonicity.Main.CycleReduction

/-! ## Vocabulary of the sub-routine specifications -/

/-- The constant registers hold `1, 0, 2, 3, 6, 7, 50, 49`. -/
structure Consts (s : Store) : Prop where
  one : s.mem (cell rOne) = 1
  zero : s.mem (cell rZero) = 0
  two : s.mem (cell rTwo) = 2
  three : s.mem (cell rThree) = 3
  six : s.mem (cell rSix) = 6
  seven : s.mem (cell rSeven) = 7
  fifty : s.mem (cell rFifty) = 50
  c49 : s.mem (cell rC49) = 49

/-- The parity-instance encoding of a candidate draw (the string `candidateInput` produces). -/
noncomputable def candX {n : ℕ} (adj : Fin n → Fin n → Bool) (s t : Fin n) (z : MatrixSeed n)
    (B : ℕ) : List Bool :=
  let a := pathAdj adj s t
  let r := restrictedSeed a s z
  parityInput a (fun e => copyMask (r.1 e)) s t (clean_no_in adj s t) (labelWeight s r.2) B

/-- Every logical cell (address ≥ 14) outside the listed registers and satisfying `outside`
keeps its value, and the output is unchanged. -/
def Kept (dirty : List ℕ) (u v : Store) (outside : ℕ → Prop) : Prop :=
  v.out = u.out ∧ ∀ a, 14 ≤ a → (∀ d ∈ dirty, a ≠ cell d) → outside a → v.mem a = u.mem a

def buildXDirty : List ℕ :=
  [rXc, rK, rTmp, rSlot, rQ, rLl, rU, rV, rIdx, rCand, rTmp2, rWv, rTv, rHv, rMm, rAddr, 106]

def certifyDirty : List ℕ := [rU, rOk, rJ, rAddr, rTmp, rNext, rFound, rV, rIdx]

def readGraphDirty : List ℕ := [rG, rPow, rE, rAddr, rCoin]

def readSeedDirty : List ℕ := [rDv, rPow, rSeedPos, rJ, rAddr, rCoin]

def decodeDirty : List ℕ := [rHi, rInner, rS, rT, rB, rTab, rSym, rWt]

def paramsDirty : List ℕ :=
  [rN2, rM, rTmp, rW, rBm1, rTmp2, rPW, rP50, rIn, rDc, rP49, rCeil50, rTb, rOb, rTrials, rP15,
   rP8, rCeil15, rBase, rL, rSw, rR, rR2, rTapeBase, rXmax, rVB, 103, 102, 105, 110, 111,
   90, 91, 92, 93]

end DirectedHamiltonicity.Main.CycleHost


