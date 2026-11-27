-- Prove2me | Definitions.Def_LogCostRAM_Interpreter
-- name    : LogCostRAM_Interpreter
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-27T03:59:36.605006+00:00
-- url     : https://prove2.me/theorems/52fbfecb-ea45-5d3d-83cb-ab755f6e631f
-- title:
--   A structured interpreter for a fixed log-cost RAM program
-- statement:
--   A structured interpreter that runs a fixed RAM program $Q$ inside a larger structured routine.
--
--   The simulated memory cell $u$ is stored at host address $\mathrm{big}+u$. Every simulated write also records the simulated address in a log at $\mathrm{logb}+\mathrm{cnt}$; after the simulated program halts, the routine `clear` zeroes every logged cell and the log itself, so that the host memory is restored. The simulated input string $x$ is stored bitwise at host addresses $\mathrm{xb},\dots,\mathrm{xb}+|x|-1$. The simulated coin tape is the window
--   $$\bigl(c_{\mathrm{co}},c_{\mathrm{co}+1},\dots,c_{\mathrm{co}+\mathrm{cl}-1}\bigr)$$
--   of the host coins $c$, where a missing host coin reads as $0$; simulated coins beyond the window read as the end symbol $2$. The witness tape is empty and the oracle answers $0$. The last output bit of the simulated machine is recorded in a capture register.
--
--   The routine `call r Q` interprets $Q$ until it halts, restores the memory and resets the scratch registers. It lets a single host machine use an arbitrary program, given only as a finite instruction list, as a subroutine on inputs that the host builds in its own memory.
--
--   **Formalization Note** `handler p i` is the host code for instruction `i` at address `p`; `interp` dispatches on the simulated program counter with `dispatch`.
-- source:
--   Engineering definition supporting the formalization of T. Koana and S. Kumabe, Breaking the 2^n barrier for directed hamiltonicity (STOC 2027 submission #811), Theorem 1 and Section 2 (PDF pp. 2-5), on the log-cost RAM of Def_TargetedSamplers_Machine.

import Definitions.Def_LogCostRAM_WorkExecution

set_option autoImplicit false

namespace TargetedSamplers.Structured.Interp

/-!
# A structured interpreter for a fixed RAM program

`interp Q r` runs the fixed program `Q : Program` on a simulated machine. The simulated memory
cell `u` lives at host address `big + u` (`big` in register `r.big`). Every simulated write logs
the simulated address at host address `logb + cnt` and increments `cnt`; `clear r` afterwards
zeroes every logged simulated cell and the log, so that the host memory is restored. The simulated
input string is stored bitwise at host addresses `xb, …, xb + xlen - 1`; simulated coin `u < cl` is
the host coin `co + u` read as `1` exactly when it is `1` (missing or `false` host bits read as `0`),
and simulated coins `u ≥ cl` read as the end symbol `2`. The witness is empty and the oracle answers
`0`. The last simulated output bit is recorded in `r.cap`. The simulated program counter is
`r.pc`; `r.run` is `1` while the simulated machine is live.
-/

/-- Host registers of the interpreter. -/
structure IRegs where
  pc : ℕ
  run : ℕ
  big : ℕ
  logb : ℕ
  cnt : ℕ
  xb : ℕ
  xlen : ℕ
  co : ℕ
  cl : ℕ
  cap : ℕ
  one : ℕ
  zero : ℕ
  ds : ℕ
  t1 : ℕ
  t2 : ℕ
  t3 : ℕ
  t4 : ℕ
  t5 : ℕ
  t6 : ℕ

def IRegs.all (r : IRegs) : List ℕ :=
  [r.pc, r.run, r.big, r.logb, r.cnt, r.xb, r.xlen, r.co, r.cl, r.cap, r.one, r.zero, r.ds,
   r.t1, r.t2, r.t3, r.t4, r.t5, r.t6]

variable (r : IRegs)

/-- `dst := simulated cell x` for a static `x` (uses `t1`). -/
def readStatic (dst x : ℕ) : Cmd :=
  .seq (.op (.const r.t1 x)) (.seq (.op (.add r.t1 r.t1 r.big)) (.op (.load dst r.t1)))

/-- `dst := simulated cell (value of register ra)` (uses `t1`). -/
def readDyn (dst ra : ℕ) : Cmd :=
  .seq (.op (.add r.t1 ra r.big)) (.op (.load dst r.t1))

/-- simulated cell (value of `ra`) := value of `rv`, and log the simulated address
(uses `t2`, `t3`). -/
def writeDyn (ra rv : ℕ) : Cmd :=
  .seq (.op (.add r.t2 ra r.big)) (.seq (.op (.store r.t2 rv))
    (.seq (.op (.add r.t3 r.logb r.cnt)) (.seq (.op (.store r.t3 ra)) (.op (.add r.cnt r.cnt r.one)))))

/-- simulated cell `d` := value of `rv` (uses `t4`, `t2`, `t3`). -/
def writeStatic (d rv : ℕ) : Cmd := .seq (.op (.const r.t4 d)) (writeDyn r r.t4 rv)

def setPC (p : ℕ) : Cmd := .op (.const r.pc p)

/-- The handler of instruction `i` located at simulated address `p`. -/
def handler (p : ℕ) : Instr → Cmd
  | .const d c => .seq (.op (.const r.t5 c)) (.seq (writeStatic r d r.t5) (setPC r (p+1)))
  | .add d a b => .seq (readStatic r r.t5 a) (.seq (readStatic r r.t6 b)
      (.seq (.op (.add r.t5 r.t5 r.t6)) (.seq (writeStatic r d r.t5) (setPC r (p+1)))))
  | .monus d a b => .seq (readStatic r r.t5 a) (.seq (readStatic r r.t6 b)
      (.seq (.op (.sub r.t5 r.t5 r.t6)) (.seq (writeStatic r d r.t5) (setPC r (p+1)))))
  | .load d a => .seq (readStatic r r.t5 a) (.seq (readDyn r r.t6 r.t5)
      (.seq (writeStatic r d r.t6) (setPC r (p+1))))
  | .store a b => .seq (readStatic r r.t5 a) (.seq (readStatic r r.t6 b)
      (.seq (writeDyn r r.t5 r.t6) (setPC r (p+1))))
  | .jle a b target => .seq (readStatic r r.t5 a) (.seq (readStatic r r.t6 b)
      (.branch r.t5 r.t6 (setPC r target) (setPC r (p+1))))
  | .inputLength d => .seq (writeStatic r d r.xlen) (setPC r (p+1))
  | .readInput d a => .seq (readStatic r r.t5 a)
      (.seq (.branch r.xlen r.t5 (.op (.const r.t6 2))
        (.seq (.op (.add r.t1 r.xb r.t5)) (.op (.load r.t6 r.t1))))
      (.seq (writeStatic r d r.t6) (setPC r (p+1))))
  | .readCoin d a => .seq (readStatic r r.t5 a)
      (.seq (.branch r.cl r.t5 (.op (.const r.t6 2))
        (.seq (.op (.add r.t1 r.co r.t5)) (.seq (.op (.coin r.t6 r.t1))
          (.branch r.t6 r.zero .skip (.branch r.t6 r.one .skip (.op (.const r.t6 0)))))))
      (.seq (writeStatic r d r.t6) (setPC r (p+1))))
  | .readWitness d => .seq (.op (.const r.t6 2)) (.seq (writeStatic r d r.t6) (setPC r (p+1)))
  | .query d _ _ => .seq (.op (.const r.t6 0)) (.seq (writeStatic r d r.t6) (setPC r (p+1)))
  | .output a => .seq (readStatic r r.t5 a)
      (.seq (.branch r.t5 r.zero (.op (.const r.cap 0)) (.op (.const r.cap 1))) (setPC r (p+1)))
  | .outputBot => .op (.const r.run 0)
  | .halt => .op (.const r.run 0)

/-- Handlers of the instructions of `Q`, in program order starting at address `p`. -/
def handlers : ℕ → Program → List Cmd
  | _, [] => []
  | p, i :: is => handler r p i :: handlers (p+1) is

/-- Run the simulated machine until it halts. -/
def interp (Q : Program) : Cmd :=
  .whileGt r.run r.zero (dispatch r.pc r.ds 0 (handlers r 0 Q))

/-- Zero every logged simulated cell and the log, then reset the log counter. -/
def clear : Cmd :=
  .seq (.op (.const r.t5 0)) (.seq (.whileGt r.cnt r.t5
    (.seq (.op (.add r.t1 r.logb r.t5)) (.seq (.op (.load r.t6 r.t1))
      (.seq (.op (.add r.t2 r.big r.t6)) (.seq (.op (.store r.t2 r.zero))
        (.seq (.op (.store r.t1 r.zero)) (.op (.add r.t5 r.t5 r.one))))))))
    (.op (.const r.cnt 0)))

/-- Reset the scratch registers and the program counter to zero. -/
def resets : Cmd :=
  .seq (.op (.const r.pc 0)) (.seq (.op (.const r.ds 0)) (.seq (.op (.const r.t1 0))
    (.seq (.op (.const r.t2 0)) (.seq (.op (.const r.t3 0)) (.seq (.op (.const r.t4 0))
      (.seq (.op (.const r.t5 0)) (.op (.const r.t6 0))))))))

/-- Interpret, restore the memory and reset the scratch registers. -/
def call (Q : Program) : Cmd := .seq (interp r Q) (.seq (clear r) (resets r))

/-- The simulated coin string: `cl` host coins starting at `co`, missing bits read as `false`. -/
def windowCoins (coins : List Bool) (co cl : ℕ) : List Bool :=
  List.ofFn fun u : Fin cl => coins[co + u.val]?.getD false

/-- The capture register value for an output string. -/
def capValue (out : List Bool) : ℕ :=
  match out.getLast? with
  | none => 2
  | some b => b.toNat

end TargetedSamplers.Structured.Interp


