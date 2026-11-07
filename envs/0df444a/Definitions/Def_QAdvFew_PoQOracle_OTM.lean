-- Prove2me | Definitions.Def_QAdvFew_PoQOracle_OTM
-- name    : QAdvFew_PoQOracle_OTM
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T10:48:54.739617+00:00
-- url     : https://prove2.me/theorems/21d2ddb0-8fdc-41d4-9d2a-8da414ce9ff6
-- title:
--   Oracle Turing machine
-- statement:
--   A deterministic **oracle Turing machine** has a two-way infinite work tape and a two-way infinite query tape, finitely many states and finitely many tape symbols, and a transition table. Six states are designated: start, accept, reject, query, answer yes and answer no.
--
--   In the query state the machine moves to the yes or no state according to the value of the oracle on the bit string on its query tape, with both tapes unchanged. Halting configurations are fixed points. This module also defines the configuration, one step, the run for $T$ steps, the result after $T$ steps (accepted, rejected or not halted), the output on the work tape, and the **space** used, which is the number of cells visited on both tapes, the input cells and the query tape included (Definition 3.5).
--
--   **Formalization Note** States and symbols are finite sets $\{0,\dots,k+5\}$ and $\{0,\dots,g+2\}$, so a machine is a finite object with a bit-string code. The sets $S_t^{\mathsf{PSPACE}}$ and $S_t^{\mathsf{NP}}$ of §4.1 need this.
-- source:
--   Goldin, Lombardi, Morimae, Quantum Advantage has Few Complexity Implications, arXiv:2611.05303v1, §3.2.2–§3.2.3 and Definitions 3.1–3.5, pp. 12–13 (PDF pp. 14–15)

import Mathlib
import Definitions.Def_QAdvFew_PoQOracle_Oracle

open QAlgorithms.Complexity

namespace QAdvFew.PoQOracle

/-- A deterministic **oracle Turing machine** (Goldin, Lombardi, Morimae, *Quantum Advantage has Few
Complexity Implications*, arXiv:2611.05303v1, §3.2.2–§3.2.3, p. 12 (PDF p. 14), Definitions 3.1–3.5,
pp. 12–13 (PDF pp. 14–15)), with a work tape and a query tape, both two-way infinite.

The states are `Fin (k + 6)`: `0` start, `1` accept, `2` reject, `3` query, `4` answer yes,
`5` answer no. The tape symbols are `Fin (g + 3)`: `0` blank, `1` the bit `0`, `2` the bit `1`.
`δ q a b = (q', a', m, b', m')`: in state `q` reading `a` on the work tape and `b` on the query tape,
write `a'` and `b'`, move the heads by `m - 1` and `m' - 1` (`m, m' ∈ {0, 1, 2}`), enter `q'`.

**Formalization Note** States and symbols are `Fin` types and `δ` is a finite table, so that a
machine is a finite object with a bit-string code (`OTM.code`), as the sets `S^PSPACE_t`, `S^NP_t`
of §4.1 require ("`(M, x)` takes less than `t` bits to specify"). -/
structure OTM where
  /-- number of states beyond the six designated ones -/
  k : ℕ
  /-- number of tape symbols beyond blank, `0` and `1` -/
  g : ℕ
  /-- the transition table -/
  δ : Fin (k + 6) → Fin (g + 3) → Fin (g + 3) →
    Fin (k + 6) × Fin (g + 3) × Fin 3 × Fin (g + 3) × Fin 3

namespace OTM

/-- A configuration: state, the two tapes with their head positions, and the leftmost and rightmost
cells visited so far on each tape (for the space bound of Definition 3.5). -/
structure Cfg (M : OTM) where
  state : Fin (M.k + 6)
  work : ℤ → Fin (M.g + 3)
  wh : ℤ
  query : ℤ → Fin (M.g + 3)
  qh : ℤ
  wlo : ℤ
  whi : ℤ
  qlo : ℤ
  qhi : ℤ

/-- The tape symbol of a bit. -/
def symOf (g : ℕ) (b : Bool) : Fin (g + 3) := if b then 2 else 1

/-- The bit of a tape symbol, if it is one. -/
def bitOf {g : ℕ} (a : Fin (g + 3)) : Option Bool :=
  if a = 1 then some false else if a = 2 then some true else none

/-- The bit string written on a tape from cell `0` up to the first non-bit cell (at most up to
cell `hi`, beyond which a tape is blank). -/
def readBits {g : ℕ} (tape : ℤ → Fin (g + 3)) (hi : ℤ) : Str :=
  (((List.range (hi + 1).toNat).map (fun i => bitOf (tape i))).takeWhile (·.isSome)).reduceOption

/-- The initial configuration on input `x`: `x` on the work tape from cell `0`, empty query tape. -/
def init (M : OTM) (x : Str) : M.Cfg where
  state := 0
  work := fun i => if 0 ≤ i ∧ i < x.length then symOf M.g (x.getD i.toNat false) else 0
  wh := 0
  query := fun _ => 0
  qh := 0
  wlo := 0
  whi := x.length
  qlo := 0
  qhi := 0

/-- One step with oracle `O`. Halting configurations are fixed. In the query state the machine
enters `yes` or `no` according to `O` applied to the bit string on the query tape (both tapes
unchanged). Otherwise it applies `δ`. -/
def step (M : OTM) (O : Oracle) (c : M.Cfg) : M.Cfg :=
  if c.state = 1 ∨ c.state = 2 then c
  else if c.state = 3 then { c with state := if O (readBits c.query c.qhi) then 4 else 5 }
  else
    let r := M.δ c.state (c.work c.wh) (c.query c.qh)
    let wh' := c.wh + (r.2.2.1.val : ℤ) - 1
    let qh' := c.qh + (r.2.2.2.2.val : ℤ) - 1
    { state := r.1
      work := Function.update c.work c.wh r.2.1
      wh := wh'
      query := Function.update c.query c.qh r.2.2.2.1
      qh := qh'
      wlo := min c.wlo wh'
      whi := max c.whi wh'
      qlo := min c.qlo qh'
      qhi := max c.qhi qh' }

/-- The configuration after `T` steps on input `x` with oracle `O`. -/
def runCfg (M : OTM) (O : Oracle) (x : Str) (T : ℕ) : M.Cfg :=
  (M.step O)^[T] (M.init x)

/-- The result after `T` steps: `some true` if `M` has accepted, `some false` if it has rejected,
`none` if it has not halted. Since halting configurations are fixed, `result M O x T ≠ none` says
that `M^O(x)` halts within `T` steps. -/
def result (M : OTM) (O : Oracle) (x : Str) (T : ℕ) : Option Bool :=
  let c := M.runCfg O x T
  if c.state = 1 then some true else if c.state = 2 then some false else none

/-- The output after `T` steps: the bit string on the work tape from cell `0` (the output of a
transducer, such as a verifier computing its next message). -/
def output (M : OTM) (O : Oracle) (x : Str) (T : ℕ) : Str :=
  let c := M.runCfg O x T
  readBits c.work c.whi

/-- The space used in the first `T` steps: the number of cells visited on the work tape (the input
cells included) plus the number of cells visited on the query tape (Definition 3.5: "uses polynomial
space including its query tape"). -/
def space (M : OTM) (O : Oracle) (x : Str) (T : ℕ) : ℕ :=
  let c := M.runCfg O x T
  (c.whi - c.wlo + 1).toNat + (c.qhi - c.qlo + 1).toNat

end OTM

end QAdvFew.PoQOracle


