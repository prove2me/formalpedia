-- Prove2me | Definitions.Def_FourBlockIP350_Main_Supplement_OracleTuring
-- name    : FourBlockIP350_Main_Supplement_OracleTuring
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T18:06:16.403956+00:00
-- url     : https://prove2.me/theorems/044e9440-a69f-4293-bb9d-998fa0a655f4
-- title:
--   Multitape Turing machines with a three-way comparison oracle (Appendix B computation model)
-- statement:
--   This file extends the deterministic multitape Turing machine used for the binary running times of the mission (the published model `IntMul.MultitapeTM`) by access to a **comparison oracle**, the computation model in which Appendix B of the paper measures time.
--
--   An **oracle machine** $P$ consists of a multitape machine $M$ together with
--
--   1. a designated **query tape**, which is a work tape (neither the input tape nor the output tape);
--   2. a **query state** $q_{?}$, different from the halting state, and three **answer states** $q_{<}, q_{=}, q_{>}$.
--
--   An oracle is a map $O$ from bit words to the three-element set $\{<,=,>\}$. A step of $P$ with oracle $O$ from a configuration that is not in the query state is an ordinary step of $M$. From a configuration in the query state, the machine reads the bit word $w$ written on the query tape from cell $1$ up to the first non-bit symbol, and moves to the answer state $q_{O(w)}$; tapes and heads are unchanged. The oracle's answer is only one of three symbols: no number ever enters the configuration.
--
--   Running time charges the oracle. Given a cost function $c$ on query words, the **charged time** of the first $t$ steps is
--   $$t+\sum_{j<t,\ \text{step } j \text{ in } q_{?}} c(w_j),$$
--   where $w_j$ is the query word at step $j$. The machine **computes output $v$ on input $u$ within $T$** with oracle $O$ and cost $c$ if, started on input $u$ (input tape $\triangleright u\#$, as in the mission's binary model), after some $t$ steps it is in the halting state with exactly $v$ on its output tape and its charged time is at most $T$.
--
--   The cost function used for the paper's oracle is $c(w)=(1+L+|w|)^e$, where $L$ is the encoding length of the instance and $e$ is a fixed exponent: this is the source's oracle answer time $(|I|+\operatorname{enc}(z,z'))^{O(1)}$.
--
--   **Formalization Note** The general object (an oracle Turing machine over the base multitape model) is kept separate from the integer-programming data, which is defined in the companion file `FourBlockIP350_Main_Supplement_SeparableIP`. The published real-RAM model `FourBlockIP350_Main_OracleMachine` of Theorem 2.9 is an arithmetic model on a lattice ball and is not this model.
-- source:
--   Klaus Jansen, Felix Ohnesorge, Corinna Wambsganz, A Fixed-Parameter Algorithm for 4-Block Integer Programming, STOC 2027 submission #350 (October 2026), p. 21, §B.1 (comparison oracle O_Φ, lines 630–636, and Theorem B.2); binary-time convention of p. 3, Theorem 1.1

import Mathlib
import Definitions.Def_IntMul_MultitapeModel

namespace FourBlockIP350.Main.Supplement

/-- A multitape machine of the base model `IntMul.MultitapeTM` with comparison-oracle access
(Jansen–Ohnesorge–Wambsganz, Appendix B, p. 21): a designated work tape is the query tape,
and a query state `qQuery` is answered in one step by a three-way answer, moving to `qLt`,
`qEq` or `qGt`. The oracle answer is only an `Ordering`; no number enters the configuration. -/
structure OracleTM where
  /-- the underlying multitape machine; its transition at `qQuery` is never used -/
  M : IntMul.MultitapeTM
  /-- the query tape, a work tape (neither the input tape `0` nor the output tape `1`) -/
  queryTape : Fin M.k
  queryTape_work : 2 ≤ queryTape.val
  /-- the query state -/
  qQuery : M.K
  /-- the states entered after the answers `<`, `=`, `>` -/
  qLt : M.K
  qEq : M.K
  qGt : M.K
  query_ne_halt : qQuery ≠ M.qHalt

namespace OracleTM

variable (P : OracleTM)

open Classical in
/-- The bit word on a tape: the maximal run of bit symbols starting at cell `1`
(empty if every cell from `1` on holds a bit, which never happens in a finite run). -/
noncomputable def tapeBits (tape : ℕ → P.M.Sym) : List Bool :=
  if h : ∃ m : ℕ, tape (m + 1) ≠ P.M.zero ∧ tape (m + 1) ≠ P.M.one then
    List.ofFn (fun i : Fin (Nat.find h) => decide (tape (i.val + 1) = P.M.one))
  else []

/-- The state entered after the oracle answers `o`. -/
def answerState : Ordering → P.M.K
  | .lt => P.qLt
  | .eq => P.qEq
  | .gt => P.qGt

open Classical in
/-- One step with oracle `O`: in the query state, the machine enters the answer state for
`O w`, where `w` is the word on the query tape; tapes and heads are unchanged. Every other
step is a step of the underlying machine. -/
noncomputable def step (O : List Bool → Ordering) (c : P.M.Cfg) : P.M.Cfg :=
  if c.state = P.qQuery then
    { c with state := P.answerState (O (P.tapeBits (c.cells P.queryTape))) }
  else P.M.step c

/-- The configuration after `t` steps on input `x` (input tape `▷ x # □ …`, as in the base
`ComputesWithin`, whose second input word is empty). -/
noncomputable def run (O : List Bool → Ordering) (x : List Bool) (t : ℕ) : P.M.Cfg :=
  (P.step O)^[t] (P.M.initCfg x [])

open Classical in
/-- Total oracle charge of the first `t` steps: every step made in the query state is charged
`cost w`, where `w` is the query word. -/
noncomputable def oracleCharge (O : List Bool → Ordering) (x : List Bool)
    (cost : List Bool → ℕ) (t : ℕ) : ℕ :=
  ∑ j ∈ Finset.range t,
    if (P.run O x j).state = P.qQuery then
      cost (P.tapeBits ((P.run O x j).cells P.queryTape))
    else 0

/-- With oracle `O`, on input `input` the machine halts after some `t` steps with exactly
`output` on its output tape, and `t` plus the oracle charge of those steps is at most `T`. -/
def ComputesWithin (O : List Bool → Ordering) (cost : List Bool → ℕ)
    (input output : List Bool) (T : ℕ) : Prop :=
  ∃ t : ℕ, (P.run O input t).state = P.M.qHalt ∧
    (P.run O input t).cells P.M.outTape = P.M.tapeOf (output.map P.M.bitSym) ∧
    t + P.oracleCharge O input cost t ≤ T

end OracleTM

/-- Oracle answer time `(1 + L + |w|)^e` for a query word `w`, where `L` is the instance
length: the source's `(|I| + enc(z, z'))^{O(1)}` with exponent `e`. -/
def polyOracleCost (L e : ℕ) (w : List Bool) : ℕ := (1 + L + w.length) ^ e

end FourBlockIP350.Main.Supplement


