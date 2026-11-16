-- Prove2me | Definitions.Def_GaussDiffSVP_Supplement_OracleRAM
-- name    : GaussDiffSVP_Supplement_OracleRAM
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T04:47:41.842252+00:00
-- url     : https://prove2.me/theorems/5f63fab5-c8d3-435a-9bba-8031f38b2abe
-- title:
--   Oracle RAM with an adversarial SVP oracle
-- statement:
--   The **oracle RAM** extends the randomized log-cost rational RAM by an SVP oracle. A run is a sequence of segments: each segment runs the program on the coin tape (fresh coins continue across segments) until it halts. If the halted output word starts with $1$, its remainder $q$ is an oracle query; the oracle's reply is written into the output cells, every other cell is kept, and the program restarts from its first instruction. Otherwise the run ends with the remaining output word.
--
--   An **SVP oracle rule** maps the previous queries and the current query to a reply; it is valid if, whenever the query is the word of a nonsingular rational basis $B'$, the reply is the coefficient vector of some shortest nonzero vector of $L(B')$, chosen by the rule.
--
--   The **work** of a run is the bit time of its own steps plus one per oracle call; its **workspace** is the largest bit space over the run; the number of calls and the list of queries are recorded.
--
--   This is the computational model of Theorem 12.6.
--
--   **Formalization Note** The published RAM has no oracle instruction; this is its oracle extension. The oracle rule is arbitrary among valid rules, so statements about it hold for every way of choosing among shortest vectors.
-- source:
--   Gao–Han–Hu, Gaussian Difference Dynamics: Breaking the 2^{n/2} Barrier for the Shortest Vector Problem and Discrete Gaussian Sampling, arXiv:2611.04336 (held version, sha256 233bf8bb…0692), Theorem 12.6, p.61; §1.2, p.6 and App. C.1.1, p.80 (computational model)

import Mathlib
import Definitions.Def_CosetTreeSVP_SVP_Algo

open MeasureTheory TwMSOCount.Main
open scoped ENNReal

namespace GaussDiffSVP.Supplement

/-- An adversarial **SVP oracle rule** (Gao–Han–Hu, *Gaussian Difference Dynamics*,
arXiv:2611.04336 (held version, sha256 233bf8bb…0692), Theorem 12.6, p.61: "The oracle may choose
among shortest vectors using any rule that depends on the current and previous queries"). A rule
`O hist q` maps the list `hist` of previous query words and the current query word `q` to a reply
word; it is a valid SVP oracle if, whenever `q = encBasis B'` is the word of a nonsingular rational
basis `B'`, the reply is the integer coefficient vector of **some** shortest nonzero vector of
`L(B')` (`SuperlatSVP.IsShortest`), whichever one the rule chooses. -/
def IsSVPOracle (O : List (List ℚ) → List ℚ → List ℚ) : Prop :=
  ∀ (hist : List (List ℚ)) (n : ℕ) (B' : Matrix (Fin n) (Fin n) ℚ), B'.det ≠ 0 →
    ∃ x : Fin n → ℤ, SuperlatSVP.IsShortest B' x ∧
      O hist (SuperlatSVP.encBasis B') = SuperlatSVP.encIntVec x

/-- The result of a halting oracle run: the final output word, the work (bit time of the RAM's own
steps plus one per oracle call), the workspace (largest bit space over the run), the number of
oracle calls, and the list of queries made, in order. -/
structure OracleResult where
  output : List ℚ
  time : ℕ
  space : ℕ
  calls : ℕ
  queries : List (List ℚ)

/-- Resume a halted configuration after an oracle call with reply word `r`: cell `0` receives the
length of `r`, cells `1, …, |r|` its entries, every other cell is kept, the program counter is
reset to `0`, and the coin pointer is kept (fresh coins after the call). -/
def resumeWith (c : Config) (r : List ℚ) : Config :=
  { pc := 0
    reg := fun i => if i = 0 then (r.length : ℚ) else if i ≤ r.length then r.getD (i - 1) 0
      else c.reg i
    used := c.used ∪ Finset.range (r.length + 1)
    coins := c.coins }

/-- Oracle execution with at most `k` RAM segments. Each segment is a run of `P` on the coin tape
`τ` (the coin pointer continues across segments) up to its first halt. If the halted output word
starts with `1`, its tail `q` is an oracle query: the reply `O hist q` is written by `resumeWith`
and the next segment starts; otherwise the run ends and its result is the output word without its
first entry. `none` if some segment never halts or more than `k` segments are needed. -/
noncomputable def oracleExec (P : Program) (O : List (List ℚ) → List ℚ → List ℚ)
    (τ : ℕ → Bool) : ℕ → Config → List (List ℚ) → Option OracleResult
  | 0, _, _ => none
  | k + 1, c, hist =>
    match runStats P τ c with
    | none => none
    | some s =>
      if s.final.output.head? = some 1 then
        (oracleExec P O τ k (resumeWith s.final (O hist s.final.output.tail))
            (hist ++ [s.final.output.tail])).map fun res =>
          ⟨res.output, s.time + 1 + res.time, max s.space res.space, res.calls + 1,
            s.final.output.tail :: res.queries⟩
      else
        some ⟨s.final.output.drop 1, s.time, s.space, 0, []⟩

open Classical in
/-- The oracle run of `P` with oracle rule `O` from the input word `w` on the coin tape `τ`
(Gao–Han–Hu, Theorem 12.6, p.61: "In the declared computational model, its work, counting each SVP
call as one operation, …"): the result with the least number of segments, `none` if the run does
not end.

**Formalization Note.** The published RAM `TwMSOCount.Main` has no oracle instruction; this is
its oracle extension. Work counts the bit time of the RAM's own steps plus one per oracle call;
workspace is the RAM's bit space (address and content bits of every written cell, maximized over the
run, including the reply cells). -/
noncomputable def oracleOutcome (P : Program) (O : List (List ℚ) → List ℚ → List ℚ)
    (τ : ℕ → Bool) (w : List ℚ) : Option OracleResult :=
  if h : ∃ k, (oracleExec P O τ k (Config.init w) []).isSome then
    oracleExec P O τ (Nat.find h) (Config.init w) []
  else none

end GaussDiffSVP.Supplement


