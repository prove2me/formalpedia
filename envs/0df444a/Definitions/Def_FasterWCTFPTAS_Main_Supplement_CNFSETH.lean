-- Prove2me | Definitions.Def_FasterWCTFPTAS_Main_Supplement_CNFSETH
-- name    : FasterWCTFPTAS_Main_Supplement_CNFSETH
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T04:07:09.450215+00:00
-- url     : https://prove2.me/theorems/64ef6862-f6e1-4710-b272-e1856d17d734
-- title:
--   CNF-SETH on the published deterministic real RAM
-- statement:
--   Write $\mathrm{FastCNFSAT}(c,\delta)$ for existence of one finite admissible program $P$ and one constant $C>0$ which decide every encoded CNF formula with $N$ variables and $M$ clauses, outputting $[1]$ for satisfiable and $[0]$ otherwise, within $C\max(1,M)^c(2-\delta)^N$ actual steps. Define the proposition
--
--   $$\mathrm{CNFSETH}\ :\Longleftrightarrow\ \forall c>0\ \forall\delta\in(0,1):\ \neg\mathrm{FastCNFSAT}(c,\delta).$$
--
--   This is an antecedent, never an asserted axiom. The assumption and all algorithms excluded by the supplement use the published deterministic real RAM, with rational constants and bounded floor. The paper does not specify a machine; this is the recorded common-machine reading. Improvements below one suffice to exclude every positive exponential improvement, and $\max(1,M)$ defines only the empty-formula boundary. Program and constant precede the formula quantifier.
-- source:
--   Karl Bringmann, Anita Dürr, Karol Węgrzycki, A Faster FPTAS for Weighted Completion Time Scheduling, STOC 2027 submission #1072 (October 2026), pp.6,19 (PDF pp.7,20), CNF-SETH.

import Definitions.Def_FasterWCTFPTAS_Main_Machine
import Definitions.Def_FasterWCTFPTAS_Main_Supplement_CNF

set_option autoImplicit false

namespace FasterWCTFPTAS.Main.Supplement

/-- Standard one-cell Boolean decision output on the published real RAM. -/
def CorrectDecision (P : Machine.Program) (xs : List ℝ) (answer : Prop) : Prop :=
  (answer → Machine.output P xs = some [1]) ∧
  (¬ answer → Machine.output P xs = some [0])

/-- One uniform admissible program decides all CNFs in the displayed time. Neither program
nor multiplicative constant can depend on the formula. -/
def FastCNFSAT (c δ : ℝ) : Prop :=
  ∃ (P : Machine.Program) (C : ℝ), Machine.Admissible P ∧ 0 < C ∧
    ∀ F : CNF,
      CorrectDecision P F.encode F.Satisfiable ∧
      Machine.HaltsWithin P F.encode
        (C * ((max 1 F.clauses.length : ℕ) : ℝ) ^ c * (2 - δ) ^ F.numVars)

/-- CNF-SETH (printed pp. 6 and 19, PDF 7 and 20), interpreted on the same published
machine as every algorithm in the conclusions. This is a proposition, not an axiom.
Improvements `0 < δ < 1` suffice to exclude every positive exponential improvement.
`max 1 M` only defines the empty-formula boundary. -/
def CNFSETH : Prop :=
  ∀ c δ : ℝ, 0 < c → 0 < δ → δ < 1 → ¬ FastCNFSAT c δ

end FasterWCTFPTAS.Main.Supplement


