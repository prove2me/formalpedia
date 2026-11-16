-- Prove2me | Definitions.Def_SteinerAPX_Supplement_WeakETH
-- name    : SteinerAPX_Supplement_WeakETH
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T00:11:06.166688+00:00
-- url     : https://prove2.me/theorems/3e0b50e8-5764-47d3-b457-1ec51fb0f15b
-- title:
--   Hypothesis 1 (Weak ETH): 3SAT has no $2^{n^\gamma}$-time algorithm for any $\gamma<1$
-- statement:
--   **Weak ETH** (Hypothesis 1 of the paper) asserts that 3SAT has no truly subexponential-time algorithm: there are no real $\gamma < 1$, Turing machine $M$ with finite alphabets and constant $c$ such that, for every CNF formula $F$ whose clauses have at most three distinct literals, $M$ decides whether $F$ is satisfiable within
--   $$\left\lceil c \cdot 2^{|F|^{\gamma}} \right\rceil$$
--   steps, where $|F|$ is the length of the binary code of $F$.
--
--   It is the hypothesis of Theorem 3. It is weaker than ETH and Gap-ETH, and is not refuted by the announced SAT algorithms the paper mentions.
--
--   **Formalization Note** "Formulas of size $n$" is read as the length of the published code `RevRedSAT.encCNF` (number of variables, then the clauses with self-delimiting variable indices and sign bits); a 3SAT formula is one of width at most $3$ (`RevRedSAT.width`). Any other reasonable code differs by a polylogarithmic factor, which the open range $\gamma<1$ absorbs. The constant $c$ changes nothing because $\gamma$ ranges over an open set.
-- source:
--   Bartlmae, Inapproximability of Euclidean Steiner Tree, STOC 2027 submission (manuscript sha256 6f78a9ea…3fcfa9), Hypothesis 1, p.2 (PDF p.4)

import Mathlib
import Definitions.Def_MainResults
import Definitions.Def_HMBinPacking_OutputsWithin
import Definitions.Def_RevRedSAT_FiniteAlphabets
import Definitions.Def_RevRedSAT_encCNF

set_option autoImplicit false

namespace SteinerAPX.Supplement

/-- **Hypothesis 1 (Weak ETH).** S. Bartlmae, *Inapproximability of Euclidean Steiner Tree*,
STOC 2027 submission (manuscript sha256 6f78a9ea…), Hypothesis 1, p.2 (PDF p.4): "3SAT has no
truly subexponential-time algorithm, that is, no algorithm running in time 2^{n^γ} on formulas of
size n for any constant γ < 1."

There are no real `γ < 1`, machine `M` with finite stack alphabets and constant `c` such that, on
the code of every CNF formula `φ` whose clauses have at most three distinct literals, `M` outputs
the single bit `[b]`, with `b = true` exactly when `φ` is satisfiable, within `⌈c · 2^{|F|^γ}⌉`
steps, where `|F|` is the length of the code of `φ`.

**Formalization Note** "Size n" is the length of the published binary code `RevRedSAT.encCNF`
(the number of variables, then the clauses, each literal as a self-delimiting variable index and a
sign bit); every reasonable code of a formula is within a polylogarithmic factor of it, which the
open range `γ < 1` absorbs. A 3SAT formula is a CNF formula of width at most `3`
(`RevRedSAT.width`, distinct literals per clause). The constant `c` is the usual meaning of
"running in time"; since `γ` ranges over all reals below `1`, the readings with and without it are
equivalent. Machines are as in `InSUBEXP`. This is not ETH (no number-of-variables measure, no
sparsification) and not Gap-ETH. -/
def WeakETH : Prop :=
  ¬ ∃ γ : ℝ, γ < 1 ∧
    ∃ M : Turing.TM2ComputableAux Bool Bool, RevRedSAT.FiniteAlphabets M ∧
      ∃ c : ℕ, ∀ (n : ℕ) (φ : MainResults.CNF n), RevRedSAT.width φ ≤ 3 →
        ∃ b : Bool, (b = true ↔ MainResults.Satisfiable φ) ∧
          HMBinPacking.OutputsWithin M (RevRedSAT.encCNF φ) [b]
            ⌈(c : ℝ) * (2 : ℝ) ^ (((RevRedSAT.encCNF φ).length : ℝ) ^ γ)⌉₊

end SteinerAPX.Supplement


