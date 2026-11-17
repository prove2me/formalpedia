-- Prove2me | Definitions.Def_RevRedSAT_Supplement_ClauseBasedDSAT
-- name    : RevRedSAT_Supplement_ClauseBasedDSAT
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T10:53:03.26823+00:00
-- url     : https://prove2.me/theorems/6c25b8a7-d7ee-4410-b0e5-4cf157871fd1
-- title:
--   The Clause-Based $d$-SAT Assumption (Assumption 4.3)
-- statement:
--   This is Assumption 4.3 of the paper. A CNF formula $F$ has *width at most $d$* if every clause has at most $d$ distinct literals; $M$ is the number of distinct clauses of $F$, compared as sets of literals, and $\lambda(t)=\log_2(t+2)$.
--
--   **Assumption 4.3.** There are one deterministic algorithm, one constant $C$ and one exponent $c$ such that, for every clause width $d$ and every CNF formula $F$ of width at most $d$, the algorithm decides whether $F$ is satisfiable within
--
--   $$\Bigl\lfloor 2^{C\,dM/\sqrt{\lambda(M)}}\;|F|^{c}\Bigr\rfloor$$
--
--   steps, where $|F|$ is the length of the binary code of $F$. The constant and the exponent do not depend on $d$.
--
--   The assumption is the clause-based half of the Quantitative $d$-SAT Assumption 4.2, stated separately because Theorems 6.5 and 10.1 need only it.
--
--   **Formalization Note** Algorithms are Turing machines with finite stack alphabets (`RevRedSAT.FiniteAlphabets`); formulas are coded by `RevRedSAT.encCNF`, and widths and distinct clauses are counted as in the published `RevRedSAT.QuantDSAT`.
-- source:
--   Kundu, Panolan, Saurabh, Xue, Zehavi, Reverse Reductions: From Faster SAT to Subexponential Algorithms, STOC 2027 submission (held manuscript, sha256 7bf9a5af…), §4.1, p.28 (Assumption 4.3)

import Mathlib
import Definitions.Def_HMBinPacking_OutputsWithin
import Definitions.Def_RevRedSAT_FiniteAlphabets
import Definitions.Def_RevRedSAT_lam
import Definitions.Def_RevRedSAT_encCNF

set_option autoImplicit false

namespace RevRedSAT.Supplement

/-- **The Clause-Based d-SAT Assumption (4.3).**
Kundu, Panolan, Saurabh, Xue, Zehavi, *Reverse Reductions: From Faster SAT to Subexponential
Algorithms*, STOC 2027 submission (held manuscript, sha256 7bf9a5af…), §4.1, p.28: "There is a single deterministic algorithm that, for every clause width d, decides
whether a given CNF formula F of width at most d is satisfiable in time 2^{O(dM/√λ(M))}|F|^{O(1)},
where λ(t) = log2(t + 2). The constant in the exponential bound and the exponent of the polynomial
input factor are absolute and independent of d."

One machine `M` with finite alphabets, one constant `C` and one exponent `c` serve every width
`d`: on the code of every formula `φ` of width at most `d` with `M` distinct clauses, `M` outputs
`[b]`, `b = true` exactly when `φ` is satisfiable, within `⌊2^{C·dM/√λ(M)} · |F|^c⌋` steps.

**Formalization Note** `M` counts distinct clauses compared as sets of literals (§4.1, "M distinct
clauses"), and the width counts distinct literals (App. C.5), exactly as in the published
`RevRedSAT.QuantDSAT`. `λ ≥ 1` on `ℕ`, so the exponent is defined everywhere. -/
def ClauseBasedDSAT : Prop :=
  ∃ M : Turing.TM2ComputableAux Bool Bool, FiniteAlphabets M ∧
    ∃ (C : ℝ) (c : ℕ), ∀ (d n : ℕ) (φ : MainResults.CNF n), width φ ≤ d →
      ∃ b : Bool, (b = true ↔ MainResults.Satisfiable φ) ∧
        HMBinPacking.OutputsWithin M (encCNF φ) [b]
          (expBound (C * d * distinctClauses φ / Real.sqrt (lam (distinctClauses φ)))
            (encCNF φ).length c)

end RevRedSAT.Supplement


