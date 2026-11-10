-- Prove2me | Definitions.Def_RevRedSAT_QuantDSAT
-- name    : RevRedSAT_QuantDSAT
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T04:46:53.474908+00:00
-- url     : https://prove2.me/theorems/4459c94c-9cd3-4dca-a46b-d6aecf7eae36
-- title:
--   The Quantitative d-SAT Assumption (4.2) and its width-restricted forms
-- statement:
--   **Assumption 4.2 (Quantitative $d$-SAT).** There is a single deterministic algorithm that, for every clause width $d$, decides whether a given CNF formula $F$ of width at most $d$ is satisfiable in time
--
--   $$2^{O(\min\{d^2N\eta(N)/\sqrt{\lambda(N)},\ dM/\sqrt{\lambda(M)}\})}\,|F|^{O(1)},$$
--
--   where $N$ is the number of occurring variables and $M$ the number of distinct clauses. "The constant in the exponential bound and the exponent of the polynomial input factor are absolute and independent of $d$" (§4.1, p.28).
--
--   Formally: one machine $M$ with finite stack alphabets, one constant $C$ and one exponent $c$ such that for every $d$ and every formula $\varphi$ of width at most $d$, the machine outputs the satisfiability bit of $\varphi$ within $\lfloor 2^{C\min\{d^2N\eta(N)/\sqrt{\lambda(N)},\,dM/\sqrt{\lambda(M)}\}}\,|F|^{c}\rfloor$ steps.
--
--   Two weaker forms are used to state the clauses "It uses SAT formulas of width at most $\max\{3,2d\}$" of Theorems 6.12 and 6.13:
--
--   1. $\mathrm{QuantSATUpTo}(w,c)$: the same bound with polynomial exponent $c$, for formulas of width at most $d\le w$ only;
--   2. $\mathrm{VarSATUpTo}(w,c)$: for formulas of width at most $d\le w$, the variable-based bound $\lfloor 2^{C d^2N\eta(N)/\sqrt{\lambda(N)}}|F|^{c}\rfloor$ only.
--
--   Assumption 4.2, with its exponent $c$, implies both forms for every $w$.
--
--   **Formalization Note** $\lambda,\eta\ge1$, so the exponent is defined for every formula.
-- source:
--   Kundu, Panolan, Saurabh, Xue, Zehavi, Reverse Reductions: From Faster SAT to Subexponential Algorithms, STOC 2027 submission (held manuscript, sha256 7bf9a5af…), §4.1, p.28, Quantitative d-SAT Assumption (4.2); Theorem 6.12, p.44 and Theorem 6.13, p.45 (width clause)

import Mathlib
import Definitions.Def_HMBinPacking_OutputsWithin
import Definitions.Def_RevRedSAT_FiniteAlphabets
import Definitions.Def_RevRedSAT_lam
import Definitions.Def_RevRedSAT_encCNF

set_option autoImplicit false

namespace RevRedSAT

/-- The exponent `min{d² N η(N)/√λ(N), d M/√λ(M)}` of Assumption 4.2 (§4.1, p.28). -/
noncomputable def quantExp (d N Mc : ℕ) : ℝ :=
  min ((d : ℝ) ^ 2 * N * eta N / Real.sqrt (lam N)) ((d : ℝ) * Mc / Real.sqrt (lam Mc))

/-- The variable-based exponent `d² N η(N)/√λ(N)` of Assumption 4.2 (§4.1, p.28). -/
noncomputable def varExp (d N : ℕ) : ℝ := (d : ℝ) ^ 2 * N * eta N / Real.sqrt (lam N)

/-- **The Quantitative d-SAT Assumption (4.2).**
Kundu, Panolan, Saurabh, Xue, Zehavi, *Reverse Reductions: From Faster SAT to Subexponential
Algorithms*, STOC 2027 submission (held manuscript, sha256 7bf9a5af…), §4.1, p.28: "There is a single
deterministic algorithm that, for every clause width d, decides whether a given CNF formula F of
width at most d is satisfiable in time 2^{O(min{d²Nη(N)/√λ(N), dM/√λ(M)})}|F|^{O(1)}, where
λ(t) = log2(t + 2), η(t) = log2(log2(t + 4)). The constant in the exponential bound and the exponent
of the polynomial input factor are absolute and independent of d."

One machine `M` with finite alphabets, one constant `C` and one exponent `c` serve every width `d`:
on the code of every formula `φ` of width at most `d`, with `N` occurring variables and `M`
distinct clauses, `M` outputs `[b]`, `b = true` exactly when `φ` is satisfiable, within
`⌊2^{C·min{d²Nη(N)/√λ(N), dM/√λ(M)}} · |F|^c⌋` steps.

**Formalization Note** `N` counts occurring variables and `M` distinct clauses as literal sets (§4.1);
width counts distinct literals (App. C.5). `λ, η ≥ 1` on `ℕ`, so the exponent is defined
everywhere; `|F| ≥ 2` absorbs a constant factor. -/
def QuantDSAT : Prop :=
  ∃ M : Turing.TM2ComputableAux Bool Bool, FiniteAlphabets M ∧
    ∃ (C : ℝ) (c : ℕ), ∀ (d n : ℕ) (φ : MainResults.CNF n), width φ ≤ d →
      ∃ b : Bool, (b = true ↔ MainResults.Satisfiable φ) ∧
        HMBinPacking.OutputsWithin M (encCNF φ) [b]
          (expBound (C * quantExp d (occVars φ) (distinctClauses φ)) (encCNF φ).length c)

/-- **Assumption 4.2 restricted to widths at most `w`, with polynomial exponent `c`.** Used for the
clause "It uses SAT formulas of width at most max{3, 2d}" of Theorem 6.12 (p.44): one machine with
finite alphabets and one constant `C` decide every formula of width at most `d ≤ w` within
`⌊2^{C·min{d²Nη(N)/√λ(N), dM/√λ(M)}} · |F|^c⌋` steps. `QuantDSAT` gives it for every `w`, with its
own exponent `c`. -/
def QuantSATUpTo (w c : ℕ) : Prop :=
  ∃ M : Turing.TM2ComputableAux Bool Bool, FiniteAlphabets M ∧
    ∃ C : ℝ, ∀ d ≤ w, ∀ (n : ℕ) (φ : MainResults.CNF n), width φ ≤ d →
      ∃ b : Bool, (b = true ↔ MainResults.Satisfiable φ) ∧
        HMBinPacking.OutputsWithin M (encCNF φ) [b]
          (expBound (C * quantExp d (occVars φ) (distinctClauses φ)) (encCNF φ).length c)

/-- **The variable-based bound of Assumption 4.2 for widths at most `w`, with polynomial exponent
`c`.** Used for the clause "The algorithm uses only the variable-based SAT bound for CNF formulas of
width at most max{3, 2d}" of Theorem 6.13 (p.45): one machine with finite alphabets and one constant
`C` decide every formula of width at most `d ≤ w` within `⌊2^{C·d²Nη(N)/√λ(N)} · |F|^c⌋` steps.
`QuantDSAT` gives it for every `w`, with its own exponent `c`. -/
def VarSATUpTo (w c : ℕ) : Prop :=
  ∃ M : Turing.TM2ComputableAux Bool Bool, FiniteAlphabets M ∧
    ∃ C : ℝ, ∀ d ≤ w, ∀ (n : ℕ) (φ : MainResults.CNF n), width φ ≤ d →
      ∃ b : Bool, (b = true ↔ MainResults.Satisfiable φ) ∧
        HMBinPacking.OutputsWithin M (encCNF φ) [b]
          (expBound (C * varExp d (occVars φ)) (encCNF φ).length c)

end RevRedSAT


