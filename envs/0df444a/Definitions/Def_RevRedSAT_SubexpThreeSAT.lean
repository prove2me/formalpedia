-- Prove2me | Definitions.Def_RevRedSAT_SubexpThreeSAT
-- name    : RevRedSAT_SubexpThreeSAT
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T04:46:38.005129+00:00
-- url     : https://prove2.me/theorems/7986f2e3-7768-4205-ae6d-2895700fce72
-- title:
--   The Subexponential 3-SAT Assumption (4.1)
-- statement:
--   **Assumption 4.1 (Subexponential 3-SAT).** There is a deterministic algorithm that decides whether a given 3-CNF formula $F$ on $N$ occurring variables is satisfiable in time $2^{o(N)}|F|^{O(1)}$.
--
--   Formally: there are a machine $M$ with finite stack alphabets, an exponent $c$ and a function $g:\mathbb N\to\mathbb N$ with $g(N)/N\to0$ such that for every formula $\varphi$ of width at most $3$, on the code of $\varphi$ the machine outputs the single bit $b$, with $b=1$ exactly when $\varphi$ is satisfiable, within
--
--   $$2^{g(N)}\cdot|F|^{c}$$
--
--   steps, where $N$ is the number of variables occurring in $\varphi$ and $|F|$ the length of its code.
--
--   The assumption is a hypothesis of the mission, not a claim: the paper reports that manuscripts by OpenAI and Anthropic give such algorithms (§4.1, p.28).
--
--   **Formalization Note** $2^{o(N)}$ is $2^{g(N)}$ for one function $g$ fixed with the machine and before the formula; no rate of convergence is required. Every code has length at least $2$, so a constant factor is absorbed by $|F|^c$.
-- source:
--   Kundu, Panolan, Saurabh, Xue, Zehavi, Reverse Reductions: From Faster SAT to Subexponential Algorithms, STOC 2027 submission (held manuscript, sha256 7bf9a5af…), §4.1, p.28, Subexponential 3-SAT Assumption (4.1)

import Mathlib
import Definitions.Def_HMBinPacking_OutputsWithin
import Definitions.Def_RevRedSAT_FiniteAlphabets
import Definitions.Def_RevRedSAT_encCNF

set_option autoImplicit false

namespace RevRedSAT

open Filter Topology

/-- **The Subexponential 3-SAT Assumption (4.1).**
Kundu, Panolan, Saurabh, Xue, Zehavi, *Reverse Reductions: From Faster SAT to Subexponential
Algorithms*, STOC 2027 submission (held manuscript, sha256 7bf9a5af…), §4.1, p.28: "For the
decision assumptions, F is a CNF formula with N occurring variables, M distinct clauses, and clause
width at most d. All algorithms below are uniform, and all polynomial input factors have fixed
exponents. Subexponential 3-SAT Assumption (4.1). There is a deterministic algorithm that decides
whether a given 3-CNF formula F on N occurring variables is satisfiable in time 2^{o(N)}|F|^{O(1)}."

There are a machine `M` with finite alphabets, an exponent `c` and a function `g` with
`g(N)/N → 0` such that on the code of every formula `φ` of width at most `3`, `M` outputs the single
bit `[b]`, `b = true` exactly when `φ` is satisfiable, within `2^{g(N)} · |F|^c` steps, where `N` is
the number of occurring variables and `|F|` the length of the code.

**Formalization Note** `2^{o(N)}` is read as `2^{g(N)}` for one function `g` with `g(N)/N → 0`,
fixed with the machine and before the formula; no rate of convergence is required. `|F| ≥ 2` for
every code, so a constant factor is absorbed by `|F|^c`. A 3-CNF formula is one of width at most `3`
after removing repeated literals (App. C.5); clauses may repeat and variables may be declared without
occurring. -/
def SubexpThreeSAT : Prop :=
  ∃ M : Turing.TM2ComputableAux Bool Bool, FiniteAlphabets M ∧
    ∃ (c : ℕ) (g : ℕ → ℕ), Tendsto (fun N => (g N : ℝ) / N) atTop (𝓝 0) ∧
      ∀ (n : ℕ) (φ : MainResults.CNF n), width φ ≤ 3 →
        ∃ b : Bool, (b = true ↔ MainResults.Satisfiable φ) ∧
          HMBinPacking.OutputsWithin M (encCNF φ) [b] (2 ^ g (occVars φ) * (encCNF φ).length ^ c)

end RevRedSAT


