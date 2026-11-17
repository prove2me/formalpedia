-- Prove2me | Definitions.Def_QWildMatch_Supplement_CorrectMin
-- name    : QWildMatch_Supplement_CorrectMin
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T10:18:23.187871+00:00
-- url     : https://prove2.me/theorems/74783945-bed7-4694-bae8-b42efc219bc6
-- title:
--   Correct output with a minimum-cost edit script
-- statement:
--   Let $T\in\Sigma^n$ be a text, $P\in(\Sigma\cup\{\star\})^m$ a pattern, $\mu,c_{\mathrm{del}},c_{\mathrm{ins}}$ a cost table and $k$ a threshold. An output of the substring search is either "no match" or a triple $(s,e,o)$ of a start, an end and an edit script (a grid path from $(0,s)$ to $(m,e)$). The output is **correct with a minimum-cost script** when:
--
--   1. "no match" is output only if no substring $T[s:e]$, $0\le s\le e\le n$, has weighted edit cost $\mathrm{ED}_\mu(P,T[s:e])\le k$;
--   2. a triple $(s,e,o)$ satisfies $s\le e\le n$, the path $o$ has cost at most $k$, and $o$ has the least cost among all grid paths for $T[s:e]$, i.e. its cost is $\mathrm{ED}_\mu(P,T[s:e])$.
--
--   This is the output guarantee of Corollary 4.2 ("an endpoint and minimum-cost edit script can be recovered"), the formal version of Theorem 1.1.
--
--   **Formalization Note** It refines the published `QWildMatch.Correct` by the minimality clause. Edge lists that are not grid paths have cost $\top$ in `pathCost`, so minimizing over all edge lists is minimizing over grid paths.
-- source:
--   Zhao, Chen, Li, Kong, Peng, Yu, Yue, Quantum Approximate Pattern Matching with Wildcards and Weighted Edits, STOC 2027 submission (file sha256 9e87a9dd…1f96), Corollary 4.2, p.5 (formal version of Theorem 1.1, p.2); output witness §3, p.4

import Mathlib
import Definitions.Def_QWildMatch_Match

namespace QWildMatch.Supplement

open QWildMatch

/-- Correctness of an output with a **minimum-cost** edit script, the output of Corollary 4.2, the formal
version of Theorem 1.1 (Zhao, Chen, Li, Kong, Peng, Yu, Yue, *Quantum Approximate Pattern Matching with
Wildcards and Weighted Edits*, STOC 2027 submission (file sha256 9e87a9dd…), p.5: "an endpoint and
minimum-cost edit script can be recovered"). `none` claims `¬ Match`; `some (s, e, o)` must satisfy the
published `Correct` (so `s ≤ e ≤ n` and `o` is a grid path of cost at most `k` for `T[s : e]`), and `o`
must have the least cost among all edge lists for `T[s : e]`.

**Formalization Note** `pathCost` is `⊤` for an edge list that is not a path from `(0, s)` to `(m, e)`, so
minimizing over every `o' : List Op` is minimizing over the grid paths. -/
def CorrectMin {Sym : Type} {n : ℕ} (cm : CostModel Sym) (P : List (Option Sym)) (T : Fin n → Sym)
    (k : ℝ) : Option (ℕ × ℕ × List Op) → Prop
  | none => ¬ Match cm P T k
  | some (s, e, o) => Correct cm P T k (some (s, e, o)) ∧
      ∀ o' : List Op, pathCost cm P (sub T s e) o ≤ pathCost cm P (sub T s e) o'

open Classical in
noncomputable instance {Sym : Type} {n : ℕ} (cm : CostModel Sym) (P : List (Option Sym))
    (T : Fin n → Sym) (k : ℝ) (o : Option (ℕ × ℕ × List Op)) : Decidable (CorrectMin cm P T k o) :=
  Classical.propDecidable _

end QWildMatch.Supplement


