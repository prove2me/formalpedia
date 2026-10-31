-- Prove2me | Definitions.Def_CardinalMatching_EFPO
-- name    : CardinalMatching_EFPO
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:28:20.735597+00:00
-- url     : https://prove2.me/theorems/6adbc27c-3434-4bc7-9230-6db8344e44d4
-- title:
--   The search problem EF+PO
-- statement:
--   **EF+PO** is the computational problem of Theorem 8: "finding an EF+PO allocation in a one-sided matching market with linear utilities".
--
--   1. An instance is the binary encoding of a number $n\ge 1$ of agents and goods and an $n\times n$ matrix $u$ of non-negative rational utilities.
--   2. An answer on that instance is the encoding of a rational $n\times n$ matrix $x$ that lies in $P_{\mathrm{PM}}$, is envy-free (Definition 4) and is Pareto-optimal over all of $P_{\mathrm{PM}}$ (Definition 5).
--
--   Every instance has an answer: by Theorem 7 of the paper a rational EF+PO allocation always exists.
--
--   **Formalization Note** Agents and goods are $\{0,\dots,n-1\}$. Answers are rational, as in the proof of Theorem 8 ("a rational EF+PO allocation … encoded with a polynomial number of bits", p.8).
-- source:
--   Tröbst, Vazirani, Cardinal-Utility Matching Markets, arXiv:2402.08851v6, Theorem 8, p.6; Definitions 4–5, p.5; P_PM, p.6; p.2 (rational utilities)

import Mathlib
import Definitions.Def_TetrisHard_Rows_Search
import Definitions.Def_CardinalMatching_IsFracPerfectMatching
import Definitions.Def_CardinalMatching_IsEnvyFree
import Definitions.Def_CardinalMatching_IsParetoOptimal
import Definitions.Def_CardinalMatching_encRatMatrix

namespace CardinalMatching

/-- **EF+PO**, the search problem of Theorem 8 (Tröbst–Vazirani, *Cardinal-Utility Matching
Markets*, arXiv:2402.08851v6, p.6): "the problem of finding an EF+PO allocation in a one-sided
matching market with linear utilities".
* An instance is the binary code `encRatMatrix n u` of a number of agents `n ≥ 1`
  (`|A| = |G| = n`, p.5) and an `n × n` matrix `u` of **non-negative rational** utilities (p.2:
  "each agent i has a vector (uij)j∈G of rational, non-negative utilities").
* An answer on that instance is the code `encRatMatrix n x` of a rational `n × n` matrix `x`
  which, as a real matrix, is a fractional perfect matching (`P_PM`, p.6) that is envy-free
  (Definition 4) and Pareto-optimal over all of `P_PM` (Definition 5).

**Formalization Note** Agents and goods are `Fin n`. Rational answers suffice: Theorem 7 (p.6)
shows a rational EF+PO allocation always exists, and the proof of Theorem 8 starts from "a
rational EF+PO allocation … encoded with a polynomial number of bits" (p.8). The codes are
self-delimiting, so a string encodes at most one instance or answer. -/
def EFPO : TetrisHard.Rows.SearchProblem where
  valid s := ∃ (n : ℕ) (u : Fin n → Fin n → ℚ), 1 ≤ n ∧ (∀ i j, 0 ≤ u i j) ∧ s = encRatMatrix n u
  answer s t := ∃ (n : ℕ) (u x : Fin n → Fin n → ℚ),
    s = encRatMatrix n u ∧ t = encRatMatrix n x ∧
    IsFracPerfectMatching (fun i j => (x i j : ℝ)) ∧
    IsEnvyFree (fun i j => (u i j : ℝ)) (fun i j => (x i j : ℝ)) ∧
    IsParetoOptimal (fun i j => (u i j : ℝ)) (fun i j => (x i j : ℝ))

end CardinalMatching


