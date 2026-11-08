-- Prove2me | Definitions.Def_QWildMatch_Match
-- name    : QWildMatch_Match
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T10:17:04.728199+00:00
-- url     : https://prove2.me/theorems/156f8aae-796e-44a5-9c4e-e90e8d01d3dd
-- title:
--   Substrings, the decision $\mathrm{Match}(P,T,k)$, the fixed-start predicate, and output correctness
-- statement:
--   For a text $T\in\Sigma^n$, the substring $T[s:e]$ consists of the positions $s\le j<e$, indexed from $0$. The substring decision problem is
--
--   $$\mathrm{Match}(P,T,k)=\bigvee_{0\le s\le e\le n}\mathbf 1\{\mathrm{ED}_\mu(P,T[s:e])\le k\}.$$
--
--   The fixed-start predicate at $s$ asks for the same inequality for some endpoint $e$ with $s\le e\le n$. An output is correct when it is "none" and $\mathrm{Match}(P,T,k)$ is false, or when it is a triple $(s,e,o)$ with $s\le e\le n$ and $o$ an edit script (a grid path from $(0,s)$ to $(m,e)$) of cost at most $k$, so that $\mathrm{ED}_\mu(P,T[s:e])\le k$; this is the witness of the paper's output semantics, "(s, e) and, when requested, a valid edit script".
--
--   **Formalization Note** The output type is `Option (ℕ × ℕ × List Op)`; the edit script is always output, which covers every request. The empty substring at $s=e=n$ is included, so there are $n+1$ possible starts.
-- source:
--   Zhao, Chen, Li, Kong, Peng, Yu, Yue, Quantum Approximate Pattern Matching with Wildcards and Weighted Edits, STOC 2027 submission (file sha256 9e87a9dd…), §3, p.4

import Mathlib
import Definitions.Def_QWildMatch_pathCost

namespace QWildMatch

/-- The substring `T[s : e]`, positions `s ≤ j < e`, 0-based (Zhao et al., STOC 2027 submission, §3,
p.4). -/
def sub {Sym : Type} {n : ℕ} (T : Fin n → Sym) (s e : ℕ) : List Sym :=
  ((List.ofFn T).drop s).take (e - s)

/-- `Match(P, T, k) = ⋁_{0 ≤ s ≤ e ≤ n} 1{ED_μ(P, T[s : e]) ≤ k}` (Zhao et al., STOC 2027 submission,
§3, p.4). -/
def Match {Sym : Type} {n : ℕ} (cm : CostModel Sym) (P : List (Option Sym)) (T : Fin n → Sym)
    (k : ℝ) : Prop :=
  ∃ s e : ℕ, s ≤ e ∧ e ≤ n ∧ EDle cm P (sub T s e) k

/-- The fixed-start threshold predicate of Theorem 4.1: some substring starting at `s` is within
cost `k` of `P` (Zhao et al., STOC 2027 submission, §4, p.5). -/
def FixedStart {Sym : Type} {n : ℕ} (cm : CostModel Sym) (P : List (Option Sym)) (T : Fin n → Sym)
    (k : ℝ) (s : ℕ) : Prop :=
  ∃ e : ℕ, s ≤ e ∧ e ≤ n ∧ EDle cm P (sub T s e) k

/-- Correctness of an output of the substring search (Zhao et al., STOC 2027 submission, §3, p.4:
"an output witness consists of `(s, e)` and, when requested, a valid edit script"; Theorem 6.5, p.10):
`none` claims `¬ Match`, and `some (s, e, o)` is a witness, `s ≤ e ≤ n`, with an edit script `o`, a grid
path from `(0, s)` to `(m, e)` of cost at most `k` (so `ED_μ(P, T[s : e]) ≤ k`).

**Formalization Note** The edit script is always part of the output, which covers every request. -/
def Correct {Sym : Type} {n : ℕ} (cm : CostModel Sym) (P : List (Option Sym)) (T : Fin n → Sym)
    (k : ℝ) : Option (ℕ × ℕ × List Op) → Prop
  | none => ¬ Match cm P T k
  | some (s, e, o) => s ≤ e ∧ e ≤ n ∧ pathCost cm P (sub T s e) o ≤ ((k : ℝ) : WithTop ℝ)

open Classical in
noncomputable instance {Sym : Type} {n : ℕ} (cm : CostModel Sym) (P : List (Option Sym))
    (T : Fin n → Sym) (k : ℝ) (o : Option (ℕ × ℕ × List Op)) : Decidable (Correct cm P T k o) :=
  Classical.propDecidable _

end QWildMatch


