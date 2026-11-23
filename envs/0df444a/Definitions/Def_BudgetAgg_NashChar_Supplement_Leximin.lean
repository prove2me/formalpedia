-- Prove2me | Definitions.Def_BudgetAgg_NashChar_Supplement_Leximin
-- name    : BudgetAgg_NashChar_Supplement_Leximin
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T06:01:36.555976+00:00
-- url     : https://prove2.me/theorems/8dea732b-2364-452d-942e-22477b617840
-- title:
--   App. G — Leximin-Leontief preferences and the leximin versions of efficiency, strategyproofness, group-strategyproofness and core fair share
-- statement:
--   Let $p\in\Delta_m$ be a peak and $M_p=\{j:p_j>0\}$. The **ratio vector** of a distribution $q$ is the list of ratios $q_j/p_j$, $j\in M_p$, sorted in ascending order. Leximin-Leontief preferences (App. G, pp. 39–40) compare ratio vectors lexicographically: $q\succ^{lex}_p q'$ if the ratio vector of $q$ is lexicographically larger than that of $q'$ (larger smallest ratio, or equal smallest and larger second smallest, and so on); $q\simeq^{lex}_p q'$ if the two vectors are equal; $q\succeq^{lex}_p q'$ if either holds.
--
--   With these relations, for a profile $P=(p_1,\dots,p_n)$ and a mechanism $f$:
--
--   1. **Efficiency**: no $q'$ with $q'\succeq^{lex}_{p_i}q$ for all $i$ and $q'\succ^{lex}_{p_i}q$ for some $i$.
--   2. **Strategyproofness**: if $P'$ differs from $P$ only in agent $i$, then $f(P)\succeq^{lex}_{p_i}f(P')$.
--   3. **Group-strategyproofness**: for every $N'\subseteq N$ and $P,P'$ agreeing outside $N'$, either $f(P)\succ^{lex}_{p_i}f(P')$ for some $i\in N'$, or $f(P)\simeq^{lex}_{p_i}f(P')$ for all $i\in N'$.
--   4. **Core fair share**: no nonempty $N'\subseteq N$ and $q'\in\Delta_m$ such that for every $q''\in\Delta_m$ and every $i\in N'$,
--   $$\tfrac{|N'|}{n}q'+\Big(1-\tfrac{|N'|}{n}\Big)q''\ \succ^{lex}_{p_i}\ q .$$
--
--   The Nash rule is still defined by the minimum ratios (the Leontief utilities), and critical alternatives are still those with the minimum ratio, as in the published base setting.
--
--   **Formalization Note** Ratios are taken only over $j$ with $p_j>0$, so no division by zero enters (Lean sets $x/0=0$). The two lists compared always have the same length $|M_p|$, and `List.Lex (· < ·)` is the lexicographic order. Core fair share excludes only nonempty blocking coalitions: the empty coalition would block every distribution vacuously, as in the base mission's Leontief definition.
--   The ratio and preference definitions accept ambient real vectors. Every theorem here evaluates them on distributions or coalition mixtures of distributions.
-- source:
--   Brandt, Greger, Segal-Halevi, Suksompong, Optimal Budget Aggregation with Star-Shaped Preference Domains, arXiv:2402.15904v3, pp. 8–9, 39–40, Definitions 1, 3, 8 and App. G

import Mathlib
import Definitions.Def_BudgetAgg_NashChar_Setting

namespace BudgetAgg.NashChar.Supplement

open Finset BudgetAgg.NashChar

/-- The ratio vector of `q` for an agent with peak `p`: the ratios `q_j / p_j` over
`M_i = {j : p_j > 0}`, sorted in ascending order (App. G, p. 39). -/
noncomputable def ratioList {m : ℕ} (p : stdSimplex ℝ (Fin m)) (q : Fin m → ℝ) :
    List ℝ :=
  ((Finset.univ.filter (fun j => 0 < p.1 j)).val.map (fun j => q j / p.1 j)).sort
    (· ≤ ·)

/-- Strict Leximin-Leontief preference `q ≻lex_p q'` (App. G, pp. 39–40): the sorted
ratio vector of `q` is lexicographically larger than that of `q'`. -/
def LexGt {m : ℕ} (p : stdSimplex ℝ (Fin m)) (q q' : Fin m → ℝ) : Prop :=
  List.Lex (· < ·) (ratioList p q') (ratioList p q)

/-- Leximin indifference `q ≃lex_p q'`: equal sorted ratio vectors. -/
def LexEq {m : ℕ} (p : stdSimplex ℝ (Fin m)) (q q' : Fin m → ℝ) : Prop :=
  ratioList p q = ratioList p q'

/-- Weak Leximin-Leontief preference `q ⪰lex_p q'`. -/
def LexGe {m : ℕ} (p : stdSimplex ℝ (Fin m)) (q q' : Fin m → ℝ) : Prop :=
  LexGt p q q' ∨ LexEq p q q'

/-- Pareto efficiency for Leximin-Leontief preferences (Definition 1 with `⪰lex`,
`≻lex`; used in Lemma 14, p. 40). -/
def IsLexEfficient {n m : ℕ} (P : Profile n m) (q : stdSimplex ℝ (Fin m)) : Prop :=
  ¬ ∃ q' : stdSimplex ℝ (Fin m),
    (∀ i, LexGe (P i) q'.1 q.1) ∧ (∃ i, LexGt (P i) q'.1 q.1)

/-- Strategyproofness for Leximin-Leontief preferences (Definition 8 with
`|N'| = 1`, App. G p. 40): a unilateral misreport never yields a strictly
leximin-better outcome for the true peak, i.e. `f(P) ⪰lex_{p_i} f(P')`. -/
def IsLexStrategyproof {n m : ℕ} (f : Mechanism n m) : Prop :=
  ∀ (i : Fin n) (P P' : Profile n m), (∀ j, j ≠ i → P' j = P j) →
    LexGe (P i) (f P).1 (f P').1

/-- Group-strategyproofness for Leximin-Leontief preferences (Definition 8, p. 9,
with `≻lex`, `≃lex`): for every coalition `S` and profiles agreeing off `S`, either
some member strictly leximin-prefers `f P`, or all members are leximin-indifferent. -/
def IsLexGroupSP {n m : ℕ} (f : Mechanism n m) : Prop :=
  ∀ (S : Finset (Fin n)) (P P' : Profile n m), (∀ j, j ∉ S → P' j = P j) →
    (∃ i ∈ S, LexGt (P i) (f P).1 (f P').1) ∨
    (∀ i ∈ S, LexEq (P i) (f P).1 (f P').1)

/-- Core fair share for Leximin-Leontief preferences (Definition 3, p. 8, with
`≻lex`), with nonempty blocking coalitions: no nonempty `S` and `q'` such that
`(|S|/n) q' + (1 - |S|/n) q''` is strictly leximin-better than `q` for every member
of `S`, whatever `q''` is. -/
def IsLexCoreFairShare {n m : ℕ} (P : Profile n m) (q : stdSimplex ℝ (Fin m)) : Prop :=
  ∀ S : Finset (Fin n), S.Nonempty →
    ¬ ∃ q' : stdSimplex ℝ (Fin m),
      ∀ q'' : stdSimplex ℝ (Fin m), ∀ i ∈ S,
        LexGt (P i) (fun j =>
            ((S.card : ℝ) / (n : ℝ)) * q'.1 j +
            (1 - (S.card : ℝ) / (n : ℝ)) * q''.1 j) q.1

end BudgetAgg.NashChar.Supplement


