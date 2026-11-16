-- Prove2me | Definitions.Def_CritContracts_Supplement_IsGrossSubstitutes
-- name    : CritContracts_Supplement_IsGrossSubstitutes
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T05:54:55.414839+00:00
-- url     : https://prove2.me/theorems/d6efe8e9-30f1-4f18-a8a3-1b6ddb0acedb
-- title:
--   Demands, gross-substitutes and subadditive set functions
-- statement:
--   Let $f:2^T\to\mathbb R$ be a set function on a finite set $T$ of actions.
--
--   1. A set $S\subseteq T$ is a **demand** at the prices $p\in\mathbb R^T$ if $S\in\operatorname*{arg\,max}_{X\subseteq T}\{f(X)-\sum_{i\in X}p_i\}$.
--   2. $f$ is **gross substitutes** if for any two price vectors $p\le q$ and any demand $S$ at $p$ there is a demand $U$ at $q$ with $U\supseteq\{i\in S:q_i=p_i\}$: when prices weakly increase, the demand for items whose prices are unchanged weakly increases.
--   3. $f$ is **subadditive** if $f(S\cup S')\le f(S)+f(S')$ for all $S,S'\subseteq T$.
--
--   These are the reward classes of Theorems 4.11 and 4.12 (§2 of the paper).
--
--   **Formalization Note** The paper prints the price vectors as elements of $\mathbb R^n$; they are indexed by the actions. Gross substitutes is the paper's price-vector definition, not an exchange-axiom variant.
-- source:
--   Ezra–Feldman–Molina–Schlesinger, Sources of Complexity in Multi-Agent Combinatorial Contracts, STOC 2027 submission (manuscript sha256 430be35c86352b23f05ee0e9126d1318096922c9cbe07d419ee38e38bfcba346), §2, p.10 (PDF p.11) (gross substitutes, subadditive, demand queries)

import Mathlib

set_option autoImplicit false

namespace CritContracts.Supplement

/-- `S` is a **demand** of `f` at the prices `p`: `S ∈ argmax_{X ⊆ T} { f(X) − Σ_{i ∈ X} p_i }`
(Ezra–Feldman–Molina–Schlesinger, *Sources of Complexity in Multi-Agent Combinatorial Contracts*, STOC 2027
submission (manuscript sha256 430be35c…), §2, p.10, PDF p.11). -/
def IsDemand {T : Type} [Fintype T] (f : Finset T → ℝ) (p : T → ℝ) (S : Finset T) : Prop :=
  ∀ X : Finset T, f X - ∑ i ∈ X, p i ≤ f S - ∑ i ∈ S, p i

/-- `f` is **gross substitutes** (§2, p.10): for any two price vectors `p ≤ q` and any demand `S` at `p`, some
demand `U` at `q` contains `{i ∈ S | q_i = p_i}`.

**Formalization Note** The paper prints the price vectors as elements of `ℝ^n`; they are indexed by the actions,
so they are `T → ℝ`. This is the paper's price-vector definition, not an exchange-axiom variant. -/
def IsGrossSubstitutes {T : Type} [Fintype T] [DecidableEq T] (f : Finset T → ℝ) : Prop :=
  ∀ (p q : T → ℝ) (S : Finset T), p ≤ q → IsDemand f p S →
    ∃ U : Finset T, IsDemand f q U ∧ S.filter (fun i => q i = p i) ⊆ U

/-- `f` is **subadditive** (§2, p.10): `f(S ∪ S') ≤ f(S) + f(S')` for any two sets `S, S' ⊆ T`. -/
def IsSubadditive {T : Type} [DecidableEq T] (f : Finset T → ℝ) : Prop :=
  ∀ S S' : Finset T, f (S ∪ S') ≤ f S + f S'

end CritContracts.Supplement


