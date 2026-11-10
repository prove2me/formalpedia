-- Prove2me | Definitions.Def_CritContracts_IsSupermodular
-- name    : CritContracts_IsSupermodular
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T21:43:33.323192+00:00
-- url     : https://prove2.me/theorems/f5cd8c94-af20-45e5-baf7-0cd19cae02ea
-- title:
--   Supermodular, normalized, monotone and $[0,1]$-valued set functions
-- statement:
--   For a set function $f:2^T\to\mathbb R$ and $j\in T$ write $f(j\mid S)=f(S\cup\{j\})-f(S)$ for the marginal gain of adding $j$ to $S$. The module defines four properties of $f$:
--
--   1. $f$ is **supermodular** if marginals are (weakly) increasing: $f(j\mid S)\le f(j\mid S')$ for any two sets $S\subseteq S'\subseteq T$ and $j\in T\setminus S'$;
--   2. $f$ is **normalized** if $f(\emptyset)=0$;
--   3. $f$ is **monotone** if $S\subseteq S'$ implies $f(S)\le f(S')$;
--   4. $f$ takes values in $[0,1]$.
--
--   These are the reward classes of the paper's supermodular results: the hardness of Theorem 3.5 concerns normalized, monotone, supermodular rewards with values in $[0,1]$.
--
--   **Formalization Note** Set functions are real-valued functions on `Finset T`; supermodularity is the paper's marginal form, with `insert j S` for $S\cup\{j\}$. The four properties are separate predicates, so that each statement assumes exactly the ones it uses.
-- source:
--   Ezra–Feldman–Molina–Schlesinger, Sources of Complexity in Multi-Agent Combinatorial Contracts, STOC 2027 submission (manuscript sha256 430be35c86352b23f05ee0e9126d1318096922c9cbe07d419ee38e38bfcba346), §2, pp.8 and 10 (PDF pp.9 and 11): f normalized and monotone (p.8), the class of supermodular rewards (p.10)

import Mathlib

set_option autoImplicit false

namespace CritContracts

/-- The reward classes of §2 (Ezra–Feldman–Molina–Schlesinger, *Sources of Complexity in Multi-Agent
Combinatorial Contracts*, STOC 2027 submission (manuscript sha256 430be35c…), §2, pp.8 and 10, PDF pp.9 and 11).

A set function `f : 2^T → ℝ` is **supermodular** if marginals are (weakly) increasing:
`f(j | S) ≤ f(j | S')` for any two sets `S ⊆ S' ⊆ T` and `j ∈ T \ S'`, where `f(j | S) = f(S ∪ {j}) − f(S)`
(p.10). -/
def IsSupermodular {T : Type} [DecidableEq T] (f : Finset T → ℝ) : Prop :=
  ∀ (S S' : Finset T) (j : T), S ⊆ S' → j ∉ S' → f (insert j S) - f S ≤ f (insert j S') - f S'

/-- `f` is **normalized**: `f(∅) = 0` (p.8). -/
def IsNormalized {T : Type} (f : Finset T → ℝ) : Prop := f ∅ = 0

/-- `f` is **monotone**: `S ⊆ S'` implies `f(S) ≤ f(S')` (p.8, p.10). -/
def IsMonotone {T : Type} (f : Finset T → ℝ) : Prop := ∀ S S' : Finset T, S ⊆ S' → f S ≤ f S'

/-- `f` takes values in `[0, 1]` (`f : 2^T → [0,1]`, p.8). -/
def IsUnitValued {T : Type} (f : Finset T → ℝ) : Prop := ∀ S : Finset T, 0 ≤ f S ∧ f S ≤ 1

end CritContracts


