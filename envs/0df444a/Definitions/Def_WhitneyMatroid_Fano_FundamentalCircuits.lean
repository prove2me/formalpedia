-- Prove2me | Definitions.Def_WhitneyMatroid_Fano_FundamentalCircuits
-- name    : WhitneyMatroid_Fano_FundamentalCircuits
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T04:29:02.654064+00:00
-- url     : https://prove2.me/theorems/b68a730c-b71b-46fc-8fda-2957b0effaa5
-- title:
--   Fundamental and strict fundamental sets of circuits (§9)
-- statement:
--   Let $M$ be a matroid with $\rho(M)$ elements and rank $r(M)$, and let $n(M)=\rho(M)-r(M)$ be its nullity. The circuits $P_1,\dots,P_q$ of $M$ form a **fundamental set of circuits** if $q=n(M)$ and the elements $e_1,\dots,e_n$ of $M$ can be ordered so that
--
--   $$
--   e_{n-q+i}\in P_i, \qquad e_{n-q+j}\notin P_i \quad (j>i).
--   $$
--
--   The set is **strict** if $P_i$ contains $e_{n-q+i}$ but no $e_{n-q+j}$ for $0<j<i$ or $j>i$. Such sets are said to be taken **with respect to** $e_{n-q+1},\dots,e_n$.
--
--   Three predicates are defined: a fundamental set with respect to a given list of distinct elements $f_1,\dots,f_q$ (Whitney's $e_{n-q+1},\dots,e_n$), its strict version, and a fundamental set (with respect to some such list). Fundamental sets are the circuits read off from a base: they index the rows of a circuit matrix that span all its rows (Theorem 29).
--
--   **Formalization Note** The condition $q=n(M)$ is written $q+r(M)=\rho(M)$ in extended natural numbers, so no truncated subtraction occurs. Only the last $q$ elements of Whitney's ordering are named; the order of the remaining elements plays no role in the definition. Indices are $0,\dots,q-1$ instead of $1,\dots,q$.
-- source:
--   Whitney, On the Abstract Properties of Linear Dependence, Amer. J. Math. 57 (1935), p. 517, §9

import Mathlib

namespace WhitneyMatroid.Fano

/-- Whitney §9 (p. 517): `P₁, …, P_q` is a *fundamental set of circuits* of `M` with respect to the
elements `f 0, …, f (q-1)` (Whitney's `e_{n-q+1}, …, e_n`): `q = n(M)` (the nullity: number of
elements minus rank, written `q + r(M) = ρ(M)`), the `f i` are distinct elements, each `P_i` is a
circuit, `P_i` contains `f i` (Whitney's `e_{n-q+i}`) but no `f j` with `j > i`. -/
def IsFundamentalCircuitSetWrt {α : Type*} {q : ℕ} (M : Matroid α) (P : Fin q → Set α)
    (f : Fin q → α) : Prop :=
  (q : ℕ∞) + M.eRank = M.E.encard ∧ Function.Injective f ∧ (∀ i, f i ∈ M.E) ∧
    ∀ i, M.IsCircuit (P i) ∧ f i ∈ P i ∧ ∀ j, i < j → f j ∉ P i

/-- Whitney §9 (p. 517): the set is *strict* (with respect to `f 0, …, f (q-1)`) if moreover
`P_i` contains `f i` but no `f j` with `j ≠ i`. -/
def IsStrictFundamentalCircuitSetWrt {α : Type*} {q : ℕ} (M : Matroid α) (P : Fin q → Set α)
    (f : Fin q → α) : Prop :=
  IsFundamentalCircuitSetWrt M P f ∧ ∀ i j, j ≠ i → f j ∉ P i

/-- Whitney §9 (p. 517): `P₁, …, P_q` is a fundamental set of circuits of `M` if the elements of
`M` can be ordered so that the conditions of `IsFundamentalCircuitSetWrt` hold for the last `q`
elements of the ordering. -/
def IsFundamentalCircuitSet {α : Type*} {q : ℕ} (M : Matroid α) (P : Fin q → Set α) : Prop :=
  ∃ f : Fin q → α, IsFundamentalCircuitSetWrt M P f

end WhitneyMatroid.Fano


