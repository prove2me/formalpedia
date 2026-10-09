-- Prove2me | Definitions.Def_LinearPathTuran_Exact_Setting
-- name    : LinearPathTuran_Exact_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T19:21:34.046587+00:00
-- url     : https://prove2.me/theorems/3e4b2c6d-55df-41e4-90cf-4302434e454e
-- title:
--   pp. 1–3, 9 — linear paths, the Turán number ex_k(n, ℙ_ℓ^(k)), f(n,k,t), g(n,k,t) and the extremal families
-- statement:
--   This file fixes the objects of the main theorem of Füredi, Jiang and Seiver.
--
--   1. **Families.** The vertex set is $[n]$. A *family* is a set $\mathcal F$ of subsets of $[n]$; it is *$k$-uniform* if every member has exactly $k$ elements, i.e. $\mathcal F\subseteq\binom{[n]}{k}$.
--   2. **Linear paths (p. 3).** A *linear path of length $\ell$* is a sequence of distinct sets $F_1,\dots,F_\ell$ with
--   $$|F_i\cap F_{i+1}|=1\ \text{ for each } i,\qquad F_i\cap F_j=\emptyset\ \text{ whenever } |i-j|>1 .$$
--   $\mathcal F$ *contains* $\mathbb P_\ell^{(k)}$ if some $F_1,\dots,F_\ell\in\mathcal F$ form a linear path.
--   3. **Turán number (pp. 1–2).** $\mathbf{ex}_k(n,\mathbb P_\ell^{(k)})$ is the maximum of $|\mathcal F|$ over $k$-uniform families $\mathcal F$ on $[n]$ that do not contain $\mathbb P_\ell^{(k)}$.
--   4. **The counting functions (p. 9).**
--   $$f(n,k,t)=\binom{n-1}{k-1}+\binom{n-2}{k-1}+\dots+\binom{n-t}{k-1},\qquad g(n,k,t)=f(n,k,t)+\binom{n-t-2}{k-2}.$$
--   5. **The extremal families.** For $S\subseteq[n]$, the *star family* is the set of all $k$-subsets of $[n]$ meeting $S$. For $S\subseteq[n]$ and $u,v\in[n]$, the *even family* is the star family of $S$ together with all $k$-subsets of $[n]\setminus S$ containing both $u$ and $v$.
--
--   These objects are shared by every statement of the mission that mentions linear paths or the Turán number.
--
--   **Formalization Note** $[n]$ is `Fin n` and families are `Finset (Finset (Fin n))`. A linear path is an injective map `P : Fin ℓ → Finset (Fin n)` into the family with `#(P i ∩ P j) = 1` when `i + 1 = j` and `P i`, `P j` disjoint when `i + 1 < j`; for $k\ge 2$ injectivity already follows from these intersection conditions. `exLin n k ℓ` is a `Finset.sup` of cardinalities over the finite set of $\mathbb P_\ell$-free subfamilies of $\binom{[n]}{k}$; for $\ell\ge1$ this set contains the empty family, so it is a true attained maximum. For $\ell=0$ every family contains the empty path and `exLin n k 0 = 0` is a default value; no statement of the mission uses $\ell=0$. The subtractions $n-i$, $n-t-2$, $k-1$, $k-2$ are natural-number subtractions; they are exact whenever $n\ge t+2$ and $k\ge 2$.
-- source:
--   Füredi, Jiang and Seiver, Exact solution of the hypergraph Turán problem for k-uniform linear paths, arXiv:1108.1247v1, pp. 1–2 (§1, definition of ex_k), p. 3 (§2, linear path), p. 9 (§5, f(n,k,t) and g(n,k,t))

import Mathlib

namespace LinearPathTuran.Exact

open Finset

variable {n : ℕ}

/-- `𝓕` contains a linear path of length `ℓ` (p. 3): distinct members `P 0, …, P (ℓ-1)` of
`𝓕` such that consecutive members meet in exactly one vertex and non-consecutive members are
disjoint. -/
def ContainsLinearPath (𝓕 : Finset (Finset (Fin n))) (ℓ : ℕ) : Prop :=
  ∃ P : Fin ℓ → Finset (Fin n), Function.Injective P ∧ (∀ i, P i ∈ 𝓕) ∧
    (∀ i j : Fin ℓ, (i : ℕ) + 1 = j → #(P i ∩ P j) = 1) ∧
    (∀ i j : Fin ℓ, (i : ℕ) + 1 < j → Disjoint (P i) (P j))

open Classical in
/-- The Turán number `ex_k(n, ℙ_ℓ^(k))` (pp. 1–2): the largest size of a `k`-uniform family on
`[n] = Fin n` containing no linear path of length `ℓ`. For positive `ℓ`, this is a maximum over
a finite set containing the empty family. -/
noncomputable def exLin (n k ℓ : ℕ) : ℕ :=
  (((univ : Finset (Fin n)).powersetCard k).powerset.filter
    (fun 𝓕 => ¬ ContainsLinearPath 𝓕 ℓ)).sup card

/-- `f(n, k, t) = C(n-1, k-1) + C(n-2, k-1) + … + C(n-t, k-1)` (p. 9). -/
def fNum (n k t : ℕ) : ℕ := ∑ i ∈ Icc 1 t, (n - i).choose (k - 1)

/-- `g(n, k, t) = f(n, k, t) + C(n-t-2, k-2)` (p. 9). -/
def gNum (n k t : ℕ) : ℕ := fNum n k t + (n - t - 2).choose (k - 2)

/-- All `k`-subsets of `[n]` that meet `S`. -/
def starFamily (n k : ℕ) (S : Finset (Fin n)) : Finset (Finset (Fin n)) :=
  ((univ : Finset (Fin n)).powersetCard k).filter (fun A => ¬ Disjoint A S)

/-- All `k`-subsets of `[n]` that meet `S`, together with all `k`-subsets of `[n] \ S` that
contain both `u` and `v`. -/
def evenFamily (n k : ℕ) (S : Finset (Fin n)) (u v : Fin n) : Finset (Finset (Fin n)) :=
  starFamily n k S ∪
    ((univ : Finset (Fin n)).powersetCard k).filter (fun A => Disjoint A S ∧ u ∈ A ∧ v ∈ A)

end LinearPathTuran.Exact


