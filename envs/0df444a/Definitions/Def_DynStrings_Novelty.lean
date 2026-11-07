-- Prove2me | Definitions.Def_DynStrings_Novelty
-- name    : DynStrings_Novelty
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:54:24.761613+00:00
-- url     : https://prove2.me/theorems/b315028b-7af3-4ffa-a29b-d278754e1465
-- title:
--   Exclusive symbols, $G(X\mid\mathcal C)$, scales $R_{k,m}$, local novelty $\Delta_{k,m}$, word and tuple witnesses, and the arity classes $U_k$, $V_k$, $V$
-- statement:
--   The quantities of the relative analysis, for a non-empty string $X$, a finite collection $\mathcal C$ and a choice of the orders shared by all strings.
--
--   A symbol is exclusive to $X$ relative to $\mathcal C$ if it labels a node of the parse tree of $X$ but of no member of $\mathcal C$; $G(X\mid\mathcal C)$ is the number of exclusive symbols plus the total arity of the exclusive tuples. Writing $X_k$ for the level-$k$ word of $X$,
--
--   $$R_{k,m}=2^{\lceil\log(50\,m\,\ell_{k+1})\rceil},\qquad \Delta_{k,m}=1+\frac{e_{R_{k,m}}(X\mid\mathcal C)}{R_{k,m}} .$$
--
--   A word witness is the leftmost occurrence in $X_k$ of a non-empty word of at most $m$ symbols, all active in round $k+1$, that occurs in no non-singleton level-$k$ word $Y_k$ of a member $Y\in\mathcal C$. For odd $k$, a tuple witness is the leftmost occurrence, among the blocks formed from $X_k$ in round $k+1$, of a block whose tuple has at most $m$ children and is exclusive. The active pairs are the pairs $(A,k)$ with $X_k$ non-singleton, $A$ a symbol of $X_k$ active in round $k+1$, and $A$ in no non-singleton $Y_k$.
--
--   Finally $K=\{k:1\le k<\kappa(|X|),\ k\text{ odd}\}$, $U_k$ is the set of exclusive tuples with creation round $k+1$, $V_k=\sum_{A\in U_k}\deg(A)$, and $V=\sum_{k\in K}V_k$.
--
--   These are the objects the proof of the relative bound counts: exclusive symbols are located near witnesses, and the random part of the grammar size is $V$.
--
--   **Formalization Note** Fragments of level words are 0-based index intervals $[i,j)$. "Non-singleton" is read literally as length different from one.
-- source:
--   Duyster, Kociumaka, Komlós, Optimal Dynamic Strings in Compressed Space (manuscript, sha256 cfcb3de9…), §5.1, p.19 (exclusive, G); §5.2, p.21 (R_{k,m}, Δ_{k,m}, witnesses); Lemma 5.4, p.22 (pairs); §5.4, p.23 (K, U_k, V_k, V)

import Mathlib
import Definitions.Def_DynStrings_Parse

namespace DynStrings

/-!
# Exclusive symbols, local novelty, witnesses and arity classes

Duyster, Kociumaka, Komlós, *Optimal Dynamic Strings in Compressed Space* (manuscript,
sha256 cfcb3de9…), §5.1, p.19 (exclusive symbols, `G(X | 𝒞)`), §5.2, p.21 (`R_{k,m}`, `Δ_{k,m}`,
active fragments, word and tuple witnesses), Lemma 5.4, p.22 (active pairs), and §5.4, p.23
(`K`, `U_k`, `V_k`, `V`).

**Formalization Note.**
* All strings are parsed with the same choice of the orders `lt`; `X_k = level lt X k`.
* Fragments of level words are 0-based index intervals `[i, j)`; the word of the fragment is
  `frag X_k i j`.
* "Non-singleton" is `length ≠ 1`, literally.
* `R_{k,m} = 2^{⌈log(50 m ℓ_{k+1})⌉}` uses `Nat.ceil` of `Real.logb 2` of a real `≥ 50`.
* The active pairs of Lemma 5.4 range over every level `k ≥ 0`; their number is counted with
  `Set.Finite` and `Set.ncard` in the statement.
-/

variable {α : Type} [DecidableEq α]

/-- `A` is exclusive to `X` relative to `𝒞` (§5.1, p.19): it labels a node of `T(X)` but no node
of `T(Y)` for any `Y ∈ 𝒞`. -/
def IsExclusive (lt : ℕ → StrSym α → StrSym α → Prop) (X : List α) (𝒞 : Multiset (List α))
    (A : StrSym α) : Prop :=
  A ∈ grammar lt X ∧ ∀ Y ∈ 𝒞, A ∉ grammar lt Y

open Classical in
/-- The set of symbols exclusive to `X` relative to `𝒞`. -/
noncomputable def excl (lt : ℕ → StrSym α → StrSym α → Prop) (X : List α)
    (𝒞 : Multiset (List α)) : Finset (StrSym α) :=
  (grammar lt X).filter (fun A => ∀ Y ∈ 𝒞, A ∉ grammar lt Y)

/-- `G(X | 𝒞)` (§5.1, p.19): the number of exclusive symbols plus the total arity of the exclusive
tuples. -/
noncomputable def Grel (lt : ℕ → StrSym α → StrSym α → Prop) (X : List α)
    (𝒞 : Multiset (List α)) : ℕ :=
  ∑ A ∈ excl lt X 𝒞, (1 + StrSym.deg A)

/-- The text scale `R_{k,m} = 2^{⌈log(50 m ℓ_{k+1})⌉}` (§5.2, p.21). -/
noncomputable def Rscale (k m : ℕ) : ℕ := 2 ^ ⌈Real.logb 2 (50 * (m : ℝ) * ell (k + 1))⌉₊

/-- The local novelty `Δ_{k,m} = 1 + e_{R_{k,m}}(X | 𝒞)/R_{k,m}` (§5.2, p.21). -/
noncomputable def DeltaLoc (X : List α) (𝒞 : Multiset (List α)) (k m : ℕ) : ℝ :=
  1 + (enov (Rscale k m) X 𝒞 : ℝ) / (Rscale k m : ℝ)

/-- A word witness (§5.2, p.21): the fragment `X_k[i, j)` is the leftmost occurrence in `X_k` of a
non-empty word of at most `m` symbols, all active in round `k + 1`, that does not occur in any
non-singleton level-`k` word `Y_k` of a member `Y ∈ 𝒞`. -/
def IsWordWitness (lt : ℕ → StrSym α → StrSym α → Prop) (X : List α) (𝒞 : Multiset (List α))
    (k m i j : ℕ) : Prop :=
  i < j ∧ j ≤ (level lt X k).length ∧ j - i ≤ m ∧
    (∀ A ∈ frag (level lt X k) i j, Active (k + 1) A) ∧
    (∀ Y ∈ 𝒞, (level lt Y k).length ≠ 1 → ¬ frag (level lt X k) i j <:+: level lt Y k) ∧
    ∀ i' < i, frag (level lt X k) i' (i' + (j - i)) ≠ frag (level lt X k) i j

/-- A tuple witness (§5.2, p.21), for odd `k`: the block `X_k[a, b)` formed in round `k + 1` is the
leftmost occurrence, among the blocks of that round, of a block whose tuple has at most `m`
children and is exclusive to `X` relative to `𝒞`. -/
def IsTupleWitness (lt : ℕ → StrSym α → StrSym α → Prop) (X : List α) (𝒞 : Multiset (List α))
    (k m a b : ℕ) : Prop :=
  Odd k ∧ (a, b) ∈ blockIntervals lt (k + 1) (level lt X k) ∧ 2 ≤ b - a ∧ b - a ≤ m ∧
    IsExclusive lt X 𝒞 (StrSym.tuple (frag (level lt X k) a b)) ∧
    ∀ p ∈ blockIntervals lt (k + 1) (level lt X k), p.1 < a →
      frag (level lt X k) p.1 p.2 ≠ frag (level lt X k) a b

/-- The pairs `(A, k)`, `k ≥ 0`, of Lemma 5.4 (p.22): `X_k` is non-singleton, `A` is a symbol of
`X_k` active in round `k + 1`, and `A` occurs in no non-singleton level-`k` word `Y_k`, `Y ∈ 𝒞`. -/
def activePairs (lt : ℕ → StrSym α → StrSym α → Prop) (X : List α) (𝒞 : Multiset (List α)) :
    Set (StrSym α × ℕ) :=
  {q | (level lt X q.2).length ≠ 1 ∧ q.1 ∈ level lt X q.2 ∧ Active (q.2 + 1) q.1 ∧
    ∀ Y ∈ 𝒞, (level lt Y q.2).length ≠ 1 → q.1 ∉ level lt Y q.2}

open Classical in
/-- `K = {k : 1 ≤ k < κ(n), k odd}` (§5.4, p.23). -/
noncomputable def Kset (n : ℕ) : Finset ℕ := (Finset.range (kappa n)).filter Odd

open Classical in
/-- `U_k`: the exclusive tuples whose creation round is `k + 1` (§5.4, p.23). -/
noncomputable def Uset (lt : ℕ → StrSym α → StrSym α → Prop) (X : List α)
    (𝒞 : Multiset (List α)) (k : ℕ) : Finset (StrSym α) :=
  (excl lt X 𝒞).filter (fun A => StrSym.IsTuple A ∧ StrSym.cr A = k + 1)

/-- `V_k = ∑_{A ∈ U_k} deg(A)` (§5.4, p.23). -/
noncomputable def Vlev (lt : ℕ → StrSym α → StrSym α → Prop) (X : List α)
    (𝒞 : Multiset (List α)) (k : ℕ) : ℕ :=
  ∑ A ∈ Uset lt X 𝒞 k, StrSym.deg A

/-- `V = ∑_{k ∈ K} V_k` (§5.4, p.23), with `K` computed from `n = |X|`. -/
noncomputable def Vtot (lt : ℕ → StrSym α → StrSym α → Prop) (X : List α)
    (𝒞 : Multiset (List α)) : ℕ :=
  ∑ k ∈ Kset X.length, Vlev lt X 𝒞 k

end DynStrings


