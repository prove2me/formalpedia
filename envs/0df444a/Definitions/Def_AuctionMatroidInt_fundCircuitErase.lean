-- Prove2me | Definitions.Def_AuctionMatroidInt_fundCircuitErase
-- name    : AuctionMatroidInt_fundCircuitErase
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:25:20.643104+00:00
-- url     : https://prove2.me/theorems/86c42679-fb63-4f5c-95f3-1e827d6dd27f
-- title:
--   The fundamental circuit minus its new element, $C_M(X\mid e)-e$
-- statement:
--   Let $M=(E,\mathcal I)$ be a matroid, $X\in\mathcal I$ and $e\in E\setminus X$ with $X+e\notin\mathcal I$. Then $X+e$ contains a unique circuit $C_M(X\mid e)$, the **fundamental circuit** of $X$ and $e$. By Observation 2.1, for $f\in X+e$ one has $X+e-f\in\mathcal I$ if and only if $f\in C_M(X\mid e)$. Hence
--
--   $$
--   C_M(X\mid e)-e=\{f\in X : X+e-f\in\mathcal I\}.
--   $$
--
--   This module defines the right-hand side for any $X$ and $e$. It is the set over which the implicit price (1) minimizes and the set the algorithm removes an element from.
--
--   **Formalization Note** The set is `X.filter (fun f => I ((insert e X).erase f))`. It equals $C_M(X\mid e)-e$ in the only situation in which the paper uses the fundamental circuit ($M$ a matroid, $X\in\mathcal I$, $e\notin X$, $X+e\notin\mathcal I$), by Observation 2.1; Mathlib's `Matroid.fundCircuit` is not used because it lives on `Set`s of a different matroid type.
-- source:
--   Huang, Kobayashi, Terao, Auction-Based Algorithms for Weighted Matroid Intersection with Near-Linear Query Complexity (manuscript, sha256 2e12cb4a…), §2.1, p.10 and Observation 2.1, p.11 (PDF pp.12–13)

import Mathlib

namespace AuctionMatroidInt

open Classical in
/-- **The fundamental circuit minus its new element, `C_M(X | e) − e`.**
Huang, Kobayashi, Terao (manuscript, sha256 2e12cb4a…), §2.1, p.10: "For an independent set
X ∈ I and an element e ∈ E \ X such that X + e ∉ I, X + e contains a unique circuit, which we
denote C_M(X | e)". Observation 2.1, p.11: for such X and e and f ∈ X + e,
X + e − f ∈ I if and only if f ∈ C_M(X | e).

`fundCircuitErase I X e` is the set `{f ∈ X | X + e − f ∈ I}`.

**Formalization Note.** By Observation 2.1 this set equals `C_M(X | e) − e` whenever `I` is a
matroid, `X ∈ I`, `e ∉ X` and `X + e ∉ I`; that is the only situation in which the paper uses
`C_M(X | e)`, and this characterization is the form in which every proof and Lemma 5.14 use it.
Outside that situation the set has no meaning in the paper and is never read. Here `X + e − f`
is `(insert e X).erase f`. -/
noncomputable def fundCircuitErase {α : Type*} [DecidableEq α] (I : Finset α → Prop)
    (X : Finset α) (e : α) : Finset α :=
  X.filter (fun f => I ((insert e X).erase f))

end AuctionMatroidInt


