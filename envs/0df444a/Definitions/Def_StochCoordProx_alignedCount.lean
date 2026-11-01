-- Prove2me | Definitions.Def_StochCoordProx_alignedCount
-- name    : StochCoordProx_alignedCount
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:32:21.639614+00:00
-- url     : https://prove2.me/theorems/be652991-b89b-4220-8030-6f368f660412
-- title:
--   Number of well-aligned iterations $|\mathbb A_K|$
-- statement:
--   Given events $W_k$ ("$U_k$ is well-aligned"), the set of well-aligned updates in $K$ iterations is
--
--   $$
--   \mathbb A_K=\{k\in[K]: U_k\text{ is well-aligned}\},\qquad [K]=\{0,1,\dots,K\},
--   $$
--
--   and $|\mathbb A_K|(\omega)$ is the number of $k\in\{0,\dots,K\}$ with $\omega\in W_k$.
--
--   **Formalization Note** $[K]$ has $K+1$ elements, as in the proof of Lemma 6, which writes $|\mathbb A_K|=\sum_{i=0}^K T_i$.
-- source:
--   Necoara & Chorobura, Efficiency of stochastic coordinate proximal gradient methods on nonseparable composite optimization, arXiv:2104.13370v3, p.8 (definition of 𝔸_K); proof of Lemma 6, p.26

import Mathlib

namespace StochCoordProx

open Classical in
/-- **The number of well-aligned iterations `|𝔸_K|`** (p.8): given the events
`W k = {U_k is well-aligned}`, the count on outcome `ω` of the indices
`k ∈ [K] = {0, 1, …, K}` with `ω ∈ W k`.

Necoara & Chorobura, arXiv:2104.13370v3, p.8 (`𝔸_K = {k ∈ [K] : U_k is well-aligned}`); the
proof of Lemma 6 (p.26) writes `|𝔸_K| = ∑_{i=0}^K T_i`, so `[K] = {0, …, K}`.

**Formalization Note.** `Finset.range (K + 1) = {0, …, K}` (`K + 1` indices). -/
noncomputable def alignedCount {Ω : Type*} (W : ℕ → Set Ω) (K : ℕ) (ω : Ω) : ℕ :=
  ((Finset.range (K + 1)).filter (fun k => ω ∈ W k)).card

end StochCoordProx


