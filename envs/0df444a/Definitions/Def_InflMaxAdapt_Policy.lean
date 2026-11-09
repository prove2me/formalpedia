-- Prove2me | Definitions.Def_InflMaxAdapt_Policy
-- name    : InflMaxAdapt_Policy
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T16:32:39.348468+00:00
-- url     : https://prove2.me/theorems/22703828-ed5d-4c55-bf18-fbbde4a1e92d
-- title:
--   Adaptive policy with budget $k$
-- statement:
--   An **adaptive policy** with budget $k$ is a random sequence $(v_1, \dots, v_k)$ of vertices in which, for every $i \in [k]$, the choice of $v_i$ is a function of the cascades $C(v_1), \dots, C(v_{i-1})$ of the earlier seeds and of external randomness independent of the live arcs. Observing the whole cascade of every probed seed is **full-adoption feedback**.
--
--   **Formalization Note** A policy is a family of decision rules indexed by the steps $0, \dots, k-1$ (0-based): the rule of step $i$ maps a point $\omega$ of the randomness space $\Omega$ and the list of the $i$ earlier cascades to a vertex. The law of $\omega$ is supplied separately as a probability measure on $\Omega$. A vertex may be chosen more than once, as the paper does not forbid it.
-- source:
--   de Azevedo–Hennebelle, Adaptivity Gaps for Influence Maximization: Percolation and Depletion, STOC 2027 submission (manuscript sha256 67dfe75c…abe5d5), Section 1.1, printed p.2 (PDF p.3)

import Mathlib

namespace InflMaxAdapt

/-- An adaptive policy with budget `k` (Section 1.1, printed p.2 = PDF p.3, of de Azevedo–Hennebelle, *Adaptivity Gaps for Influence Maximization: Percolation and Depletion*, STOC 2027 submission manuscript (sha256 67dfe75c…abe5d5)):
for every `i ∈ [k]` the vertex `v_i` is a function of the external randomness `ω ∈ Ω` (independent
of the live arcs) and of the cascades `C(v_1), …, C(v_{i−1})` of the earlier seeds.

**Formalization Note** Indices are 0-based: `rule i ω h` is the seed chosen at step `i` when the
external randomness is `ω` and `h j = C(v_j)` for `j < i` (full-adoption feedback). The law of `ω`
is supplied separately (a probability measure on `Ω`). Repeated seeds are allowed, as the paper
does not forbid them. -/
structure Policy (V : Type) (k : ℕ) (Ω : Type) where
  /-- the decision rule of step `i`: external randomness and earlier cascades ↦ the next seed -/
  rule : (i : Fin k) → Ω → (Fin i.val → Finset V) → V

end InflMaxAdapt


