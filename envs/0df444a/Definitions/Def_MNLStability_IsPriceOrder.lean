-- Prove2me | Definitions.Def_MNLStability_IsPriceOrder
-- name    : MNLStability_IsPriceOrder
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T13:26:20.349706+00:00
-- url     : https://prove2.me/theorems/8d928a95-414b-4bee-8ed0-419e7b599e4e
-- title:
--   Products of $I$ indexed by non-increasing price; non-increasing levels
-- statement:
--   §4.1 assumes without loss of generality that $I=[m]$ with $r_1\ge\dots\ge r_m$. Here a list `ord` plays this role: it lists every product of $I$ exactly once, and prices are non-increasing along it. Position $k$ of the list (from $0$) is the paper's product $k+1$ of $I$.
--
--   A vector $V$ is **non-increasing along** the list when $V_1\ge V_2\ge\dots\ge V_m$ in this indexing, as for $V^\uparrow$ in Lemma 6 and $V^{\mathrm{step}}$ in §4.3.
-- source:
--   Aouad & Segev, The Stability of MNL-Based Demand under Dynamic Customer Substitution and its Algorithmic Implications, SSRN:3498325 (manuscript of 2019-12-04), §4.1, p.18 ("indexed by non-increasing prices"); Lemma 6, p.19

import Mathlib

namespace MNLStability

variable {n : ℕ}

/-- `ord` lists the products of `I`, each once, by non-increasing price: the indexing
`I = [m]`, `r₁ ≥ ⋯ ≥ r_m` of SSRN:3498325, §4.1, p.18 ("the products in I are indexed by
non-increasing prices"). Position `k` of `ord` (0-based) is the paper's product `k + 1` of `I`. -/
def IsPriceOrder (r : Fin n → ℝ) (I : Finset (Fin n)) (ord : List (Fin n)) : Prop :=
  ord.Nodup ∧ (∀ i, i ∈ ord ↔ i ∈ I) ∧ ord.Pairwise fun i j => r j ≤ r i

/-- The inventory levels of `V` are non-increasing along `ord`: `V_1 ≥ ⋯ ≥ V_m` in the indexing of
§4.1 (Lemma 6, p.19). -/
def NonincAlong (ord : List (Fin n)) (V : Fin n → ℕ) : Prop :=
  ord.Pairwise fun i j => V j ≤ V i

end MNLStability


