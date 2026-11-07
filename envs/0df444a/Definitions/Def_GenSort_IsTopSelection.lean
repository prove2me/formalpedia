-- Prove2me | Definitions.Def_GenSort_IsTopSelection
-- name    : GenSort_IsTopSelection
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T03:27:10.762656+00:00
-- url     : https://prove2.me/theorems/ba86d1b1-e9c7-492e-9884-ae9042ec03a0
-- title:
--   $Q_v$: the $t$ highest-score left neighbours of each right vertex
-- statement:
--   Given scores on the left vertices, a selection $(Q_v)_{v \in R}$ **selects the $t$ highest-score neighbours** if for every right vertex $v$: $Q_v$ is a set of $\min(t, \deg v)$ neighbours of $v$, and no unselected neighbour of $v$ has a strictly higher score than a selected one. Ties are broken arbitrarily.
--
--   **Formalization Note** Every statement quantifies over all selections with this property.
-- source:
--   Khanna, Putterman, Song, A Near-Optimal Generalized Sorting Algorithm, STOC 2027 submission (preprint of November 3, 2026, sha256 f1b5a9aa…), §3.4 step 4, p.8 (PDF p.10)

import Mathlib

namespace GenSort

/-- **`Q_v`: the `t` highest-score left neighbours of each right vertex**, Khanna–Putterman–Song, *A Near-Optimal Generalized Sorting Algorithm*, STOC 2027 submission (preprint of November 3, 2026, sha256 f1b5a9aa…), §3.4 step 4, p.8
(PDF p.10): "For every right vertex `v ∈ R`, we select its `t` highest score left neighbors,
breaking ties arbitrarily." `Q v` is a selection of `min(t, deg v)` neighbours of `v` such that
no unselected neighbour has a strictly higher score.

**Formalization Note.** Ties are broken arbitrarily, so every theorem quantifies over all
selections satisfying this property. A vertex with fewer than `t` neighbours selects all. -/
def IsTopSelection {L R : Type*} (E : Finset (L × R)) (sc : L → ℕ) (t : ℕ)
    (Q : R → Finset L) : Prop :=
  open Classical in
  ∀ v : R, Q v ⊆ (E.filter fun p => p.2 = v).image Prod.fst ∧
    (Q v).card = min t ((E.filter fun p => p.2 = v).image Prod.fst).card ∧
    ∀ u ∈ Q v, ∀ u' ∈ (E.filter fun p => p.2 = v).image Prod.fst, u' ∉ Q v → sc u' ≤ sc u

end GenSort


