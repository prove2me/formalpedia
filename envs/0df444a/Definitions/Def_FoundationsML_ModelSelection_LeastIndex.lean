-- Prove2me | Definitions.Def_FoundationsML_ModelSelection_LeastIndex
-- name    : FoundationsML_ModelSelection_LeastIndex
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-19T21:18:18.825979+00:00
-- url     : https://prove2.me/theorems/92135b3e-41d6-48c2-873a-2bf84cae7811
-- title:
--   k(h) — the least hypothesis-set index containing h
-- statement:
--   **`k(h)`, p. 65, PDF p. 82.** For a nested countable family of hypothesis sets
--   $(H_k)_{k\ge1}$, $k(h)$ denotes "the least complex hypothesis set among the $H_k$s that
--   contain $h$": the smallest index $k \ge 1$ with $h \in H_k$. Central to the statement of
--   Theorem 4.2 (the SRM learning guarantee) and Theorem 4.4 (cross-validation vs. SRM).
--
--   **Formalization Note.** `LeastIndex H h` is `Nat.sInf {k | 1 ≤ k ∧ h ∈ H k}`; every
--   consuming theorem carries the standing hypothesis that `h` lies in the union
--   `⋃ k ≥ 1, H k`, under which this set is nonempty and `Nat.sInf` returns the least element,
--   matching the book's `k(h)`.
-- source:
--   Mohri, Rostamizadeh & Talwalkar, Foundations of Machine Learning, 2nd ed., MIT Press 2018, p. 65 (PDF p. 82)

import Mathlib

namespace FoundationsML.ModelSelection

/-- For a countable family of hypothesis sets `(H_k)_{k≥1}`, `LeastIndex H h` is `k(h)`,
"the least complex hypothesis set among the `H_k`s that contain `h`" (Mohri, Rostamizadeh &
Talwalkar, *Foundations of Machine Learning*, 2nd ed., MIT Press 2018, p. 65, PDF p. 82): the
smallest index `k ≥ 1` with `h ∈ H_k`.

**Formalization Note.** `Nat.sInf` of the (possibly empty) set `{k | 1 ≤ k ∧ h ∈ H k}` is used;
every theorem that uses this definition carries the standing hypothesis that `h` lies in the
union `⋃ k ≥ 1, H k`, under which the set is nonempty and `Nat.sInf` returns its least
element, matching the book's `k(h)`. -/
noncomputable def LeastIndex {X Y : Type*} (H : ℕ → Set (X → Y)) (h : X → Y) : ℕ :=
  sInf {k : ℕ | 1 ≤ k ∧ h ∈ H k}

end FoundationsML.ModelSelection


