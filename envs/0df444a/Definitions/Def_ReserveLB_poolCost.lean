-- Prove2me | Definitions.Def_ReserveLB_poolCost
-- name    : ReserveLB_poolCost
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:29:28.532076+00:00
-- url     : https://prove2.me/theorems/4150f55a-fee2-439b-b87f-08959d39d244
-- title:
--   Whole-job cost of a two-endpoint pool placement
-- statement:
--   With the data of the global density, the **whole-job cost** is the least, over all choices of one of its two endpoints for every portion, of the maximum endpoint load.
--
--   **Formalization Note** In Lemma 6.1 every original has at most one positive portion, so choosing per portion is choosing per original.
-- source:
--   Mahboub–Rahgoshay, Stochastic Load Balancing with Strict Machine-Reservation Budgets, manuscript of Oct. 30, 2026 (sha256 aefe1158e8000194527b025b3c358dcb571c94e1038c0bfdd295c6119bc9f630), Lemma 6.1, p.11

import Mathlib

namespace ReserveLB

/-- **Whole-job cost of a two-endpoint pool placement.**
Mahboub–Rahgoshay, *Stochastic Load Balancing with Strict Machine-Reservation Budgets*,
manuscript of Oct. 30, 2026 (sha256 aefe1158…), Lemma 6.1, p.11: "additive whole-job cost".

With the data of `poolDensity`, `poolCost R z u1 u2` is the minimum, over all choices `b` of one of
the two endpoints for every portion, of the maximum endpoint load.

**Formalization Note.** Portions are exclusive across pools in Lemma 6.1, so choosing per portion
is choosing per original. The maximum over an empty endpoint set is `0`. -/
noncomputable def poolCost {n : ℕ} {Pl : Type*} [Fintype Pl] [DecidableEq Pl] (R : Pl → ℕ)
    (z : Fin n → Pl → ℝ) (u1 u2 : Fin n → (p : Pl) → Fin (R p)) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty fun b : Fin n → Pl → Bool =>
    if h : (Finset.univ : Finset ((p : Pl) × Fin (R p))).Nonempty then
      Finset.univ.sup' h fun e => ∑ j, ∑ p,
        if e = ⟨p, if b j p then u1 j p else u2 j p⟩ then z j p else 0
    else 0

end ReserveLB


