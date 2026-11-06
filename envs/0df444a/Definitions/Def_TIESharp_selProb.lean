-- Prove2me | Definitions.Def_TIESharp_selProb
-- name    : TIESharp_selProb
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:35:58.070043+00:00
-- url     : https://prove2.me/theorems/19531790-c107-491c-baa3-f2ec727d69db
-- title:
--   Selection probabilities $\theta_i=\Pr(I=i)$ of a maximum-load machine
-- statement:
--   In each outcome $A$ of the assignment law $y$, a rule $I=\mathrm{sel}(A)$ chooses a machine (in the paper, a maximum-load machine by fixed tie-breaking). Its **selection probabilities** are
--   $$\theta_i=\Pr(I=i)=\sum_{A:\ \mathrm{sel}(A)=i}y_A .$$
--   They weight each machine's mean load in the bound on the expected makespan.
--
--   **Formalization Note.** `sel` is any function of the outcome; that it picks a maximum-load machine is a hypothesis of the statements that use $\theta$. Every fixed tie-breaking rule is such a function.
-- source:
--   Li, Sharp Bounds for Truthful-in-Expectation Scheduling, arXiv:2611.05134 (held version, sha256 e611c390…b70e5481), §3.2, p.10

import Mathlib

set_option autoImplicit false

namespace TIESharp

/-- The **selection probability** `θ_i = P(I = i)` of machine `i` (Li, *Sharp Bounds for
Truthful-in-Expectation Scheduling*, arXiv:2611.05134, §3.2, p.10): "In each outcome choose a
maximum-load machine I by fixed tie-breaking, and let θ_i = P(I = i)". The rule `sel` picks the
machine `I = sel(A)` in outcome `A`; under the assignment law `y`, `θ_i` is the total weight of the
outcomes with `sel(A) = i`.

**Formalization Note.** `sel : (Fin m → Fin n) → Fin n` is any deterministic choice of a machine
per outcome; statements that use `selProb` assume separately that `sel A` attains the makespan of
`A`. Every fixed tie-breaking rule is such a `sel`. -/
def selProb {n m : ℕ} (y : (Fin m → Fin n) → ℝ) (sel : (Fin m → Fin n) → Fin n) (i : Fin n) : ℝ :=
  ∑ A ∈ Finset.univ.filter (fun A : Fin m → Fin n => sel A = i), y A

end TIESharp


